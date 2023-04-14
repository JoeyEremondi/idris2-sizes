module Brouwer

import Control.Relation
import Control.Order
import Syntax.PreorderReasoning.Generic

||| A Brouwer tree is either zero, successors of another tree,
||| or the limit of some function producing Brouwer trees
public export
data BrouTree : Type where
  BZ : BrouTree
  BS : BrouTree -> BrouTree
  BLim : (Maybe x -> BrouTree) -> BrouTree

||| Less-than relation for Brouwer Trees
||| Designed specifically to be transitive, rather than having transitivity as a constructor
||| Zero is less than everything and BS is monotone.
||| For limits, we have that BLim x f is as large as every (f a) for (a : x),
||| but that it is the least such element.
||| These are sometimes calls "cocone" and "limiting" respectively
public export
data BLT : BrouTree -> BrouTree -> Type where
  BZMin : BZ `BLT` o
  BSucMono :  o1 `BLT` o2 -> (BS o1) `BLT` (BS o2)
  BLimUB : {0 f : Maybe x -> BrouTree} -> (k : Maybe x) -> o `BLT` (f k) -> o `BLT` (BLim f)
  BLimLeast : ((k : Maybe x) -> (f k) `BLT` o) -> (BLim f) `BLT` o



export
underLim :  {o : BrouTree} -> {f : _} -> ((k : Maybe x) -> BLT o (f k)) -> BLT o (BLim f)
underLim lt = BLimUB _ {f = f} (lt Nothing)

export
bExtLim : forall x , f , g. ((k : Maybe x) -> BLT (f k) (g k) ) -> BLT (BLim f) (BLim g)
bExtLim flt = BLimLeast $ \ k => BLimUB k (flt k)


-- The less-than relation is a pre-order

export
Reflexive BrouTree BLT where
  reflexive {x = BZ} = BZMin
  reflexive {x = (BS x)} = BSucMono reflexive
  reflexive {x = (BLim f)} = BLimLeast $ \ k => BLimUB k reflexive

export
Transitive BrouTree BLT where
  transitive BZMin p23 = BZMin
  transitive (BSucMono p12) (BSucMono p23) = BSucMono (transitive p12 p23)
  transitive p12 (BLimUB _ p23) = BLimUB _ (transitive p12 p23)
  transitive (BLimUB k p12) (BLimLeast p23) = transitive p12 (p23 k)
  transitive (BLimLeast p12) p23 = BLimLeast $ \ k => transitive (p12 k) p23

export
Preorder BrouTree BLT where

||| The pre-max operation on ordinals
||| It's not a true least-upper-bound
||| But when we define Sizes, we exclude the ill-behaved ordinals

||| Helper datatype for pattern matching
data MaxView : BrouTree -> BrouTree -> Type where
  MaxZL : MaxView BZ o
  MaxZR : MaxView o BZ
  MaxSucSuc : MaxView (BS o1) (BS o2)
  MaxLimL : {f : _} -> MaxView (BLim f) o
  MaxLimR : {f : _} ->
    (0 notLim : {x : Type} -> {f2 : Maybe x -> BrouTree} -> Not (o === BLim f2))
    -> MaxView o (BLim f)

||| There's a max view for any two ordinals
public export
maxView : (o1 : BrouTree) -> (o2 : BrouTree) -> MaxView o1 o2
maxView BZ o2 = MaxZL
maxView (BLim f) o2 = MaxLimL
maxView (BS x) BZ = MaxZR
maxView (BS x) (BLim f) = MaxLimR helper
  where
    helper : BS x === BLim f2 -> Void
    helper Refl impossible
maxView (BS x) (BS y) = MaxSucSuc

||| The pre-max operation
||| The key detail is that the max of two successors is the successor of the maxes
||| which will let us implement that this is a least upper-bound for sizes
public export
bmaxHelper : (o1 : BrouTree) -> (o2 : BrouTree) -> MaxView o1 o2 -> BrouTree
bmaxHelper .(BZ) o2 MaxZL = o2
bmaxHelper o1 .(BZ) MaxZR = o1
bmaxHelper .(BLim f) o2 (MaxLimL) = BLim $ \ k => bmaxHelper _ _ (maxView (f k) o2)
bmaxHelper o1 .(BLim f) (MaxLimR notLim) = BLim $ \ k => bmaxHelper _ _ (maxView o1 (f k))
bmaxHelper (BS o1) (BS o2) MaxSucSuc = BS (bmaxHelper _ _ (maxView o1 o2))

public export
bmax : BrouTree -> BrouTree -> BrouTree
bmax o1 o2 = bmaxHelper o1 o2 (maxView o1 o2)

export
bmaxLTL : {o1 : _} -> {o2 : _} -> o1 `BLT` (bmax o1 o2)
bmaxLTL {o1} {o2}  with (maxView o1 o2)
  bmaxLTL {o1 = BZ} {o2 = o2} | MaxZL = BZMin
  bmaxLTL {o1 = o1} {o2 = BZ} | MaxZR = reflexive
  bmaxLTL {o1 = (BS o1)} {o2 = (BS o2)} | MaxSucSuc = BSucMono (bmaxLTL {o1 = o1} {o2 = o2})
  bmaxLTL {o1 = (BLim f)} {o2 = o2} | MaxLimL = bExtLim $ \ k => bmaxLTL {o1 = f k} {o2 = o2}
  bmaxLTL {o1 = o1} {o2 = (BLim f)} | (MaxLimR notLim) = underLim (\ k => bmaxLTL {o1 = o1} {o2 = f k})

export
bmaxLTR : {o1 : _} -> {o2 : _} -> o2 `BLT` (bmax o1 o2)
bmaxLTR {o1} {o2}  with (maxView o1 o2)
  bmaxLTR {o1 = BZ} {o2 = o2} | MaxZL = reflexive
  bmaxLTR {o1 = o1} {o2 = BZ} | MaxZR = BZMin
  bmaxLTR {o1 = (BS o1)} {o2 = (BS o2)} | MaxSucSuc = BSucMono (bmaxLTR {o1 = o1} {o2 = o2})
  bmaxLTR {o1 = o1} {o2 = (BLim f)} | (MaxLimR notLim) = bExtLim $ \ k => bmaxLTR {o1 = o1} {o2 = f k}
  bmaxLTR {o1 = (BLim f)} {o2 = o2 } | MaxLimL = underLim (\ k => bmaxLTR {o1 = f k} {o2 = o2})

bmaxZR : {o : BrouTree} -> bmax o BZ `BLT` o
bmaxZR {o = BZ} = BZMin
bmaxZR {o = (BS x)} = reflexive
bmaxZR {o = (BLim f)} = bExtLim $ \ k => bmaxZR {o = f k}

bmaxLimR : (f : Maybe x -> BrouTree) -> (o : BrouTree) -> (o `bmax` BLim f) `BLT` (BLim $ \ k => o `bmax` f k)
bmaxLimR f BZ = reflexive
bmaxLimR f (BS y) = reflexive
bmaxLimR f (BLim g) = BLimLeast $ \ k =>
  CalcWith {leq = BLT} $
    |~ _
    <~ _ ... bmaxLimR f {o = g k}
    <~ _ ... (bExtLim $ \ k2 => BLimUB k reflexive)

export
bmaxMonoR : {o : BrouTree} -> {o1 : BrouTree} -> {o2 : BrouTree} -> o1 `BLT` o2 -> (o `bmax` o1) `BLT` (o `bmax` o2)
bmaxMonoR' : {o : BrouTree} -> {o1 : BrouTree} -> {o2 : BrouTree} -> (BS o1) `BLT` o2 -> (BS (o `bmax` o1)) `BLT` (BS o `bmax` o2)

bmaxMonoR lt with (maxView o o1) proof eq1
  _ | mv1 with (maxView o o2) proof eq2
    bmaxMonoR lt | MaxZL | MaxZL = lt
    bmaxMonoR lt | MaxZR | mv2 = transitive (bmaxLTL {o2 = o2}) (rewrite eq2 in reflexive)
    bmaxMonoR lt | MaxLimL {f = f} | MaxLimL = bExtLim $ \ k => bmaxMonoR lt {o = f k}
    bmaxMonoR lt | MaxSucSuc | MaxZR impossible
    bmaxMonoR {o1 = BS o1} {o2 = BS o2} (BSucMono lt) | MaxSucSuc | MaxSucSuc
      = BSucMono (bmaxMonoR lt {o = o} {o1 = o1} {o2 = o2})
    bmaxMonoR (BLimUB k lt) | MaxSucSuc {o1 = oo} | (MaxLimR notLim) =
      transitive (bmaxMonoR' {o = oo}  lt) (BLimUB k reflexive)
    bmaxMonoR (BLimUB k lt) | (MaxLimR notLim) | MaxZL impossible
    bmaxMonoR (BLimUB k lt) | (MaxLimR notLim) | MaxLimL impossible
    bmaxMonoR (BLimUB k lt) | (MaxLimR notLim) | (MaxLimR f) = ?blr_11
    bmaxMonoR (BLimLeast {f = f} lt) | (MaxLimR notLim) | mv2 = ?blr_8
bmaxMonoR' lt = ?blrr

export
bmaxCommut : {o1 : BrouTree} -> {o2 : BrouTree} -> (o1 `bmax` o2) `BLT` (o2 `bmax` o1)
bmaxCommut with (maxView o1 o2)
  _ | MaxZL = bmaxLTL {o2 = BZ}
  _ | MaxZR = reflexive
  bmaxCommut {o1 = BS o1} {o2 = BS o2} | MaxSucSuc = BSucMono (bmaxCommut {o1 = o1} {o2 = o2})
  _ | (MaxLimR notLim {f = f}) = bExtLim  $ \ k => bmaxCommut {o1 = o1} {o2 = f k}
  _ | MaxLimL {f = f} with (maxView o2 o1)
    _ | MaxZL = bExtLim $ \k => bmaxZR
    _ | (MaxLimR notLim) = reflexive
    _ | MaxLimL {f = g} = CalcWith {leq = BLT} $
        |~ _
        <~  (BLim $ \ k1 => BLim $ \ k2 =>  f k1 `bmax` g k2) ... (bExtLim $ \ k => bmaxLimR g (f k) )
        <~  (BLim $ \ k1 => BLim $ \ k2 => g k2 `bmax` f k1) ... (bExtLim $ \ k1 => bExtLim $ \ k2 => bmaxCommut)
        <~  (BLim $ \ k2 => BLim $ \ k1 => g k2 `bmax` f k1) ... ?p1
        <~  (BLim $ \ k2 => g k2 `bmax` BLim f) ... (bExtLim $ \ k2 => BLimLeast $ \ k1 => ?p2 )
        -- <~  _ ... ?p2
        -- <~  _ ... (bExtLim $ \ k2 => BLimLeast $ \ k1 => ?b3)


-- nmax : BrouTree -> Maybe Nat -> BrouTree
-- nmax o Nothing = BZ
-- nmax o (Just Z) = BZ
-- nmax o (Just (S n)) = bmax (nmax o (Just n)) o

-- export
-- bmaxInf : BrouTree -> BrouTree
-- bmaxInf o = BLim (\ n => nmax o n )

-- bmaxInfSelf : {o : BrouTree} -> BLT o (bmaxInf o)
-- bmaxInfSelf = BLimUB (Just 1) reflexive

-- export
-- bmaxInfIdem : {o : BrouTree} -> ((bmaxInf o) `bmax` (bmaxInf o)) `BLT` (bmaxInf o)
-- bmaxInfIdem = BLimLeast $ \ k => CalcWith {leq = BLT} $
--   |~ _
--   <~ _ ... ?y
--   <~ ?xx ... ?yy
