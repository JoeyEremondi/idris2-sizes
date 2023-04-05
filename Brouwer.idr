module Brouwer

import Control.Relation
import Control.Order

||| A Brouwer tree is either zero, successors of another tree,
||| or the limit of some function producing Brouwer trees
data Ord : Type where
  OZ : Ord
  OS : Ord -> Ord
  OLim : (x -> Ord) -> Ord

||| Less-than relation for Brouwer Trees
||| Designed specifically to be transitive, rather than having transitivity as a constructor
||| Zero is less than everything and OS is monotone.
||| For limits, we have that OLim x f is as large as every (f a) for (a : x),
||| but that it is the least such element.
||| These are sometimes calls "cocone" and "limiting" respectively
data OLT : Ord -> Ord -> Type where
  OZMin : OLT OZ o
  OSucMono : OLT o1 o2 -> OLT (OS o1) (OS o2)
  OLimUB : {0 f : x -> Ord} -> {k : x} -> OLT o (f k) -> OLT o (OLim f)
  OLimLeast : ((k : x) -> OLT (f k) o) -> OLT (OLim f) o


-- The less-than relation is a pre-order



Reflexive Ord OLT where
  reflexive {x = OZ} = OZMin
  reflexive {x = (OS x)} = OSucMono reflexive
  reflexive {x = (OLim f)} = OLimLeast $ \ k => OLimUB (reflexive {x = f k})

Transitive Ord OLT where
  transitive OZMin p23 = OZMin
  transitive (OSucMono p12) (OSucMono p23) = OSucMono (transitive p12 p23)
  transitive p12 (OLimUB p23) = OLimUB (transitive p12 p23)
  transitive (OLimUB {k = k} p12) (OLimLeast p23) = transitive p12 (p23 k)
  transitive (OLimLeast p12) p23 = OLimLeast $ \ k => transitive (p12 k) p23

Preorder Ord OLT where

||| The pre-max operation on ordinals
||| It's not a true least-upper-bound
||| But when we define Sizes, we exclude the ill-behaved ordinals

||| Helper datatype for pattern matching
data MaxView : Ord -> Ord -> Type where
  MaxZL : MaxView OZ o
  MaxZR : MaxView o OZ
  MaxSucSuc : MaxView (OS o1) (OS o2)
  MaxLimL : MaxView (OLim f) o
  MaxLimR :
    (0 notLim : {x : Type} -> {f2 : x -> Ord} -> Not (o === OLim f2))
    -> MaxView o (OLim f)

||| There's a max view for any two ordinals
maxView : (o1 : Ord) -> (o2 : Ord) -> MaxView o1 o2
maxView OZ o2 = MaxZL
maxView (OLim f) o2 = MaxLimL
maxView (OS x) OZ = MaxZR
maxView (OS x) (OLim f) = MaxLimR helper
  where
    helper : OS x === OLim f2 -> Void
    helper Refl impossible
maxView (OS x) (OS y) = MaxSucSuc

||| The pre-max operation
||| The key detail is that the max of two successors is the successor of the maxes
||| which will let us implement that this is a least upper-bound for sizes
omaxHelper : (o1 : Ord) -> (o2 : Ord) -> MaxView o1 o2 -> Ord
omaxHelper OZ o2 MaxZL = o2
omaxHelper o1 OZ MaxZR = o1
omaxHelper (OLim f) o2 (MaxLimL) = OLim $ \ k => omaxHelper _ _ (maxView (f k) o2)
omaxHelper o1 (OLim f) (MaxLimR notLim) = OLim $ \ k => omaxHelper _ _ (maxView o1 (f k))
omaxHelper (OS o1) (OS o2) MaxSucSuc = OS (omaxHelper _ _ (maxView o1 o2))

omax : Ord -> Ord -> Ord
omax o1 o2 = omaxHelper o1 o2 (maxView o1 o2)

omaxLTL : (mv : MaxView o1 o2) -> OLT o1 (omaxHelper o1 o2 mv)
omaxLTL MaxZL = OZMin
-- While processing right hand side of omaxLTL. Can't solve constraint between: omaxHelper o1 OZ MaxZR and o1.
omaxLTL MaxZR = reflexive
omaxLTL MaxSucSuc = ?h_2
omaxLTL MaxLimL = ?h_3
omaxLTL (MaxLimR notLim) = ?h_4
