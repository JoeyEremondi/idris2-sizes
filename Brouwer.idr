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
