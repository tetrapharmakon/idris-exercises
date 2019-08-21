module Structures

isAssoc : (f : a -> a -> a) -> Type
isAssoc f x y z = f (f x y) z = f x (f y z)

record Semigroup (g : Type) where
  constructor MkSemigroup
  (<+>) : g -> g -> g
  assoc : (l : g) -> (c : g) -> (r : g) -> isAssoc <+> l c r


record Monoid (m : Type) where
  constructor MkMonoid
  isSemigroup : Semigroup m
  z : m
  lId : z <+> x = x
  rId : x <+> z = x