module Structures

-- isAssoc : (f : a -> a -> a) -> Type
-- isAssoc f x y z = f (f x y) z = f x (f y z)

record MySemigroup (g : Type) where
  constructor MkMySemigroup
  (<+>) : g -> g -> g
  assoc : (l : g) -> (c : g) -> (r : g) -> (l <+> c) <+> r = l <+> (c <+> r)


-- This typechecks but it's not the right definition
record MyMonoid (m : Type) where
  constructor MkMyMonoid
  (<+>) : m -> m -> m
  isSemigroup : MySemigroup m
  z : m
  lId : (x : m) -> (z <+> x) = x
  rId : (x : m) -> (x <+> z) = x

-- record MyGroup (g : Type) where
--  constructor MkMyGroup