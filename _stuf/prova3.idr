module Main

interface Functore (f : Type -> Type) where
  fmap : (a -> b) -> f a -> f b

functorial : {f : b -> c} -> {g : a -> b} -> (phi : Type -> Type) -> fmap (f . g) = (fmap f . fmap g)
functorial phi = ?belive_me

Functore List where
  fmap f [] = []
  fmap f (x :: xs) = f x :: fmap f xs
