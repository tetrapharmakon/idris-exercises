module Shenanigans

-- "Iso" = an iso between types
record Iso (a : Type) (b : Type) where
  constructor MkIso
  f     : a -> b
  -- a function from a type 'a' to a type 'b'
  g     : b -> a
  -- a function from a type 'b' to a type 'a'
  comp  : (x : a) -> (g (f x) = x)
  comp' : (y : b) -> (f (g y) = y)
  -- ^ proofs that u.g = 1 && v.f = 1

-- the identity function
-- equivalently: id a x = x
id : (a : Type) -> (a -> a)
id a x = x-- (\x => x)

-- proof that the identity is idempotent
idIdem : (a : Type) ->
         (x : a) ->
         (id a (id a x) = id a x)
idIdem a x = Refl

-- Iso is reflexive
isoIsReflexive : (a : Type) -> Iso a a
isoIsReflexive a = MkIso (id a) (id a) (idIdem a) (idIdem a)

-- Iso is symmetric
isoIsSymmetric : (a : Type) ->
                 (b : Type) ->
                 Iso a b ->
                 Iso b a
isoIsSymmetric a b iso = MkIso (g iso) (f iso) (comp' iso) (comp iso)

-- Iso is transitive
isoIsTransitive : (a : Type) ->
                  (b : Type) ->
                  (c : Type) ->
                  Iso a b ->
                  Iso b c ->
                  Iso a c
isoIsTransitive a b c iso iso' =
  MkIso ((f iso') . (f iso))
        ((g iso) . (g iso'))
        ?hole_1
        ?hole_2

-- shall use a tactic for this ^
{-
  ((f iso') . (f iso)) . ((g iso) . (g iso'))
  ------------------------------------------- [assoc]
  f iso' . id . g iso'
  --------------------                        [f iso' . comp . g iso']
  f iso' . g iso'
  ---------------                             [comp]
  id
  --                                          [qed]
-}