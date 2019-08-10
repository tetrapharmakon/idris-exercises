module Shenanigans

-- "Isomorphism" = an iso between types
record Isomorphism (a : Type) (b : Type) where
  constructor MkIsomorphism
  u     : a -> b -- a function from a type 'a' to a type 'b'
  v     : b -> a -- a function from a type 'b' to a type 'a'
  comp  : (x : a) -> (v (u x) = x)
  comp' : (y : b) -> (u (v y) = y) -- proofs that u.v = 1 && v.u = 1

-- the identity function
-- equivalently: id a x = x
id : (a : Type) -> (a -> a)
id a = (\x => x)

-- proof that the identity is idempotent
idIdem : (a : Type) ->
         (x : a) ->
         (id a (id a x) = id a x)
idIdem a x = Refl

-- Isomorphism is reflexive
isoIsReflexive : (a : Type) -> Isomorphism a a
isoIsReflexive a = MkIsomorphism (id a) (id a) (idIdem a) (idIdem a)

-- Isomorphism is symmetric
isoIsSymmetric : (a : Type) ->
                 (b : Type) ->
                 Isomorphism a b ->
                 Isomorphism b a
isoIsSymmetric a iso = ?hole_sym

-- Isomorphism is transitive
isoIsTransitive : (a : Type) ->
                  (b : Type) ->
                  (c : Type) ->
                  Isomorphism a b ->
                  Isomorphism b c ->
                  Isomorphism a c
isoIsTransitive a b c iso iso' = ?hole_trn