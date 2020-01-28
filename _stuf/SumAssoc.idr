module SumAssoc

import Pruviloj
-- import Pruviloj.Core
import Pruviloj.Induction

plusAssoc : (l, c, r : Nat) -> (l + (c + r) = (l + c) + r)
plusAssoc Z c r = Refl
plusAssoc (S k) c r = rewrite plusAssoc k c r in Refl

plusAssoc' : (l, c, r : Nat) -> (l + (c + r) = (l + c) + r)
plusAssoc' Z c r = Refl
plusAssoc' (S k) c r = ?hole_2

plusAssoc'' : (l, c, r : Nat) -> (l + (c + r) = (l + c) + r)
plusAssoc'' = ?hole_3

---------- Proofs ----------

SumAssoc.hole_2 = proof
  intros
  rewrite plusAssoc' k c r
  trivial
