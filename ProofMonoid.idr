module ProofMonoid

%runElab

import Interfaces.Verified

data Option a = Some a | None

-- Associativity
-- (a <+> b) <+> c = a <+> (b <+> c)

implementation Semigroup a => Semigroup (Option a) where
  (Some a) <+> (Some b) = Some (a <+> b)
  None <+> a = a
  a <+> b = a

-- Identity laws
-- neutral <+> a = a ; a <+> neutral = a

implementation Semigroup a => Monoid (Option a) where
  neutral = None

-- Verify

implementation VerifiedSemigroup a => VerifiedSemigroup (Option a) where
  semigroupOpIsAssociative (Some x) (Some y) (Some z) = ?sssAssoc
  semigroupOpIsAssociative (Some _) (Some _) None = Refl
  semigroupOpIsAssociative (Some _) None _ = Refl
  semigroupOpIsAssociative None _ _ = Refl

implementation VerifiedSemigroup a => VerifiedMonoid (Option a) where
  monoidNeutralIsNeutralL (Some _) = Refl
  monoidNeutralIsNeutralL None = Refl
  monoidNeutralIsNeutralR (Some _) = Refl
  monoidNeutralIsNeutralR None = Refl

---- Proofs ----

sssAssoc = proof
  intros
  rewrite (semigroupOpIsAssociative x y z)
  trivial

