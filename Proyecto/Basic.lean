import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty ∧ BddAbove S → IsLUB S (sSup S)

variable (X : Type) [RealField X]


instance : Archimedean X where
  arch := by
  sorry
