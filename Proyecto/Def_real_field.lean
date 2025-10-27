import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty ∧ BddAbove S → IsLUB S (sSup S)
variable (X : Type) [RealField X]

#print RealField

--print para ver teoremas, axiomas y props dados por la clase

instance : Archimedean X where
  arch := by
    intro x y hy1
    by_contra hc
    have forall_n_prod_lt_y:  ∀(m : ℕ), m • y ≤ x := by
      intro m
      rw[not_exists] at hc
      specialize hc m
      linarith

    by_cases neg: x≤0

    · specialize forall_n_prod_lt_y 1
      ring_nf at forall_n_prod_lt_y
      linarith

    by_cases pos:  x>0
    · let A := { y | ∃ m : ℕ, y = m • x }
      let sup := sSup A










    --ya tenemos la contradicción, por transitividad
    rw[<- MulOneClass.one_mul y] at forall_n_prod_lt_y





#print RealField
