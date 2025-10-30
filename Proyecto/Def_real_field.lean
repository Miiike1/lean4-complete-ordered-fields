import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty → BddAbove S → IsLUB S (sSup S)
variable (X : Type) [RealField X]

#print RealField

open RealField

--print para ver teoremas, axiomas y props dados por la clase
--escribo teoremas útliles para el futuro
theorem supA_lt_x_in_upbdA {A : Set X} (a : X) (hA : A.Nonempty)
(hB : BddAbove A):a ∈ upperBounds A → sSup A ≤ a  := by
  intro ha
  have sup_islub:= sSup_axiom A hA hB
  rw[IsLUB,IsLeast, lowerBounds] at sup_islub
  obtain ⟨hsup1,hsup2⟩:=sup_islub
  simp at hsup2
  have hsup3:= hsup2
  exact hsup3 ha




theorem supA_lt_a_in_A {A : Set X} (hA : A.Nonempty)
 (hB : BddAbove A) (a : X) :a ∈ A → a ≤ sSup A := by
  intro ha
  obtain ⟨sup_up,sup_low⟩:= sSup_axiom A hA hB
  exact sup_up ha

theorem x_lt_supA_a_lt_sup {A : Set X} (hA : A.Nonempty)
 (hB : BddAbove A) (b : X): b ≤ sSup A → ∃ a ∈ A, b ≤ a := by

  intro hx
  by_contra hc
  push_neg at hc
  have x_is_upper_bound: b ∈ upperBounds A
  · have hc' : ∀ x₁ ∈ A, x₁ ≤ b
    · intro x₁ hx₁
      exact le_of_lt (hc x₁ hx₁)
    exact hc'
  sorry

--he tenido problemas a la hora de cerrar este teorema, no me deja aplicar el teorema
-- supA_lt_a_in_A
--al poner tanto "have sup_lt_x:= supA_lt_a_in_A x hA hB x_in:upper_bound
--como distintas variaciones (probando a introducir A, quitar x etc) me da error.
--no sé cómo solucionarlo (estoy creando estos teoremas porque creo que vendrán bien)

instance : Archimedean X where
  arch := by
    intro x y hy1
    by_contra hc
    have forall_n_prod_lt_x:  ∀(m : ℕ), m • y ≤ x := by
      intro m
      rw[not_exists] at hc
      specialize hc m
      linarith
    by_cases neg: x≤0
    · specialize forall_n_prod_lt_x 1
      rw[one_smul] at forall_n_prod_lt_x
      linarith
    · let A := { (z : X) | ∃ m : ℕ, z = m • y }
      have Anonempty: A.Nonempty := by
          use y; use 1
          rw[one_smul]
      have Abddabv: BddAbove A:= by
        use x
        intro z hz
        have z_in_A: ∃(i:ℕ),  z = i • y:= by
          exact hz
        obtain ⟨i,hz⟩:=hz
        rw[hz]
        specialize forall_n_prod_lt_x i
        exact forall_n_prod_lt_x
      let sup := sSup A
      have sup_islub:= sSup_axiom A Anonempty Abddabv
      have sup_eq_sup: sup= sSup A:= by
        rfl
      rw[<-sup_eq_sup] at sup_islub
      have sup_sub_y_lt_x: sup - y < sup
      · rw[sub_lt_self_iff]; exact hy1
      have alph_in_A_gt_sup_sub_y: ∃α ∈ A, sup - y < α
      · by_contra hc
        have sup_sub_y_upbd: sup - y ∈ upperBounds A
        · intro x hx
          push_neg at hc
          specialize hc x
          exact hc hx
        have sup_lt_sup_sub_y: sup < sup - y
        · rw[IsLUB,IsLeast, lowerBounds] at sup_islub
          obtain ⟨hsup1,hsup2⟩:=sup_islub
          simp at hsup2
          have hsup3:= hsup2 sup_sub_y_upbd
          linarith
        linarith
      obtain ⟨α,hα1,hα2⟩:=alph_in_A_gt_sup_sub_y
      have alpha_eq_n0_y : ∃(n₀ : ℕ), α = n₀ • y
      · exact hα1
      obtain ⟨n₀,hn₀⟩:=alpha_eq_n0_y
      have sup_lt: sup < (n₀ + 1) • y
      · rw[hn₀] at hα2
        rw[sub_lt_iff_lt_add] at hα2
        rw[succ_nsmul]
        exact hα2
      have n0_add_1_in_A: (n₀ + 1) • y ∈ A:= by
        use (n₀ +1)
      have sup_gt_n0_add_one_y:

































    --ya tenemos la contradicción, por transitividad




#print RealField
