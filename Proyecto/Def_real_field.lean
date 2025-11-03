import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty → BddAbove S → IsLUB S (sSup S)
variable {X : Type} [RealField X]
variable {Y : Type} [RealField Y]
#print RealField

open RealField

--print para ver teoremas, axiomas y props dados por la clase
--escribo teoremas útliles para el futuro
theorem supA_lt_x_in_upbdA {A : Set X} (a : X) (hA : A.Nonempty)
 (hB : BddAbove A) : a ∈ upperBounds A → sSup A ≤ a  := by
  intro ha
  exact (sSup_axiom A hA hB).2 ha

theorem gt_sup_then_upbdd {A : Set X} (x : X) (hA : A.Nonempty)
 (hB : BddAbove A) : sSup A < x → x ∈ upperBounds A:= by
  have supp:= (sSup_axiom A hA hB).1
  rw[upperBounds] at supp
  simp at supp
  intro hx
  apply le_of_lt at hx
  intro a ha
  have sup2:= supp ha
  exact le_trans (supp ha) hx

theorem supA_lt_a_in_A {A : Set X} (hA : A.Nonempty)
 (hB : BddAbove A) (a : X) :a ∈ A → a ≤ sSup A := by
  intro ha
  exact (sSup_axiom A hA hB).1 ha

theorem x_lt_supA_a_lt_sup {A : Set X} (hA : A.Nonempty)
 (hB : BddAbove A) (b : X) : b < sSup A → ∃ a ∈ A, b < a := by
  intro hx
  by_contra hc
  push_neg at hc
  have x_is_upper_bound: b ∈ upperBounds A
  · have hc' : ∀ x₁ ∈ A, x₁ ≤ b
    · intro x₁ hx₁
      specialize hc x₁ hx₁
      exact hc
    exact hc'
  have sup_lt_b := supA_lt_x_in_upbdA b hA hB x_is_upper_bound
  linarith




instance : Archimedean X where
  arch := by
    intro x y hy1
    by_contra hc
    have forall_n_prod_lt_x:  ∀(m : ℕ), m • y ≤ x := by
      intro m
      push_neg at hc
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
      obtain ⟨α, hα1, hα2⟩ := x_lt_supA_a_lt_sup Anonempty Abddabv (sup-y) sup_sub_y_lt_x
      have alpha_eq_n0_y : ∃(n₀ : ℕ), α = n₀ • y
      · exact hα1
      obtain ⟨n₀ , hn₀⟩:=alpha_eq_n0_y
      have sup_lt: sup < (n₀ + 1) • y
      · rw[hn₀] at hα2
        rw[sub_lt_iff_lt_add] at hα2
        rw[succ_nsmul]
        exact hα2
      have n0_add_1_in_A: (n₀ + 1) • y ∈ A:= by
        use (n₀ +1)
      have n0_add_one_lt_sup:= supA_lt_a_in_A Anonempty Abddabv
      specialize n0_add_one_lt_sup ((n₀ + 1) • y) n0_add_1_in_A
      linarith

  --quedó más larga de lo que querría, pero bueno, de momento...

theorem Q_is_dense (x y : X) (h : x < y) :
  ∃ p : ℚ, x < p ∧ p < y := by
  exact exists_rat_btwn h

  -- este lo llamo distinto para aclararme, pero vamos, es tontería

theorem natCast_injective : Function.Injective (fun n : ℕ => (n : X)) :=
  Nat.cast_injective
theorem ratCast_injective : Function.Injective (fun q: ℚ => (q : X)) :=
  Rat.cast_injective
  --es decir, en X están incluidos los racionales, idem para Y

def Nₓ : Set X := {x : X | ∃ n : ℕ, x = n}
def Qₓ : Set X := {x : X | ∃ q : ℚ, x = q}

theorem natCast_A_Y_injective :
  Function.Injective (fun (n : Nₓ) => (n.val : Y)) := by

  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  -- h : (x : Y) = (y : Y)
  -- los naturales se inyectan en Y:
  simp at *
  exact h







theorem Uniqueness_Real_Numbers :
  ∃ f : X → Y,
    Function.Bijective f ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧
    (∀ x y, x < y → f x < f y) := by
    sorry




























    --ya tenemos la contradicción, por transitividad




#print RealField
