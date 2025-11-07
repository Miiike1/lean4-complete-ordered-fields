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

theorem Q_is_dense (R : Type) [RealField R] (x y : R) (h : x < y) :
  ∃ p : ℚ, x < p ∧ p < y := by
  exact exists_rat_btwn h
--pendiente a demostrar por mi





--conjunto de elementos en R (probar que es no vacío y acotado)
def Sℚ (R : Type) [RealField R] : R → (Set ℚ) := fun x => {(q:ℚ ) | ↑ q < x}

def SR (R : Type) [RealField R] : R → (Set R) := fun x => {(q : R) | q ∈ Sℚ R x}

lemma forall_x_SℚRx_nonempty (R : Type) [RealField R] (x : R) : (Sℚ R x).Nonempty:= by

  have aux : x - 1 < x := by linarith
  have hp := Q_is_dense R (x-1) x aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  exact hp2

theorem forall_x_SℚRx_bddabv (R : Type) [RealField R] (x : R) : BddAbove (Sℚ R x) := by
  rw[BddAbove, upperBounds]
  have aux : x < x + 1 := by linarith
  have hp := Q_is_dense R x (x+1)  aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  intro a
  rw [Sℚ]
  intro h
  have aux:= lt_trans h hp1
  apply le_of_lt at aux
  exact Rat.cast_le.mp aux


--se puede modificar esto y aplicar que Sℚ R x es no vacío, sacando un testigo etc

theorem forall_x_SRRx_nonempty (R : Type) [RealField R] (x : R) : (SR R x).Nonempty:= by

  have aux : x - 1 < x := by linarith
  have hp := Q_is_dense R (x-1) x aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  rw[SR]
  simp
  exact hp2


theorem forall_x_SRRx_bddabv (R : Type) [RealField R] (x : R) : BddAbove (SR R x) := by
  rw[BddAbove, upperBounds]
  have aux : x < x + 1 := by linarith
  have hp := Q_is_dense R x (x+1)  aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  intro a
  rw [SR]
  intro h
  simp at h
  obtain ⟨q,hq,ha⟩:= h
  rw[Sℚ] at hq; simp at hq
  linarith


--def Sℚ (R : Type) [RealField R] : R → (Set ℚ) := fun x => {(q:ℚ ) | (q:R) < x}
--def SR (R : Type) [RealField R] : R → (Set X ) := fun x => { (q : X) | q ∈ Sℚ R x}

def Supx (R : Type) [RealField R] : R → R := fun x => sSup (SR R x)


theorem Supx_is_idd (R : Type) [RealField R] :  Supx R = id := by
  funext x
  rw[id,Supx]
  have xislub : IsLUB (SR R x) x := by
    constructor
    · intro a ha
      rw[SR, Sℚ] at ha
      simp at ha
      obtain ⟨q,hq,ha⟩:=ha
      rw[ha] at hq
      exact le_of_lt hq

    · intro y hy
      rw[upperBounds,SR,Sℚ] at hy
      simp at hy
      by_contra hc
      push_neg at hc
      obtain ⟨p,hp1,hp2⟩ := Q_is_dense R y x hc
      have hy2 := hy p hp2
      linarith
  have nonempty:= forall_x_SRRx_nonempty R x
  have bddabv  := forall_x_SRRx_bddabv R x
  have IsLUBsup:= sSup_axiom (SR R x) nonempty bddabv
  exact IsLUBsup.unique xislub

--función definida, la que da el isomorfismo (a comprobar)
--cambiar algún nombre

lemma Sℚ_inj (R) [RealField R] : Function.Injective (Sℚ R):= by
  intro x y h
  by_contra hc
  rw[Sℚ , Sℚ] at h
  simp at h
  push_neg at hc
  by_cases hc1: x < y
  · obtain ⟨q, hqx, hqy⟩ := Q_is_dense R x y hc1
    have hqinSQY: q ∈ Sℚ R y := by
      exact hqy
    have hqnoinSQX: q ∉ Sℚ R x:= by
      rw[Sℚ]
      simp
      linarith
    have diff_sets:  Sℚ R x ≠ Sℚ R y := by
      rw[Sℚ, Sℚ]
      simp
      rw[Set.ext_iff]
      push_neg
      use q
      right
      constructor
      · exact hqnoinSQX
      · exact hqinSQY
    trivial
  · push_neg at hc1
    symm at hc
    have hc1:= lt_of_le_of_ne hc1 hc
    obtain ⟨q, hqy, hqx⟩ := Q_is_dense R y x hc1
    have hqinSQX: q ∈ Sℚ R x := by
      exact hqx
    have hqnoinSQY: q ∉ Sℚ R y:= by
      rw[Sℚ]
      simp
      linarith
    have diff_sets:  Sℚ R x ≠ Sℚ R y := by
      rw[Sℚ, Sℚ]
      simp
      rw[Set.ext_iff]
      push_neg
      use q
      left
      constructor
      · exact hqinSQX
      · exact hqnoinSQY
    trivial

lemma SR_injective (R : Type) [RealField R] : Function.Injective (SR R) := by
  intro x y hxy
  rw[SR, SR] at hxy
  by_contra hc
  push_neg at hc
  by_cases hc1: x < y


def SRZ (R Z : Type) [RealField R] [RealField Z] :
  R → Z := fun x => sSup {(q : Z) | q ∈ Sℚ R x}

--clave: los números racionales más pequeños que un x dado coinciden
--con los de su imagen por la aplicación SRZ
#print Sℚ X


theorem SℚRx_eq_SℚZSRZRZx (R Z : Type) [RealField R] [RealField Z] (x : R): Sℚ R x = Sℚ Z (SRZ R Z x):= by
  rw[Sℚ,Sℚ]
  rw[Set.ext_iff]
  intro q

  constructor
  · intro hq
    simp at *
    rw[SRZ,Sℚ]
    simp
    have x_eq_supp: sSup {x_1 | ∃ q ∈ Sℚ R x, ↑q = x_1} = x
    · have idd:= Supx_is_idd R
      apply congrFun idd x
    rw[Sℚ] at x_eq_supp
-- problema al hacer rw (debería poder pero no entiende que es la misma estructura)
    simp at x_eq_supp
   -- problema al hacer rw (debería poder pero no entiende que es la misma estructura)
    rw[x_eq_supp]



#print SR






def Supx (R : Type) [RealField R] : R → R := fun x => sSup (SR R x)








theorem SZR_is_SRZ_inv (R Z : Type) [RealField R] [RealField Z] : (SRZ Z R) ∘ (SRZ R Z) = id := by
  funext x
  rw[id]
  have fx:= SRZ R Z x
  have compo: (SRZ Z R ∘ SRZ R Z) x= SRZ Z R (SRZ R Z x):=rfl
  rw[compo]
  rw[SRZ,SRZ]
  sorry

--teorema a demostrar
theorem Uniqueness_Real_Numbers (X Y : Type) [RealField X] [RealField Y] :
  ∃ f : X → Y,
    Function.Bijective f ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧
    (∀ x y, x < y → f x < f y) := by

  sorry





















    --ya tenemos la contradicción, por transitividad




#print RealField
