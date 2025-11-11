import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty → BddAbove S → IsLUB S (sSup S)
variable {X : Type} [RealField X]
variable {Y : Type} [RealField Y]

open RealField

--print para ver teoremas, axiomas y props dados por la clase
--escribo teoremas útliles para el futuro
lemma supA_lt_x_in_upbdA {A : Set X} (a : X) (hA : A.Nonempty)
 (hB : BddAbove A) : a ∈ upperBounds A → sSup A ≤ a  := by
  intro ha
  exact (sSup_axiom A hA hB).2 ha

lemma gt_sup_then_upbdd {A : Set X} (x : X) (hA : A.Nonempty)
 (hB : BddAbove A) : sSup A < x → x ∈ upperBounds A:= by
  have supp:= (sSup_axiom A hA hB).1
  rw[upperBounds] at supp
  simp at supp
  intro hx
  apply le_of_lt at hx
  intro a ha
  have sup2:= supp ha
  exact le_trans (supp ha) hx

lemma supA_lt_a_in_A {A : Set X} (hA : A.Nonempty)
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

lemma forall_x_SℚRx_bddabv (R : Type) [RealField R] (x : R) : BddAbove (Sℚ R x) := by
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
lemma forall_x_SRRx_nonempty (R : Type) [RealField R] (x : R) : (SR R x).Nonempty:= by

  have aux : x - 1 < x := by linarith
  have hp := Q_is_dense R (x-1) x aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  rw[SR]
  simp
  exact hp2


lemma forall_x_SRRx_bddabv (R : Type) [RealField R] (x : R) : BddAbove (SR R x) := by
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


def Supx (R : Type) [RealField R] : R → R := fun x => sSup (SR R x)


lemma Supx_is_idd (R : Type) [RealField R] :  Supx R = id := by
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

lemma Supx_is_idd2 (R : Type) [RealField R] :∀(x:R),  Supx R x = x := by
  intro x
  have idd:= Supx_is_idd R
  rw[idd]
  rfl

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

def SRZ (R Z : Type) [RealField R] [RealField Z] :
  R → Z := fun x => sSup {(q : Z) | q ∈ Sℚ R x}


--clave: los números racionales más pequeños que un x dado coinciden
--con los de su imagen por la aplicación SRZ

theorem rat_btw_p_lt_x_lt_q (R : Type) [RealField R] (x : R) (p q : ℚ) :
  ↑ p < x → x < ↑ q → p < q := by
  intro hp hq
  have  p_lt_q: (↑p:R) < (↑q:R) := by
    linarith
  norm_cast at p_lt_q

theorem rat_lt_x_lt_rat (R : Type) [RealField R] (x : R) (p q : ℚ) :
   ↑ q < x → x < ↑ p → (q : ℚ) < (p : ℚ):= by
  intro hq hp
  have := lt_trans hq hp
  norm_cast at this


theorem rat_btw_xinR_yinZ (R Z : Type) [RealField R] [RealField Z] (x : R) (y : Z) (p : ℚ) :
  ↑ p < x →  y = ↑ p → ∃(q : ℚ), ↑q < x ∧ y < ↑ q := by
  intro hx hy
  have hq:= Q_is_dense R p x hx
  obtain ⟨q, hq1, hq2⟩:= hq
  use q
  constructor
  · exact hq2
  · rw[hy]
    norm_cast at *

theorem x_lt_x_add_one {R : Type} [RealField R] {x : R} : x < x + 1 := by linarith

theorem x_sub_one_lt_x {R : Type} [RealField R] {x : R} : x - 1 < x := by linarith

theorem pR_lt_x_le_qR_y_eq_pZ_y_le_qZ (R Z : Type) [RealField R] [RealField Z]
  (x : R) (y : Z) (p q : ℚ) : ↑ p < x →  x ≤ ↑q →  y = ↑ p → y <  ↑q := by

  intro h1 h2 h3
  have := lt_of_lt_of_le  h1 h2
  norm_cast at this
  rw[h3]
  norm_cast

lemma rats_lt_x_nonempt {R : Type} [RealField R] (x : R) :
 {q : ℚ | ↑q < x }.Nonempty:= by

· obtain ⟨qaux,hqaux1,hqaux2⟩:= Q_is_dense R (x-1) x x_sub_one_lt_x; use qaux; exact hqaux2

lemma rats_lt_sup_rats_nonempt (R Z : Type) [RealField R] [RealField Z] (x : R) :
  { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}.Nonempty := by
  obtain ⟨qaux, hq⟩:= rats_lt_x_nonempt x
  use (↑qaux)
  simp
  exact hq

lemma rats_lt_x_bddabv {R : Type} [RealField R] (x : R) :
  BddAbove {q : ℚ | ↑q < x }:= by

  obtain ⟨p,hp1,hp2⟩ := Q_is_dense R x (x+1) x_lt_x_add_one
  use p; rw[upperBounds]
  intro a ha
  simp at ha
  apply lt_trans ha at hp1
  norm_cast at hp1
  exact le_of_lt hp1

lemma rats_lt_sup_rats_bddabv (R Z : Type) [RealField R] [RealField Z] (x : R) :
  BddAbove { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y} := by

  obtain ⟨p,hp1,hp2⟩ := Q_is_dense R x (x+1) x_lt_x_add_one
  use ↑ p
  intro a ha
  simp at ha; obtain ⟨r,ha1,ha2⟩:=ha; symm at ha2
  apply le_of_lt at hp1
  have :=  pR_lt_x_le_qR_y_eq_pZ_y_le_qZ R Z x a r p ha1 hp1 ha2
  apply le_of_lt at this
  exact this

--escribir teorema que demuestre que IsLUB set sup para acortar la demostración
--para el futuro

theorem SℚRx_eq_SℚZSRZRZx (R Z : Type) [RealField R] [RealField Z] (x : R) :
  Sℚ R x = Sℚ Z (SRZ R Z x):= by

  rw[Sℚ,Sℚ]
  rw[Set.ext_iff]

  let set := { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}
  let sup := sSup { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}

  have set_eq_set: set= { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y} := by rfl

  have sup_eq_sup: sup = sSup { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y} := by rfl

  have nonempt2 := rats_lt_sup_rats_nonempt R Z x

  have bddabv2  := rats_lt_sup_rats_bddabv R Z x

  have sup_IsLUB:= sSup_axiom set nonempt2 bddabv2

  intro q
  constructor
  · intro hq
    rw[SRZ,Sℚ]
    push_neg at hq

    have q_in_set: (↑ q:Z) ∈ set
    · rw[set_eq_set]
      simp
      exact hq

    have q_lt_sup : (↑ q:Z) < sup
    · rw[sup_eq_sup]
      simp at hq
      apply sup_IsLUB.1 at q_in_set

      have coq_nesup: ↑q ≠ sup
      · by_contra hc ; symm at hc
        obtain ⟨p,hp1,hp2⟩:= rat_btw_xinR_yinZ R Z x sup q hq hc
        have p_in_set : (↑ p:Z) ∈ set := by rw[set_eq_set]; simp; exact hp1
        have contra: ↑ p ≤ sup

        · rw[sup_eq_sup]
          exact sup_IsLUB.1 p_in_set
        linarith

      apply lt_or_gt_of_ne at coq_nesup
      cases coq_nesup
      · linarith
      · linarith

    rw[sup_eq_sup] at q_lt_sup
    exact q_lt_sup

  · intro hq; simp at hq

    rw[SRZ, Sℚ] at hq

    by_contra hc; simp at hc
    · have q_gt_sup:   sup ≤  q
      · rw[sup_eq_sup]
        have q_is_uppbd: ↑q ∈ upperBounds set
        · rw[set_eq_set]
          intro a ha
          simp at ha
          obtain ⟨p,hp1,hp2⟩:= ha
          symm at hp2
          have := pR_lt_x_le_qR_y_eq_pZ_y_le_qZ R Z x a p q hp1 hc hp2
          exact le_of_lt this
        exact sup_IsLUB.2 q_is_uppbd
      rw[sup_eq_sup] at *
      have aux: sSup { x_1:Z | ∃ q  ∈ {q:ℚ | ↑q < (x : R)}, (↑q : Z) = x_1} = sup := by rfl
      rw[aux] at hq
      linarith

theorem compo (R Z : Type) [RealField R] [RealField Z] (x : R) :
 (SRZ Z R ∘ SRZ R Z) x= SRZ Z R (SRZ R Z x):=rfl


theorem SZR_is_SRZ_inv (R Z : Type) [RealField R] [RealField Z] : (SRZ Z R) ∘ (SRZ R Z) = id := by

  funext x
  have:= SℚRx_eq_SℚZSRZRZx R Z x
  rw[id]
  rw[compo]
  rw[SRZ]
  rw[<-this,Sℚ]
  exact Supx_is_idd2 R x

theorem SZR_SRZ_x_eq_x (R Z : Type) [RealField R] [RealField Z] :
  ∀(x : R), ((SRZ Z R) ∘ (SRZ R Z)) x = x := by

  intro x
  have idd:= SZR_is_SRZ_inv R Z
  rw[idd]
  rfl

theorem SRZ_is_bijective (R Z : Type) [RealField R] [RealField Z] :
  Function.Bijective (SRZ R Z) := by

  have bij_if_inv: Function.Bijective (SRZ R Z) ↔
  ∃ g, Function.LeftInverse g (SRZ R Z) ∧ Function.RightInverse g (SRZ R Z):=by
    exact Function.bijective_iff_has_inverse
  rw [bij_if_inv]
  use (SRZ Z R)

  constructor

  · rw[Function.LeftInverse]
    intro x
    rw[<-compo]
    have := SZR_SRZ_x_eq_x
    specialize this R Z x
    exact this

  · rw[Function.RightInverse]
    intro z
    rw[<-compo]
    have := SZR_SRZ_x_eq_x
    specialize this Z R z
    exact this


def addset {R : Type} [Ring R] :
  (Set R) → (Set R) → (Set R) := fun  U V => {(x : R) | ∃ u ∈ U, ∃ v ∈ V, x = u + v }

lemma Sℚ_x_add_Sℚ_y_eq_Sℚ_A_addset_B {R : Type} [RealField R] (x : R) (y : R) :
  addset (Sℚ R x) (Sℚ R y) = Sℚ R (x + y) := by
  rw[addset,Sℚ,Sℚ,Sℚ]
  apply Set.ext_iff.mpr
  intro k
  constructor

  · simp
    intro x1 hx1 x2 hx2 hk
    rw[hk, Rat.cast_add]
    linarith

  · simp
    intro h
    have ineq : (x + y - ↑k)/2 >0 := by linarith
    have : x-(x + y - ↑k)/2 < x := by linarith
    obtain ⟨p,hp1,hp2⟩ := Q_is_dense R (x-(x + y - ↑k)/2) x this

    use p
    constructor
    · exact hp2
    · use k - p
      constructor
      · rw[Rat.cast_sub]
        linarith
      · simp


lemma sup_ad_eq_ad_sup {R : Type} [RealField R] (x y : R) :
   Supx R (x+y) = Supx R x + Supx R y:= by

  have ineq1 : Supx R (x+y) ≤  Supx R x + Supx R y
  ·
    sorry
  sorry










--theorem sSup_SℚRx_plus_y_eq_sSup_SℚRx_plus_SℚRy {R:Type} [RealField R] (x y : R): Sℚ R (x + y) = (Sℚ R x) addset (Sℚ R x)







theorem add_preserved {R Z:Type} [RealField R] [RealField Z] :
  ∀ (x y : R) ,  SRZ R Z (x + y) =  SRZ R Z x + SRZ R Z y := by
  intro x y
  rw[SRZ, SRZ]
  sorry



--teorema a demostrar
theorem Uniqueness_Real_Numbers (X Y : Type) [RealField X] [RealField Y] :
  ∃ f : X → Y,
    Function.Bijective f ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧
    (∀ x y, x < y → f x < f y) := by

  use SRZ X Y
  constructor
  · exact  SRZ_is_bijective X Y

  sorry
