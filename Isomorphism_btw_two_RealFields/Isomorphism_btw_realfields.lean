import Mathlib

class RealField (R : Type) extends SupSet R, Field R, LinearOrder R, IsStrictOrderedRing R where
  sSup_axiom :  ∀ (S: Set R), S.Nonempty → BddAbove S → IsLUB S (sSup S)
variable {X : Type} [RealField X]
variable {Y : Type} [RealField Y]

open RealField
-- el supremo de A es la menor de las cotar superiores
lemma supA_lt_x_in_upbdA {A : Set X} (a : X) (hA : A.Nonempty)
 (hB : BddAbove A) : a ∈ upperBounds A → sSup A ≤ a  := by
  intro ha
  exact (sSup_axiom A hA hB).2 ha
--conjunto no vacío y acotado superiormente, mayor que el supremo implica cota superior
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
--mayor que el supremo implica cota superior
lemma supA_gt_a_in_A {A : Set X} (hA : A.Nonempty)
 (hB : BddAbove A) (a : X) :a ∈ A → a ≤ sSup A := by
  intro ha
  exact (sSup_axiom A hA hB).1 ha
--el supremo es cota superior
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
--propiedad arquimediana
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
      have n0_add_one_lt_sup:= supA_gt_a_in_A Anonempty Abddabv
      specialize n0_add_one_lt_sup ((n₀ + 1) • y) n0_add_1_in_A
      linarith
--densidad de los racionales en R (a demostrar por mi)
theorem Q_is_dense (R : Type) [RealField R] (x y : R) (h : x < y) :
  ∃ p : ℚ, x < p ∧ p < y := by
  exact exists_rat_btwn h
--función que lleva nuestro elemento a R a los elementos de ℚ menores que él
def ℚlower (R : Type) [RealField R] : R → (Set ℚ) := fun x => {(q:ℚ ) | ↑ q < x}

def ℚlower_gt0 (R : Type) [RealField R] : R → (Set ℚ) := fun x => {(q : ℚ )| 0 < q ∧ q ∈ ℚlower R x}
--función que lleva nuestro elemento a R a los elementos de ℚ menores que él y mayores que 0
def SR (R : Type) [RealField R] : R → (Set R) := fun x => {(q : R) | q ∈ ℚlower R x}
--defimimos el isomorfisno, dado por el supremo en el cuerpo de llegada
--de los racionales menores que x ∈ cuerpo de salida
def φ (R Z : Type) [RealField R] [RealField Z] :
  R → Z := fun x => sSup {(q : Z) | q ∈ ℚlower R x}
--φ de R en R
def Supx (R : Type) [RealField R] : R → R := fun x => sSup (SR R x)
--operación entre conjuntos, útil para más tarde
def addset {R : Type} [Ring R] :
  (Set R) → (Set R) → (Set R) := fun  U V => {(x : R) | ∃ u ∈ U, ∃ v ∈ V, x = u + v }
--ooperación entre conjuntos, útil para más tarde
def mulset {R : Type} [Ring R] :
  (Set R) → (Set R) → (Set R) := fun  U V => {(x : R) | ∃ u ∈ U, ∃ v ∈ V, x = u * v }

lemma forall_x_QlowerRx_nonempty (R : Type) [RealField R] (x : R) : (ℚlower R x).Nonempty:= by

  have aux : x - 1 < x := by linarith
  have hp := Q_is_dense R (x-1) x aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  exact hp2

lemma forall_x_QlowerRx_bddabv (R : Type) [RealField R] (x : R) : BddAbove (ℚlower R x) := by
  rw[BddAbove, upperBounds]
  have aux : x < x + 1 := by linarith
  have hp := Q_is_dense R x (x+1)  aux
  obtain ⟨p,hp1,hp2⟩ := hp
  use p
  intro a
  rw [ℚlower]
  intro h
  have aux:= lt_trans h hp1
  apply le_of_lt at aux
  exact Rat.cast_le.mp aux
--la aplicación Qlower es inyectiva
lemma Qlower_inj (R : Type) [RealField R] : Function.Injective (ℚlower R):= by
  intro x y h
  by_contra hc
  rw[ℚlower , ℚlower] at h
  simp at h
  push_neg at hc
  by_cases hc1: x < y
  · obtain ⟨q, hqx, hqy⟩ := Q_is_dense R x y hc1
    have hqinSQY: q ∈ ℚlower R y := by
      exact hqy
    have hqnoinSQX: q ∉ ℚlower R x:= by
      rw[ℚlower]
      simp
      linarith
    have diff_sets:  ℚlower R x ≠ ℚlower R y := by
      rw[ℚlower, ℚlower]
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
    have hqinSQX: q ∈ ℚlower R x := by
      exact hqx
    have hqnoinSQY: q ∉ ℚlower R y:= by
      rw[ℚlower]
      simp
      linarith
    have diff_sets:  ℚlower R x ≠ ℚlower R y := by
      rw[ℚlower, ℚlower]
      simp
      rw[Set.ext_iff]
      push_neg
      use q
      left
      constructor
      · exact hqinSQX
      · exact hqnoinSQY
    trivial

theorem x_eq_y_iff_QlowerRx_eq_QlowerRy {R : Type} [RealField R] (x y : R) :
  x = y ↔ ℚlower R x = ℚlower R y := by
  constructor
  · intro heq
    rw[heq]
  · have inj := Qlower_inj R
    rw[Function.Injective] at inj
    intro hinj
    exact inj hinj

lemma Qlowergt0_determines_Qlower {R : Type} [RealField R] (x y : R) :
   (0 < x) → (0 < y) →  ℚlower_gt0 R x = ℚlower_gt0 R y → ℚlower R x = ℚlower R y := by
  intro hx hy hsq
  rw[ℚlower_gt0, ℚlower_gt0, ℚlower, ℚlower] at *; simp at *
  ext a
  constructor
  · simp
    intro hax
    by_cases ha : (↑a : R) ≤ 0
    · linarith
    push_neg at ha
    have a_in_Qlowergt0 : a ∈ { (q : ℚ) | 0 < q ∧ ↑q < x}
    · simp
      constructor
      · norm_cast at ha
      · exact hax
    rw[ hsq] at a_in_Qlowergt0
    obtain ⟨ha', ha''⟩ := a_in_Qlowergt0; exact ha''
  · simp
    intro hay
    by_cases ha : (↑a : R) ≤ 0
    · linarith
    push_neg at ha
    have a_in_Sℚ' : a ∈ { (q : ℚ) | 0 < q ∧ ↑q < y}
    · simp
      constructor
      · norm_cast at ha
      · exact hay
    rw[<- hsq] at a_in_Sℚ'
    obtain ⟨ha', ha''⟩ := a_in_Sℚ'; exact ha''

lemma Qlower_determines_Qlowergt0 {R : Type}
[RealField R] {x y : R} : (0 < x) → (0 < y)
  →  ℚlower R x = ℚlower R y → ℚlower_gt0 R x = ℚlower_gt0 R y := by
  intro hx hy hsq
  ext a
  rw[ℚlower_gt0, ℚlower_gt0, ℚlower, ℚlower]
  constructor
  · simp
    intro ha' ha''
    constructor
    · exact ha'
    · apply Qlower_inj at hsq
      linarith
  · simp
    intro ha' ha''
    constructor
    · exact ha'
    · apply Qlower_inj at hsq
      linarith

theorem x_eq_y_iff_Qlowergt0Rx_eq_Qlowergt0Ry
  (R : Type) [RealField R] (x y : R) :(0 < x) →
  (0 < y) → (x = y ↔ ℚlower_gt0 R x = ℚlower_gt0 R y) := by
  intro hx hy
  constructor
  · intro heq
    rw[heq]
  · intro eqq
    apply Qlowergt0_determines_Qlower x y hx hy at eqq
    apply Qlower_inj R at eqq
    exact eqq
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
  rw[ℚlower] at hq; simp at hq
  linarith
-- tutoría, igual a demostrar que SRZ R R es la identidad, podría reescribirlo... (debería)
lemma Supx_is_idd (R : Type) [RealField R] :  Supx R = id := by
  funext x
  rw[id,Supx]
  have xislub : IsLUB (SR R x) x := by
    constructor
    · intro a ha
      rw[SR, ℚlower] at ha
      simp at ha
      obtain ⟨q,hq,ha⟩:=ha
      rw[ha] at hq
      exact le_of_lt hq

    · intro y hy
      rw[upperBounds,SR,ℚlower] at hy
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

lemma coertion_QlowerRx_nonempt_in_Z (R Z : Type) [RealField R] [RealField Z] (x : R) :
  {(q : Z) | q ∈ ℚlower R x}.Nonempty := by

  have: {(q : Z) | q ∈ ℚlower R x} =  { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}:= by rfl
  rw[this]; exact rats_lt_sup_rats_nonempt R Z x

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

lemma coertion_QlowerRx_bdd_in_Z (R Z : Type) [RealField R] [RealField Z] (x : R) :
  BddAbove {(q : Z) | q ∈ ℚlower R x} := by
  have: {(q : Z) | q ∈ ℚlower R x} =  { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}:= by rfl
  rw[this]; exact rats_lt_sup_rats_bddabv R Z x

theorem A_nonem_bddabv_p_upbd_if_p_gt_sup
    {R : Type} [RealField R] {A : Set R} (p : R) :
    A.Nonempty → BddAbove A → sSup A < p → p ∈ upperBounds A := by
  intro nonem bdd
  have := sSup_axiom A nonem bdd
  intro hp
  obtain ⟨h1, h2⟩:= this
  intro a ha
  rw[upperBounds] at h1
  simp at h1
  apply h1 at ha
  linarith
--los racionales menores que x∈X son iguales a los racionales menores a su imagen en Z por F_iso R Z
theorem QlowerRx_eq_QlowerZF_isoRZx (R Z : Type) [RealField R] [RealField Z] (x : R) :
  ℚlower R x = ℚlower Z (φ R Z x):= by

  rw[ℚlower,ℚlower]
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
    rw[φ,ℚlower]
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
    rw[φ, ℚlower] at hq
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
 (φ Z R ∘ φ R Z) x = φ Z R (φ R Z x):=rfl

theorem gt_sup_if_upbd {R : Type}
 [RealField R] (x : R) (A : Set R) (ha : ∀ a ∈ A, a ≤ x) :
  A.Nonempty → sSup A ≤ x:= by
  intro nnempt
  have : BddAbove A := by
    use x
    rw[upperBounds]
    simp
    intro b hb
    apply ha at hb
    exact hb
  have supIsLUB:= (sSup_axiom A nnempt this).2
  have x_upbd: x ∈ upperBounds A := by
    rw[upperBounds]
    simp
    intro b hb
    apply ha at hb
    exact hb
  apply supIsLUB at x_upbd
  exact x_upbd

theorem φZR_is_φRZ_inverse (R Z : Type)
[RealField R] [RealField Z] : (φ Z R) ∘ (φ R Z) = id := by
  funext x
  have:= QlowerRx_eq_QlowerZF_isoRZx R Z x
  rw[id]
  rw[compo]
  rw[φ]
  rw[<-this,ℚlower]
  exact Supx_is_idd2 R x

theorem φφx_eq_x (R Z : Type) [RealField R] [RealField Z] :
  ∀(x : R), ((φ Z R) ∘ (φ R Z)) x = x := by
  intro x
  have idd:= φZR_is_φRZ_inverse R Z
  rw[idd]
  rfl

theorem φ_is_bijective (R Z : Type) [RealField R] [RealField Z] :
  Function.Bijective (φ R Z) := by
  have bij_if_inv: Function.Bijective (φ R Z) ↔
  ∃ g, Function.LeftInverse g (φ R Z) ∧ Function.RightInverse g (φ R Z):=by
    exact Function.bijective_iff_has_inverse
  rw [bij_if_inv]
  use (φ Z R)
  constructor
  · rw[Function.LeftInverse]
    intro x
    rw[<-compo]
    have := φφx_eq_x
    specialize this R Z x
    exact this
  · rw[Function.RightInverse]
    intro z
    rw[<-compo]
    have := φφx_eq_x
    specialize this Z R z
    exact this

lemma Qlower_x_addset_Qlower_y_eq_Qlower_x_add_y {R : Type} [RealField R] (x : R) (y : R) :
  addset (ℚlower R x) (ℚlower R y) = ℚlower R (x + y) := by
  rw[addset,ℚlower,ℚlower,ℚlower]
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
  rw[ Supx_is_idd2 R (x+y), Supx_is_idd2 R x, Supx_is_idd2 R y]

lemma subss1 (R : Type) {A B : Set R} : A ⊂ B →  A ⊆ B ∧ A ≠ B := by
  exact ssubset_iff_subset_ne.mp

lemma subss2 (R : Type) {A B : Set R} : A ⊆ B ∧ A ≠ B →  A ⊂ B  := by
  exact ssubset_iff_subset_ne.mpr

lemma x_lt_y_then_Qlowerx_in_Qlowery {R : Type} [RealField R]
  (x y : R) : (x <  y) →  ((ℚlower R x) ⊂ (ℚlower R y)) := by
  intro hxy
  constructor
  · intro a ha
    rw[ℚlower] at *; simp at *; linarith
  · by_contra hc
    by_cases case: ℚlower R y = ℚlower R x
    · apply Qlower_inj at case ; linarith
    · rw[ℚlower, ℚlower] at *
      simp at hc
      obtain ⟨q, hq1, hq2⟩ := Q_is_dense R x y hxy
      have := hc q hq2 ; linarith

lemma Qlowerx_in_Qlowery_then_x_lt_y {R : Type} [RealField R] (x y : R) :
 ((ℚlower R x) ⊂ (ℚlower R y)) → (x <  y)  := by
  intro hin
  apply subss1 at hin
  obtain ⟨hin, hneq⟩ := hin
  have neq: x ≠ y
  · by_contra hc
    have aux: ℚlower R x = ℚlower R y
    · rw[hc]
    tauto
  by_contra hc
  simp at hc
  have hcineq: y < x:= by exact Std.lt_of_le_of_ne hc (id (Ne.symm neq))
  apply x_lt_y_then_Qlowerx_in_Qlowery y x at hcineq
  have subsse : ℚlower R x ⊂ ℚlower R y
  · have : ℚlower R x ⊆ ℚlower R y ∧ ℚlower R x ≠ ℚlower R y := by
      constructor
      · exact hin
      · exact hneq
    exact subss2 ℚ this
  apply ssubset_asymm at subsse
  tauto

lemma Qlower_preserves_order {R : Type} [RealField R] (x y : R) :
  ((ℚlower R x) ⊂ (ℚlower R y)) ↔ (x <  y):=by
  constructor
  · intro h1
    exact Qlowerx_in_Qlowery_then_x_lt_y x y h1
  · intro h2
    exact x_lt_y_then_Qlowerx_in_Qlowery x y h2

lemma φ_preserves_order (R Z : Type) [RealField R]
  [RealField Z] (x y : R) : x < y ↔ φ R Z x < φ R Z y := by
  constructor
  · intro hxy
    apply (Qlower_preserves_order x y).mpr at hxy
    apply (Qlower_preserves_order (φ R Z x) (φ R Z y)).mp
    rw[<-QlowerRx_eq_QlowerZF_isoRZx R Z x,<-QlowerRx_eq_QlowerZF_isoRZx R Z y]; exact hxy
  · intro hin
    apply (Qlower_preserves_order (φ R Z x) (φ R Z y)).mpr at hin
    apply (Qlower_preserves_order x y).mp
    rw[QlowerRx_eq_QlowerZF_isoRZx R Z x,QlowerRx_eq_QlowerZF_isoRZx R Z y]; exact hin

lemma φ_preserves_add (R Z : Type) [RealField R] [RealField Z] (x y : R) :
  φ R Z (x + y) = φ R Z x + φ R Z y := by
  rw[x_eq_y_iff_QlowerRx_eq_QlowerRy]
  rw[<- QlowerRx_eq_QlowerZF_isoRZx]
  rw[<-Qlower_x_addset_Qlower_y_eq_Qlower_x_add_y]
  rw[<-Qlower_x_addset_Qlower_y_eq_Qlower_x_add_y]
  rw[<- QlowerRx_eq_QlowerZF_isoRZx,<- QlowerRx_eq_QlowerZF_isoRZx]

lemma zero_to_zero (R Z : Type) [RealField R] [RealField Z] : φ R Z 0 = 0:= by
    have zero_eq : (0 : R) = 0 + 0 := by linarith
    have fi_eq1 : φ R Z 0 =  φ R Z (0 + 0) := by nth_rewrite 1 [zero_eq]; rfl
    have fi_eq2 : φ R Z 0 = φ R Z 0 + φ R Z 0  := by
      rw[ φ_preserves_add R Z 0 0] at fi_eq1
      exact fi_eq1
    linarith

theorem Qlower_gt0Rx_eq_Qlower_gt0ZφRZx (R Z : Type) [RealField R] [RealField Z] (x : R) : (0 < x) →
  ℚlower_gt0 R x = ℚlower_gt0 Z (φ R Z x):= by
  intro hx
  have cero_lt_φx : 0 < (φ R Z x)
  · rw[<- zero_to_zero R Z]
    exact (φ_preserves_order R Z 0 (x)).mp hx
  have Qlow_eq_Qlow : ℚlower R x = ℚlower Z (φ R Z x) := by exact QlowerRx_eq_QlowerZF_isoRZx R Z x
  rw[ℚlower_gt0, ℚlower_gt0]
  ext a
  constructor
  · intro ha
    simp
    constructor
    · exact ha.left
    · rw[<-QlowerRx_eq_QlowerZF_isoRZx]
      exact ha.right
  · intro ha
    simp
    constructor
    · exact ha.left
    · rw[<- QlowerRx_eq_QlowerZF_isoRZx] at ha
      exact ha.right

lemma Qlower_gt0_preserves_mulset {R : Type} [RealField R] {x : R} {y : R} :
 (0 < x) → ( 0 < y) → mulset (ℚlower_gt0 R x) (ℚlower_gt0 R y) = ℚlower_gt0 R (x*y) := by
  rw[ℚlower_gt0, ℚlower_gt0]
  have set_eq {z : R} :
  {(q : ℚ) | 0 < q ∧ ↑q < z} =  {(q : ℚ) | 0 < q ∧  q ∈ ℚlower R z} := by rw[ℚlower]; rfl
  rw[<-set_eq]
  intro hx hy
  rw[mulset]
  ext a
  constructor
  · simp
    intro p hp1 hp2 q hq1 hq2 ha
    rw[ℚlower_gt0] at *
    rw[<-set_eq]
    simp at *
    have ha' : ↑a = ↑p * ↑q := by norm_cast
    rw[ha', Rat.cast_mul]
    have aux2: ↑ p * y < x * y := by
      exact RealField.mul_lt_mul_of_pos_right (↑p) x y hp2 hy
    have aux3 : ↑ p * ↑ q < ↑ p * y := by
      have cero_lt_p : (0 : R) < ↑p := by norm_cast
      exact RealField.mul_lt_mul_of_pos_left (↑q) y ↑p hq2 cero_lt_p
    constructor
    · exact (Rat.mul_pos_iff_of_pos_left hp1).mpr hq1
    · linarith
  · rw[ℚlower_gt0]; simp
    intro ha1 ha2
    have hcoa2: 0 < (↑ a:R) := by
      norm_cast
    have ineq_1 : 0 < (x*y)/a
    · have ineq_2 : 1 < (x*y)/a := by
        field_simp
        exact ha2
      linarith
    have ineq_3: x / ((x * y)/a) < x := by
      field_simp
      exact ha2
    have ineq_4: 0 < x / ((x * y)/a) := by
      field_simp
      simp
      exact ha1
    obtain ⟨p,hp1,hp2⟩ := Q_is_dense R (x/((x * y)/a)) x ineq_3
    have ineq_5 := lt_trans ineq_4 hp1
    use p
    constructor
    · constructor
      · norm_cast at ineq_5
      · exact hp2
    · use a/p
      constructor
      · constructor
        · norm_cast at ineq_5
          exact div_pos ha1 ineq_5
        · rw[ℚlower]; simp
          field_simp at *
          exact hp1
      field_simp
      norm_cast at ineq_5
      rw[div_self ]; linarith

lemma a_lt_b_Sℚa_in_Sℚb (R : Type) [RealField R] (a b : R) : a ≤ b ↔ ℚlower R a ⊆ ℚlower R b := by
  constructor
  · intro hab q hq
    rw[ℚlower] at *
    simp at *
    linarith
  · intro hab
    rw[ℚlower, ℚlower] at hab
    simp at hab
    by_contra hc
    push_neg at hc
    obtain ⟨q, hq1, hq2⟩ := Q_is_dense R b a hc
    specialize hab q
    have := hab hq2
    linarith

lemma A_in_B_supA_lt_supB (R : Type) [RealField R] (A B : Set R) :
   A ⊆ B →  A.Nonempty → BddAbove B → sSup A ≤ sSup B := by
  intro AB noneA Bbdd
  have noneB : B.Nonempty := by exact Set.Nonempty.mono AB noneA
  have Abdd : BddAbove A
  · rw[BddAbove] at Bbdd
    rw[upperBounds] at Bbdd
    obtain ⟨x, hx⟩:=Bbdd
    simp at hx
    use x
    intro a ha
    have aB : a∈B := by
      exact Set.mem_of_subset_of_mem AB ha
    exact hx aB
  have ISLUBA := sSup_axiom A noneA Abdd
  have ISLUBB := sSup_axiom B noneB Bbdd
  have clue := ISLUBA.right
  have supBuppbd : sSup B ∈ upperBounds A
  · intro b hb
    have bB : b  ∈ B := by
      exact Set.mem_of_subset_of_mem AB hb
    exact ISLUBB.left bB
  apply clue at supBuppbd
  exact supBuppbd

lemma supZ_Qlower_gt0Rx_eq_φRZx
  (R Z : Type) [RealField R] [RealField Z] (x : R) : 0 < x →
   sSup { y : Z | ∃ q ∈ ℚlower_gt0 R x, y = (q : Z)}
  = φ R Z x := by
  have reww:
     { y : Z | ∃ q ∈ ℚlower_gt0 R x, y = (q : Z)} = { y : Z | ∃ q ∈ ℚlower R x, y = (q : Z) ∧ 0 < q}
  · ext a
    rw[ℚlower_gt0, ℚlower]
    simp
    constructor
    · intro haux
      obtain ⟨q, hq1, hq2⟩ := haux
      obtain ⟨hq1, hq3⟩ := hq1
      use q
    · intro haux
      obtain ⟨q, hq1, hq2⟩ := haux
      obtain ⟨hq2, hq3⟩ := hq2
      use q
  rw[reww]
  intro hx
  obtain ⟨q,hq1,hq2⟩:= Q_is_dense R 0 x hx
  obtain ⟨k, hk1,hk2⟩:= Q_is_dense R x (x+1) x_lt_x_add_one
  have nonem1: {y : Z | ∃ q ∈ ℚlower R x, y = ↑q }.Nonempty
  · use q
    rw[ℚlower]
    simp
    exact hq2
  have nonem2: {y : Z | ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q}.Nonempty
  · use q
    simp
    constructor
    · exact hq2
    · norm_cast at hq1
  have bdd : BddAbove {y : Z | ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q}
  · rw[BddAbove]
    use k
    rw[upperBounds]
    simp
    intro a x1 hx1 ha hx2
    rw[ℚlower] at hx1
    simp at hx1
    rw[ha]
    have := lt_trans hx1 hk1
    norm_cast
    norm_cast at this
    linarith
  have bdd1 : BddAbove {y : Z | ∃ q ∈ ℚlower R x, y = ↑q}
  · obtain ⟨q, hq1, hq2⟩:= Q_is_dense R x (x+1) x_lt_x_add_one
    use q
    intro k hk
    rw[ℚlower] at hk
    simp at hk
    obtain ⟨nat, hnat1, hnat2⟩:= hk
    rw[hnat2]
    have := lt_trans hnat1 hq1
    norm_cast at this
    norm_cast
    linarith
  have eqq : {y : Z | ∃ q ∈ ℚlower R x, y = ↑q} = {y : Z | ∃ q ∈ ℚlower R x, ↑q = y} := by
    ext a
    constructor
    · intro ha
      simp at ha
      simp
      obtain ⟨q, hq1, hq2⟩:= ha
      use q
      constructor
      · exact hq1
      · symm
        exact hq2
    · intro ha
      simp at ha
      simp
      obtain ⟨q, hq1, hq2⟩:= ha
      use q
      constructor
      · exact hq1
      · symm
        exact hq2
  have inn: {y : Z | ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q} ⊆ {y : Z | ∃ q ∈ ℚlower R x, y = ↑q } := by
    intro a ha
    obtain ⟨b, ha1, ha2, ha3⟩ := ha
    simp
    use b
  have ISLUBsSup := sSup_axiom {y : Z | ∃ q ∈ ℚlower R x, y = ↑q} nonem1 bdd1
  have ISLUB0srz : IsLUB {y : Z | ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q} (φ R Z x):= by
    constructor
    · intro a ha
      have aux1 : a ∈ {y | ∃ q ∈ ℚlower R x, y = ↑q} := by
        obtain ⟨k, ha1, ha2, ha3⟩:=ha
        simp
        use k
      rw[φ]
      have aux2 :=
        A_in_B_supA_lt_supB Z {y | ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q}
        {y | ∃ q ∈ ℚlower R x, y = ↑q} inn nonem2 bdd1
      apply ISLUBsSup.left at aux1
      rw[<-eqq]
      linarith
    intro upp hupp
    have upp_gt_0 : 0 < upp
    · rw[upperBounds] at hupp
      simp at hupp
      obtain ⟨e, ee, he2, he3, he4⟩:= nonem2
      have saver1 := he3
      have saver2 := he4
      apply hupp at he2
      apply he2 at he3
      apply he3 at he4
      rw[saver1] at he4
      have ineq : 0 < (↑ee : Z) := by norm_cast
      linarith
    have upp_uppbdd : upp ∈ upperBounds {y | ∃ q ∈ ℚlower R x, y = ↑q }:= by
      rw[upperBounds]
      simp
      intro r  b ha1 ha3
      by_cases hr : r ≤ 0
      · rw[ℚlower] at ha1
        simp at ha1
        rw[ha3] at hr
        rw[ha3]
        linarith
      · push_neg at hr
        have : r ∈ {y : Z| ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q}:= by
          simp
          use b
          constructor
          · exact ha1
          · constructor
            · exact ha3
            · rw[ha3] at hr
              norm_cast at hr
        rw[upperBounds] at hupp
        apply hupp at this
        exact this
    have := ISLUBsSup.right
    apply this at upp_uppbdd
    rw[φ, <- eqq]
    exact upp_uppbdd
  rw[φ, <- eqq] at ISLUB0srz
  rw[φ, <- eqq]
  have ISLUB0sSup := sSup_axiom {y : Z| ∃ q ∈ ℚlower R x, y = ↑q ∧ 0 < q} nonem2 bdd
  exact IsLUB.unique ISLUB0sSup ISLUB0srz

lemma φminusx_eq_minusφx {R Z : Type} [RealField R]
    [RealField Z] {x : R} : φ R Z (-x) = - (φ R Z x):= by
  have zero_to_zero := zero_to_zero R Z
  have cero_eq_cero1 : (0 : R)= x - x := by linarith
  have cero_eq_cero2 : (0 : Z) = φ R Z x - φ R Z x:= by linarith
  rw[cero_eq_cero1] at zero_to_zero
  have aux : x - x = x + (-x) := by linarith
  rw[aux] at zero_to_zero
  rw[φ_preserves_add R Z x (-x)] at zero_to_zero
  rw[cero_eq_cero2] at zero_to_zero
  linarith

lemma φ_preserves_mul_x_y_pos (R Z : Type) [RealField R] [RealField Z] (x y : R) :(0<x) → (0<y) →
  φ R Z (x * y) = φ R Z x * φ R Z y := by
  intro hx hy
  have mul_gt_0 : 0 < x*y := by exact mul_pos hx hy
  have aux1 := Qlower_determines_Qlowergt0 hx hy
  have cero_lt_φxy : 0 < φ R Z (x*y)
  · rw[<- zero_to_zero R Z]
    exact (φ_preserves_order R Z 0 (x*y)).mp mul_gt_0
  have cero_lt_φx : 0 < (φ R Z x)
  · rw[<- zero_to_zero R Z]
    exact (φ_preserves_order R Z 0 (x)).mp hx
  have cero_lt_φy : 0 < (φ R Z y)
  · rw[<- zero_to_zero R Z]
    exact (φ_preserves_order R Z 0 y).mp hy
  have cero_lt_φxφy : 0 < φ R Z x * φ R Z y
  · exact mul_pos cero_lt_φx cero_lt_φy
  have aux2 := Qlowergt0_determines_Qlower
    (φ R Z (x*y)) ( φ R Z x * φ R Z y) cero_lt_φxy cero_lt_φxφy
  rw[x_eq_y_iff_QlowerRx_eq_QlowerRy]
  apply aux2
  have Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_1 := Qlower_gt0Rx_eq_Qlower_gt0ZφRZx R Z (x*y) mul_gt_0
  have Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_2 := Qlower_gt0Rx_eq_Qlower_gt0ZφRZx   R Z x hx
  have Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_3 := Qlower_gt0Rx_eq_Qlower_gt0ZφRZx  R Z y hy
  have cero_lt_sup1 : 0 < sSup {y : Z| ∃ q ∈ ℚlower_gt0 R x, y = ↑q}:= by
    rw[supZ_Qlower_gt0Rx_eq_φRZx]; exact cero_lt_φx; exact hx
  have cero_lt_sup2 : 0 < sSup {z : Z| ∃ q ∈ ℚlower_gt0 R y, z = ↑q}:= by
    rw[supZ_Qlower_gt0Rx_eq_φRZx]; exact cero_lt_φy; exact hy
  have preserved1:= Qlower_gt0_preserves_mulset hx hy
  have preserved2:= Qlower_gt0_preserves_mulset cero_lt_sup1 cero_lt_sup2
  rw[<-Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_1 ]
  rw[<- supZ_Qlower_gt0Rx_eq_φRZx R Z, <- supZ_Qlower_gt0Rx_eq_φRZx R Z]
  rw[<- preserved1 ,<- preserved2]
  rw[supZ_Qlower_gt0Rx_eq_φRZx , supZ_Qlower_gt0Rx_eq_φRZx]
  rw[Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_2, Qlower_gt0Rx_eq_Qlower_gt0ZφRZx_3]
  · exact hy
  · exact hx
  · exact hy
  · exact hx

lemma mSRZmx_eq_SRZx (R Z : Type)
 [RealField R] [RealField Z] (x : R) : φ R Z x = -φ R Z (-x) := by
  rw[φminusx_eq_minusφx]; simp

lemma φ_preserves_mul_x_y_neg (R Z : Type) [RealField R] [RealField Z] (x y : R) :(x<0) → (y<0) →
  φ R Z (x * y) = φ R Z x * φ R Z y := by

  intro hx hy
  have mx_pos  : 0 < -x := by linarith
  have my_pos  : 0 < -y := by linarith
  have prod_pos: x*y = (-x)*(-y) := by field_simp
  have mSRZmx_eq_SRZ_x : φ R Z x = -φ R Z (-x)
  · exact mSRZmx_eq_SRZx R Z x
  have mSRZmy_eq_SRZ_y : φ R Z y = -φ R Z (-y)
  · exact mSRZmx_eq_SRZx R Z y

  rw[prod_pos]
  rw[mSRZmx_eq_SRZ_x, mSRZmy_eq_SRZ_y]
  rw[φ_preserves_mul_x_y_pos R Z (-x) (-y) mx_pos my_pos]
  simp

lemma φ_preserves_mul_diff_sign (R Z : Type)
  [RealField R] [RealField Z] (x y : R) : (x < 0 ∧ 0 < y) ∨ (0 < x ∧ y < 0) →
  φ R Z (x * y) = φ R Z x * φ R Z y := by
  intro or
  cases' or with h1 h2
  · obtain ⟨hx, hy⟩ := h1
    have hx' : 0 < -x := by linarith
    have aux :  φ R Z (x * y) = - φ R Z (-(x * y))
    · exact mSRZmx_eq_SRZx R Z (x*y)
    have aux1 : -(x*y) = (-x)*y := by linarith
    rw[aux1] at aux
    rw[φ_preserves_mul_x_y_pos R Z (-x) y hx' hy] at aux
    rw[mSRZmx_eq_SRZx R Z x]
    simp at *
    exact aux
  · obtain ⟨hx, hy⟩ := h2
    have hy' : 0 < -y := by linarith
    have aux :  φ R Z (x * y) = - φ R Z (-(x * y))
    · exact mSRZmx_eq_SRZx R Z (x*y)
    have aux1 : -(x*y) = x*(-y) := by linarith
    rw[aux1] at aux
    rw[φ_preserves_mul_x_y_pos R Z x (-y) hx hy'] at aux
    rw[mSRZmx_eq_SRZx R Z y]
    simp at *
    exact aux

theorem φ_preserves_mul (R Z : Type)
  [RealField R] [RealField Z] (x y : R) : φ R Z (x * y) = φ R Z x * φ R Z y := by
  by_cases hxlt :  x < 0
  · by_cases hylt : y < 0

    · exact φ_preserves_mul_x_y_neg R Z x y hxlt hylt
    · by_cases hyeq : y = 0
      · rw[hyeq]; simp; rw[zero_to_zero]; simp
      · push_neg at *
        have hygt : 0<y := by exact lt_of_le_of_ne' hylt hyeq
        have or : (x < 0 ∧ 0 < y) ∨ (0<x ∧ y < 0)
        · left
          constructor
          · exact hxlt
          · exact hygt
        exact φ_preserves_mul_diff_sign R Z x y or
  by_cases hxeq : x=0
  · rw[hxeq]; simp; rw[zero_to_zero]; simp
  push_neg at *
  have hxgt : 0<x := by exact lt_of_le_of_ne' hxlt hxeq
  by_cases hylt : y < 0
  · have or : (x < 0 ∧ 0 < y) ∨ (0<x ∧ y < 0)
    · right
      constructor
      · exact hxgt
      · exact hylt
    exact φ_preserves_mul_diff_sign R Z x y or
  · push_neg at hylt
    by_cases hyeq : y=0
    · rw[hyeq]; simp; rw[zero_to_zero]; simp
    · have hygt : 0<y
      · push_neg at hyeq
        exact lt_of_le_of_ne' hylt hyeq
      exact φ_preserves_mul_x_y_pos R Z x y hxgt hygt

theorem a2_eq_a_a_neq_0_a_eq_one
  (R : Type) [RealField R] (x : R) : (x ≠ 0)∧ x*x = x ↔  x = 1 := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := h
    field_simp at h1
    exact h1
  · intro h1
    constructor
    · linarith
    · rw[h1]; simp

theorem one_to_one (R Z : Type) [RealField R] [RealField Z] : φ R Z 1 = 1:= by
    have one_eq : (1 : R) = 1*1 := by linarith
    have srz_eq1 : φ R Z 1 =  φ R Z (1*1) := by nth_rewrite 1 [one_eq]; rfl
    have srz_eq2 : φ R Z 1 = φ R Z 1 * φ R Z 1  := by
      rw[ φ_preserves_mul R Z 1 1] at srz_eq1
      exact srz_eq1
    have neq_0 : φ R Z 1 ≠ 0
    · by_contra hc
      have cero_eq_SRZ0:= zero_to_zero R Z
      rw[<- cero_eq_SRZ0] at hc
      apply (φ_is_bijective R Z).left at hc
      linarith
    obtain ⟨aux, eq⟩:= a2_eq_a_a_neq_0_a_eq_one Z (φ R Z 1)
    apply aux
    constructor
    · exact neq_0
    · symm; exact srz_eq2
--Teorema que unifica todo
theorem Real_fields_are_isomorphic (X Y : Type) [RealField X] [RealField Y] :
  ∃ f : X → Y,
    Function.Bijective f ∧
    (∀ x y, f (x + y) = f x + f y) ∧
    (∀ x y, f (x * y) = f x * f y) ∧
    (∀ x y, x < y ↔ f x < f y)
    ∧ ((f 0 =0 ) ∧  (f 1 = 1)) := by

  use φ X Y
  constructor
  · exact  φ_is_bijective X Y
  · constructor
    · exact φ_preserves_add X Y
    · constructor
      · exact φ_preserves_mul X Y
      · constructor
        · exact φ_preserves_order X Y
        · constructor
          · exact zero_to_zero X Y
          · exact one_to_one X Y
