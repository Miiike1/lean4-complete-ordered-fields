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


theorem x_eq_y_iff_SℚRx_eq_SℚRy {R : Type} [RealField R] (x y : R) : x = y ↔ Sℚ R x = Sℚ R y := by
  constructor
  · intro heq
    rw[heq]
  · have inj := Sℚ_inj R
    rw[Function.Injective] at inj
    intro hinj
    exact inj hinj


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

-- tutoría, igual a demostrar que SRZ R R es la identidad, podría reescribirlo... (debería)
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

lemma coSℚRx_nonempt_in_Z (R Z : Type) [RealField R] [RealField Z] (x : R) :
  {(q : Z) | q ∈ Sℚ R x}.Nonempty := by

  have: {(q : Z) | q ∈ Sℚ R x} =  { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}:= by rfl
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

lemma coSℚRx_bdd_in_Z (R Z : Type) [RealField R] [RealField Z] (x : R) :
  BddAbove {(q : Z) | q ∈ Sℚ R x} := by
  have: {(q : Z) | q ∈ Sℚ R x} =  { y:Z | ∃ (q : ℚ), (↑q < (x : R)) ∧ (↑q : Z) = y}:= by rfl
  rw[this]; exact rats_lt_sup_rats_bddabv R Z x

--escribir teorema que demuestre que IsLUB set sup para acortar la demostración
--para el futuro


--TUTORÍA
-- qués es lo que falta? que un conjunto de reacionales (menores q x en un cuerpo arbitrario)
--si coincide con otro entonces determina el mismo elemento? creo que era eso... revisar
--creo que lo he utilizado para demostrar que la composición es la identidad,
--pero necesito formalizar el resultado

--revisar esto con el lema x_eq_y_iff_SℚRy=....



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
--tutoría



theorem compo (R Z : Type) [RealField R] [RealField Z] (x : R) :
 (SRZ Z R ∘ SRZ R Z) x= SRZ Z R (SRZ R Z x):=rfl

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

lemma Sℚ_x_addset_Sℚ_y_eq_Sℚ_x_add_y {R : Type} [RealField R] (x : R) (y : R) :
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
  rw[ Supx_is_idd2 R (x+y), Supx_is_idd2 R x, Supx_is_idd2 R y]

--quedó más largo de lo que querría, pero la manera que pensé funcionó
--añadir en la memoria que primero hice un código de 100 líneas para terminar dejándolo en 5

lemma SRZ_preserves_add (R Z : Type) [RealField R] [RealField Z] (x y : R) :
  SRZ R Z (x + y) = SRZ R Z x + SRZ R Z y := by

  rw[x_eq_y_iff_SℚRx_eq_SℚRy]
  rw[<- SℚRx_eq_SℚZSRZRZx]
  rw[<-Sℚ_x_addset_Sℚ_y_eq_Sℚ_x_add_y]
  rw[<-Sℚ_x_addset_Sℚ_y_eq_Sℚ_x_add_y]
  rw[<- SℚRx_eq_SℚZSRZRZx,<- SℚRx_eq_SℚZSRZRZx]

lemma zero_to_zero (R Z : Type) [RealField R] [RealField Z] : SRZ R Z 0 = 0:= by
    have zero_eq : (0 : R) = 0 + 0 := by linarith
    have srz_eq1 : SRZ R Z 0 =  SRZ R Z (0 + 0) := by nth_rewrite 1 [zero_eq]; rfl
    have srz_eq2 : SRZ R Z 0 = SRZ R Z 0 + SRZ R Z 0  := by
      rw[ SRZ_preserves_add R Z 0 0] at srz_eq1
      exact srz_eq1
    linarith

def mulset {R : Type} [Ring R] :
  (Set R) → (Set R) → (Set R) := fun  U V => {(x : R) | ∃ u ∈ U, ∃ v ∈ V, x = u * v }

lemma gtzero_Sℚx_mulset_gtzeroSℚy_eq_gtzeroSℚxy
{R : Type} [RealField R] (x : R) (y : R) (hx : 0 < x) (hy : 0 < y) :

  mulset { q : ℚ | q > 0 ∧ q ∈ Sℚ R x } { q : ℚ | q > 0 ∧ q ∈ Sℚ R y }
  = { q : ℚ | q > 0 ∧ q ∈ Sℚ R (x*y) } := by
  rw[Set.ext_iff]
  intro a
  constructor
  · rw[mulset]
    simp
    intro x1 hx11 hx12 x2 hx21 hx22 hax1x2
    constructor
    · rw[hax1x2]
      exact mul_pos hx11 hx21
    · rw[Sℚ] at *
      simp

      have hcox11: 0 < (↑ x1 : R)
      · norm_cast

      have hcox21: 0 < (↑ x2 : R)
      · norm_cast

      have eqq : (a : R) = (x1 : R) * (x2 : R)
      · rw [hax1x2]
        rw[Rat.cast_mul]

      rw[hax1x2,Rat.cast_mul]
      simp at hx22
      simp at hx12
      exact mul_lt_mul_of_pos hx12 hx22 hcox11 hy
  · simp
    rw[Sℚ, mulset]
    simp
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
        · rw[Sℚ]
          simp
          field_simp at *
          exact hp1
      field_simp
      norm_cast at ineq_5
      rw[div_self ]; linarith


lemma a_lt_b_Sℚa_in_Sℚb (R : Type) [RealField R] (a b : R) : a ≤ b ↔ Sℚ R a ⊆ Sℚ R b := by
  constructor
  · intro hab
    intro q
    intro hq
    rw[Sℚ] at *
    simp at *
    linarith
  · intro hab
    rw[Sℚ, Sℚ] at hab
    simp at hab
    by_contra hc
    push_neg at hc
    obtain ⟨q, hq1, hq2⟩ := Q_is_dense R b a hc
    specialize hab q
    have := hab hq2
    linarith

lemma A_in_B_supA_lt_supB (R : Type)[RealField R] (A B : Set R) :
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



lemma supZ_SℚRx_gt_0_eq_SRZRZx_x_gt_0
  (R Z : Type)[RealField R][RealField Z] (x : R ) : 0 < x →
   sSup { y : Z | ∃ q ∈ Sℚ R x, y = (q : Z) ∧ 0 < q}
  = SRZ R Z x := by
  intro hx

  obtain ⟨q,hq1,hq2⟩:= Q_is_dense R 0 x hx
  obtain ⟨k, hk1,hk2⟩:= Q_is_dense R x (x+1) x_lt_x_add_one
  have nonem1: {y : Z | ∃ q ∈ Sℚ R x, y = ↑q }.Nonempty
  · use q
    rw[Sℚ]
    simp
    exact hq2

  have nonem2: {y : Z | ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q}.Nonempty
  · use q
    simp
    constructor
    · exact hq2
    · norm_cast at hq1
  have bdd : BddAbove {y : Z | ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q}
  · rw[BddAbove]
    use k
    rw[upperBounds]
    simp
    intro a x1 hx1 ha hx2
    rw[Sℚ] at hx1
    simp at hx1
    rw[ha]
    have := lt_trans hx1 hk1
    norm_cast
    norm_cast at this
    linarith
  have bdd1 : BddAbove {y : Z | ∃ q ∈ Sℚ R x, y = ↑q}
  · obtain ⟨q, hq1, hq2⟩:= Q_is_dense R x (x+1) x_lt_x_add_one
    use q
    intro k hk
    rw[Sℚ] at hk
    simp at hk
    obtain ⟨nat, hnat1, hnat2⟩:= hk
    rw[hnat2]
    have := lt_trans hnat1 hq1
    norm_cast at this
    norm_cast
    linarith
  have eqq : {y : Z | ∃ q ∈ Sℚ R x, y = ↑q} = {y : Z | ∃ q ∈ Sℚ R x, ↑q = y} := by
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
  have inn: {y : Z | ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q}  ⊆   {y : Z | ∃ q ∈ Sℚ R x, y = ↑q } := by
    intro a ha
    obtain ⟨b, ha1, ha2, ha3⟩ := ha
    simp
    use b
  have ISLUBsSup := sSup_axiom {y : Z | ∃ q ∈ Sℚ R x, y = ↑q} nonem1 bdd1
  have ISLUB0srz : IsLUB {y : Z | ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q} (SRZ R Z x):= by
    constructor
    · intro a ha
      have aux1 : a ∈ {y | ∃ q ∈ Sℚ R x, y = ↑q} := by
        obtain ⟨k, ha1, ha2, ha3⟩:=ha
        simp
        use k
      rw[SRZ]
      have aux2 :=
        A_in_B_supA_lt_supB Z {y | ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q}
        {y | ∃ q ∈ Sℚ R x, y = ↑q} inn nonem2 bdd1
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
    have upp_uppbdd : upp ∈ upperBounds {y | ∃ q ∈ Sℚ R x, y = ↑q }:= by
      rw[upperBounds]
      simp
      intro r  b ha1 ha3
      by_cases hr : r ≤ 0
      · rw[Sℚ] at ha1
        simp at ha1
        rw[ha3] at hr
        rw[ha3]
        linarith
      · push_neg at hr
        have : r ∈ {y : Z| ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q}:= by
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
    rw[SRZ, <- eqq]
    exact upp_uppbdd
  rw[SRZ, <- eqq] at ISLUB0srz
  rw[SRZ, <- eqq]
  have ISLUB0sSup := sSup_axiom {y : Z| ∃ q ∈ Sℚ R x, y = ↑q ∧ 0 < q} nonem2 bdd
  exact IsLUB.unique ISLUB0sSup ISLUB0srz





























lemma SRZ_preserves_mul_x_y_pos (R Z : Type) [RealField R] [RealField Z] (x y : R) :(0<x) → (0<y) →
  SRZ R Z (x * y) = SRZ R Z x * SRZ R Z y := by
  intro hx hy




      -- (etc)



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
