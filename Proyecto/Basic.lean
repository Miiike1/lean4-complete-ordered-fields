





import Mathlib.Tactic -- import all the tactics


def f : ℕ → ℝ := fun n ↦ n ^ 2 + 3

/-

Mathematicians might write `n ↦ n^2+3` for this function. You can
read more about function types in the "three kinds of types" section
of Part B of the course book.

Sometimes you might find yourself with a lambda-defined function
evaluated at a number. For example, you might see something like
`(fun n => n^2 + 3) 37`, which means "take the function sending
`n` to `n^2+3` and then evaluate it at 37". You can use the `dsimp`
(or `dsimp only`) tactic to simplify this to `37^2+3`.

The reason we need to know about function notation for this sheet
is that a sequence `x₀, x₁, x₂, …` of reals on this sheet will
be encoded as a function from `ℕ` to `ℝ` sending `0` to `x₀`, `1` to `x₁`
and so on.

## Limit of a sequence.

Here's the definition of the limit of a sequence.
-/
/-- If `a(n)` is a sequence of reals and `t` is a real, `TendsTo a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def TendsTo (a : ℕ → ℝ) (t : ℝ) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

/-

We've made a definition, so it's our job to now make the API
for the definition, i.e. prove some basic theorems about it.

-/
-- If your goal is `TendsTo a t` and you want to replace it with
-- `∀ ε > 0, ∃ B, …` then you can do this with `rw tendsTo_def`.
theorem tendsTo_def {a : ℕ → ℝ} {t : ℝ} :
    TendsTo a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε := by
  rfl  -- true by definition

-- the eagle-eyed viewers amongst you might have spotted
-- that `∀ ε > 0, ...` and `∀ ε, ε > 0 → ...` and `∀ ε, 0 < ε → ...`
-- are all definitionally equal, so `rfl` sees through them.
/-

## The questions

Here are some basic results about limits of sequences.
See if you can fill in the `sorry`s with Lean proofs.
Note that `norm_num` can work with `|x|` if `x` is a numeral like 37,
but it can't do anything with it if it's a variable.
-/
/-- The limit of the constant sequence with value 37 is 37. -/
theorem tendsTo_thirtyseven : TendsTo (fun n ↦ 37) 37 :=
  by
  rw [ tendsTo_def]
  intro ε hε
  use 100
  intro n hn
  norm_num
  exact hε

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsTo_const (c : ℝ) : TendsTo (fun n ↦ c) c :=
  by
  rw[tendsTo_def]
  intro ε hε
  use 37
  intro n hn
  ring_nf
  norm_num
  exact hε

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsTo_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n => a n + c) (t + c) :=
  by
  rw [tendsTo_def] at h ⊢
  ring_nf
  exact h
  -- hints: make sure you know the maths proof!
  -- use `cases` to deconstruct an `exists`
  -- hypothesis, and `specialize` to specialize
  -- a `forall` hypothesis to specific values.
  -- Look up the explanations of these tactics in Part C
  -- of the course notes.  rw [tendsTo_def] at h ⊢


-- you're not quite ready for this one yet though.
/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
example {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n => -a n) (-t) := by
  rw[tendsTo_def] at ha
  ring_nf
  sorry
  done




/-

# Figuring out how to use the reals

## The `exact?` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `exact?` tactic tells you the names of all these lemmas.
See where it says "try this" -- click there and Lean will replace
`exact?` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.
However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `exact?` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |-x| = |x| := by exact abs_neg x
-- click where it says "try this" to replace
-- `exact?` with an "exact" proof
-- Why do this? Because it's quicker!
example (x y : ℝ) : |x - y| = |y - x| := by exact abs_sub_comm x y


-- Hmm. What would a theorem saying "the max is
-- less-or-equal to something iff something else
-- be called, according to Lean's naming conventions?"
example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by exact Nat.max_le

-- abs of something less than something...
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact abs_lt

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by linarith

-- or linarith, or guess the name...
example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by exact add_lt_add h1 h2

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by linarith

-- This is too obscure for the library
example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by linarith

-- note that add_lt_add doesn't work because
-- ((a+b)+c)+d and (a+c)+(b+d) are not definitionally equ


-- you can maybe do this one now
theorem tendsTo_neg {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  rw[tendsTo_def] at *
  ring_nf
  have h : ∀ n, |a n - t| = |-a n - -t| := by
    intro n
    rw[abs_sub_comm]
    ring_nf
  simpa [h]using ha
/-
`tendsTo_add` is the next challenge. In a few weeks' time I'll
maybe show you a two-line proof using filters, but right now
as you're still learning I think it's important that you
try and suffer and struggle through the first principles proof.
BIG piece of advice: write down a complete maths proof first,
with all the details there. Then, once you know the maths
proof, try translating it into Lean. Note that a bunch
of the results we proved in sheet 4 will be helpful.
-/
/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsTo_add {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n + b n) (t + u) :=
  by
  rw [tendsTo_def] at *
  -- let ε > 0 be arbitrary
  intro ε hε
  --  There's a bound X such that if n≥X then a(n) is within ε/2 of t
  specialize ha (ε / 2) (by linarith)
  cases' ha with X hX
  --  There's a bound Y such that if n≥Y then b(n) is within ε/2 of u
  specialize hb (ε /2) (by linarith)
  cases' hb with Y hy

  --  use max(X,Y),
  use max X Y
  -- now say n ≥ max(X,Y)
  intro n hn
  rw [max_le_iff] at hn
  specialize hX n hn.1
  specialize hy n hn.2
  --  Then easy.
  rw [abs_lt] at *
  constructor <;>-- `<;>` means "do next tactic to all goals produced by this tactic"
    linarith

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n - b n) (t - u) := by
  -- this one follows without too much trouble from earlier results.
  rw[tendsTo_def] at *
  intro ε hε
  specialize ha (ε/2) (by linarith)
  specialize hb (ε/2) (by linarith)
  cases' ha with X hx
  cases' hb with Y hy
  use max X Y
  intro n hn
  rw[max_le_iff] at hn
  specialize hx n hn.1
  specialize hy n hn.2
  rw[abs_lt] at *
  constructor <;>
    linarith



/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / 37) (by linarith)
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;>
  linarith
/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / c) (div_pos hε hc)
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact (lt_div_iff₀' hc).mp hX

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw[tendsTo_def] at *
  intro ε hε
  have hpos : 0 < |c| := abs_pos.mpr hc.ne
  obtain ⟨X, hX⟩ := h (ε / |c|) (div_pos hε hpos)
  use X
  intro n hn
  specialize hX n hn
  rw[<-mul_sub,abs_mul]
  rw[mul_comm]
  exact (lt_div_iff₀ hpos).mp hX

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  obtain hc |rfl| hc:= lt_trichotomy 0 c
  exact tendsTo_pos_const_mul h hc
  rw[tendsTo_def] at*
  intro ε hε
  use 1
  intro n hn
  ring_nf
  rw[abs_zero];exact hε
  exact tendsTo_neg_const_mul h hc
/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  simpa [mul_comm] using tendsTo_const_mul c h


-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
    simpa using tendsTo_add h1 h2


/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  · intro h
    simpa using tendsTo_sub h (tendsTo_const t)
  · intro h
    simpa using tendsTo_add h (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨X,hX⟩:=ha ε hε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  simpa [abs_mul] using mul_lt_mul'' hX hY


/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw[tendsTo_sub_lim_iff] at *
  have  h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by intro n; ring
  simp [h]
  rw [show (0 : ℝ) = 0 + t * 0 + 0 * u by simp]
  refine' tendsTo_add (tendsTo_add _ _) _
  · exact tendsTo_zero_mul_tendsTo_zero ha hb
  · exact tendsTo_const_mul t hb
  · exact tendsTo_mul_const u ha

-- something we never used!
/-- A sequence has at most one limit. -/
theorem eq_zero_of_abs_lt_eps {r : ℝ} (h : ∀ ε > 0, |r| < ε) : r = 0:=by
  by_contra hc
  specialize h (|r|) (abs_pos.mpr hc)
  norm_num at h


theorem tendsTo_unique' (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t :=by
  -- We know a - a tends to s - t because of `tendsTo_sub`
  have h := tendsTo_sub hs ht
  -- We want to prove s = t; by previous result suffices to
  -- show |t - s|<ε for all ε>0
  suffices ∀ ε > 0, |t - s| < ε by linarith [eq_zero_of_abs_lt_eps this]
  intro ε hε
  obtain ⟨X,hX⟩ :=h ε hε
  specialize hX X (by rfl)
  simpa using hX







-- Second proof
theorem tendsTo_uniquee (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t :=
  by
  by_contra h
  wlog h2 : s < t
  · cases' Ne.lt_or_lt h with h3 h3
    · contradiction

    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε : 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  specialize hX (max X Y) (le_max_left X Y)
  specialize hY (max X Y) (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith
