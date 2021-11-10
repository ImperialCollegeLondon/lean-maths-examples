-- we want to use tactics
import tactic
-- we want to use the real numbers
import data.real.basic

/-

# Limits of sequences in Lean

We give the standard `ε`, `N` definition of the limit of a sequence
and prove some theorems about them. The boss level: limit of
products is product of limits.

-/

/-

## lambda (λ) notation for functions

Here's how we define the functions from the naturals to the naturals
sending n to n^2 + 3:

-/

def f : ℕ → ℝ := λ n, n^2+3

/-

Mathematicians might write `n ↦ n^2+3` for this functions; indeed `λ` is
just prefix notation for the infix notation `↦` (i.e. you write it at the
front, not in the middle).

The reason we need to know about function notation for this sheet
is that a sequence `x₀, x₁, x₂, …` of reals on this sheet will
be encoded as a function `f : ℕ → ℝ` sending `0` to `x₀`, `1` to `x₁`
and so on.
 
## Limit of a sequence.

Here's the definition of the limit of a sequence.
-/

/-- If `a(n)` is a sequence of reals and `t` is a real, `tendsto a t`
is the assertion that the limit of `a(n)` as `n → ∞` is `t`. -/
def tendsto (a : ℕ → ℝ) (t : ℝ) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε

-- the basic API for `tendsto`

/-- If your goal is `tendsto a t` and you want to replace it with
`∀ ε > 0, ∃ B, …` then you can do this with `rw tendsto_def`. -/
theorem tendsto_def {a : ℕ → ℝ} {t : ℝ} :
  tendsto a t ↔ ∀ ε, 0 < ε → ∃ B : ℕ, ∀ n, B ≤ n → |a n - t| < ε :=
begin
  -- true by definition
  refl
end

/-

## The questions

Here are some basic results about limits of sequences.
See if you can fill in the `sorry`s with Lean proofs.
The HINTS.md file in this directory contains some mathematical
sketch proofs and some hints about which tactics might be helpful
in this situation.

-/

/-- The limit of the constant sequence with value 37 is 37. -/
theorem tendsto_thirtyseven (c : ℝ) : tendsto (λ n, 37) 37 :=
begin
  rw tendsto_def, -- you can just comment this out and the pf still works
  intros ε hε,
  use 1234567, -- any natural will do, but we have to choose one
  intros n hn,
  simp, -- because the goal mentions `|37 - 37|` which can
  -- be solved by "simplifying rewrites" like `c - c = 0`
  exact hε, -- you can combine the last two tactics with `simp [hε]`
end

/-- The limit of the constant sequence with value `c` is `c`. -/
theorem tendsto_const (c : ℝ) : tendsto (λ n, c) c :=
begin
  rw tendsto_def,
  intros ε hε,
  use 42,
  intros, -- something I promise I will never use just got a weird name
  -- because I couldn't be bothered to name it 
  simp [hε],
end

/-- If `a(n)` tends to `t` then `a(n) + c` tends to `t + c` -/
theorem tendsto_add_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ)
  (h : tendsto a t) :
  tendsto (λ n, a n + c) (t + c) :=
begin
  rw tendsto_def at *,
  intros ε hε,
  specialize h ε hε,
  cases h with B hB,
  use B,
  intros n hn,
  specialize hB n hn,
  convert hB using 2, -- could have done `convert hB n hn using 2` and saved a line,
  ring,
end

-- alternative proof
theorem tendsto_add_const' {a : ℕ → ℝ} {t : ℝ} (c : ℝ)
  (h : tendsto a t) :
  tendsto (λ n, a n + c) (t + c) :=
begin
  rw tendsto_def at *,
  simpa using h, -- if you have a hypothesis `h` and
  -- a goal `⊢ P`, and if after running the simplifier on
  -- both `h` and `P` the terms become definitionally equal,
  -- then `simpa using h` closes the goal. Try `simp *`
  -- before the `simpa` to see what happens. `simp, assumption`
  -- also closes the goal.
end

/-- If `a(n)` tends to `t` then `-a(n)` tends to `-t`.  -/
theorem tendsto_neg {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  rw tendsto_def at *,
  simp [abs_sub_comm] at *,
  exact ha,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then `a(n) + b(n)`
tends to `t + u`. -/
theorem tendsto_add {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n + b n) (t + u) :=
begin
  unfold tendsto,
  intros ε hε,
  specialize ha (ε/2) (by linarith),
  specialize hb (ε/2) (by linarith),
  cases ha with B₁ hB₁,
  cases hb with B₂ hB₂,
  use max B₁ B₂,
  intros n hn,
  rw max_le_iff at hn,
  cases hn with hn₁ hn₂,
  specialize hB₁ n hn₁,
  specialize hB₂ n hn₂,
  rw abs_lt at *,
  cases hB₁,
  cases hB₂,
  split,
  linarith,
  linarith,
end

/-- If `a(n)` tends to t and `b(n)` tends to `u` then `a(n) - b(n)`
tends to `t - u`. -/
theorem tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (ha : tendsto a t) (hb : tendsto b u) :
  tendsto (λ n, a n - b n) (t - u) :=
begin
  exact tendsto_add ha (tendsto_neg hb),
end

/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsto_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tendsto a t) :
  tendsto (λ n, 37 * a n) (37 * t) :=
begin
  unfold tendsto at *,
  intros ε hε,
  specialize h (ε/37) (by linarith),
  cases h with B hB,
  use B,
  intros n hn,
  specialize hB n hn,
  rw [← mul_sub, abs_mul, abs_of_nonneg],
  linarith, norm_num,
end

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : 0 < c) : tendsto (λ n, c * a n) (c * t) :=
begin
  unfold tendsto at *,
  intros ε hε,
  specialize h (ε/c) (div_pos hε hc),
  cases h with B hB,
  use B,
  intros n hn,
  specialize hB n hn,
  rw [← mul_sub, abs_mul, abs_of_nonneg],
  exact (lt_div_iff' hc).mp hB,
  linarith,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : c < 0) : tendsto (λ n, c * a n) (c * t) :=
begin
  have hc' : 0 < -c,
    exact neg_pos.mpr hc,
  intros ε hε,
  specialize h ((ε/(-c))) _,
  exact div_pos hε hc',
  cases h with B hB,
  use B,
  intros n hn,
  specialize hB n hn,
  simp,
  rw [← mul_sub, abs_mul, abs_of_neg hc],
  exact (lt_div_iff' hc').mp hB,
end

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsto_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, c * a n) (c * t) :=
begin
  rcases lt_trichotomy 0 c with (hc | rfl | hc),
  { apply tendsto_pos_const_mul h hc },
  { convert tendsto_const 0,
      ext,
      simp,
    simp },
  { apply tendsto_neg_const_mul h hc },
end

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsto_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, a n * c) (t * c) :=
begin
--  rw mul_comm,
  simp_rw mul_comm,
  rw mul_comm t,
  exact tendsto_const_mul c h,
end

-- another proof of this
theorem tendsto_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  convert tendsto_const_mul (-1) ha,
  ext,
  simp,
  simp,
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsto_of_tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tendsto (λ n, a n - b n) t) (h2 : tendsto b u) :
  tendsto a (t+u) :=
begin
  convert tendsto_add h1 h2,
  ext,simp,
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsto_sub_lim {a : ℕ → ℝ} {t : ℝ}
  (h : tendsto a t) : tendsto (λ n, a n - t) 0 :=
begin
  convert tendsto_add_const (-t) h,
  simp,
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsto_zero_mul_tendsto_zero
  {a b : ℕ → ℝ} (ha : tendsto a 0) (hb : tendsto b 0) :
  tendsto (λ n, a n * b n) 0 :=
begin
  intros ε hε,
  specialize ha ε hε,
  specialize hb 1 (by linarith),
  cases ha with Ba hBa,
  cases hb with Bb hBb,
  use (max Ba Bb),
  intros n hn,
  rw max_le_iff at hn,
  cases hn with ha hb,
  specialize hBa n ha,
  specialize hBb n hb,
  simp at *,
  rw abs_mul,
  have h0 : 0 ≤ |a n| := abs_nonneg (a n),
  have h1 : 0 ≤ |b n| := abs_nonneg (b n),
  nlinarith,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsto_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tendsto a t)
  (hb : tendsto b u) : tendsto (λ n, a n * b n) (t * u) :=
begin
  have h1 : tendsto (λ n, a n - t) 0 := tendsto_sub_lim ha,
  have h2 : tendsto (λ n, b n - u) 0 := tendsto_sub_lim hb,
  have h3 := tendsto_zero_mul_tendsto_zero h1 h2,
  clear h1 h2,
  simp [sub_mul, mul_sub] at h3,
  replace ha := tendsto_mul_const u ha,
  replace ha := tendsto_sub_lim ha,
  simp at ha,
  replace hb := tendsto_const_mul t hb,
  have h6 := tendsto_of_tendsto_sub h3 ha,
  clear h3 ha,
  simp at h6,
  have h8 := tendsto_of_tendsto_sub h6 hb,
  simp at h8,
  exact h8,
end