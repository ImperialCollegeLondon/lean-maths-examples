# Hints for the limits of sequences example

## Tactics used in the model answers

The usual ones in the natural number game (intro, exact, cases, split, rw etc)

`simp`, the tactic which does simplifying rewrites (like changing `x * 1` into `x` and `x * 0` into `0`)

`linarith` and `nlinarith`, tactics for solving linear and nonlinear inequalities.

## Library theorems used in the model answers

It helps if you know the basic API for `abs`, a.k.a. `|x|`. Here are some examples.

`abs_mul (a b : ℝ), |a * b| = |a| * |b|`
`abs_of_nonneg : 0 ≤ a → |a| = a`
`abs_of_neg : a < 0 → |a| = -a`

You can use the `rw` or `simp_rw` tactics to rewrite theorems about `abs`.

## Maths hints

