# Hints for the limits of sequences example

## Tactics used in the model answers

The usual ones in the natural number game (intro, exact, cases, split, rw etc)

`simp`, the tactic which does simplifying rewrites (like changing `x * 1` into `x` and `x * 0` into `0`)

`linarith` and `nlinarith`, tactics for solving linear and nonlinear inequalities.

`convert` comes in handy a couple of times. If `h` and the goal are nearly but not quite definitionally equal,
then `convert h` will spit out goals for where they differ.

The `wlog` tactic is helpful for the final level.

## Library theorems used in the model answers

It helps if you know the basic API for `abs`, a.k.a. `|x|`. Here are some examples.

`abs_mul (a b : ℝ), |a * b| = |a| * |b|`
`abs_of_nonneg : 0 ≤ a → |a| = a`
`abs_of_neg : a < 0 → |a| = -a`

You can use the `rw` or `simp_rw` tactics to rewrite theorems about `abs`.

I used `lt_trichotomy (a b : ℝ) : a < b ∨ a = b ∨ b < a` at some point.

## Maths hints for the later questions

For `tendsto_add` use `ε/2`.

It seems to me that `tendsto_const_mul`, the theorem that if `aₙ → l` then `c*aₙ → c*l`,
needs to deal with the case c=0 separately. I elect to prove the positive and negative cases 
separately as well; one can of course try a unified approach but the case split has to come at some point.

There shouldn't be any epsilons or B's in proofs like `tendsto_of_tendsto_sub` : the idea
is that you have set up the API now and these proofs should just use that. 

For `tendsto_zero_mul_tendsto_zero` you can let one of the `ε`s be 1.

For `tendsto_mul` the maths proof I formalised went via proving that `λ n, (a n - t) * (b n - u)`
tended to zero first.

For `tendto_unique` you need the killer epsilon for the contradiction. 



