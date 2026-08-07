/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Values of the probabilists' Hermite polynomials at zero

Mathlib's `Polynomial.hermite : ℕ → ℤ[X]` records `hermite 0 = C 1` and `hermite 1 = X` and
computes every coefficient (`Polynomial.coeff_hermite_explicit`, `Polynomial.coeff_hermite`), but
the special value `Hₙ(0)` is nowhere stated in closed form. This file supplies it: the odd values
vanish and the even values follow the alternating-sign double-factorial pattern

  `H_{2n+1}(0) = 0`,  `H_{2n}(0) = (-1)ⁿ · (2n-1)‼`.

These are the coefficients of the exponential generating function at `x = 0`, which reads

  `∑ Hₙ(0) · tⁿ / n! = exp (-t² / 2)`,

matching `TauCeti.hermite_generating_function` specialized at `x = 0`. Together with
`Polynomial.hermite_aeval_neg` (parity, in `Derivative.lean`) they complete the acceptance values
`H₀(0)=1, H₁(0)=0, H₂(0)=-1, H₃(0)=0, H₄(0)=3, …` of the `OrthogonalL2Bases` roadmap's Part A1.

The two-step recursion `H_{n+2}(0) = -(n+1) · Hₙ(0)`, an immediate consequence of the classical
three-term recurrence `Polynomial.hermite_add_two`, is stated as its own lemma: it is what the
double-factorial pattern encodes, and downstream users may reach for it directly (an induction on
the even index is often shorter than unwinding the closed form).

The base statements are given over `ℤ` (the natural output ring of `Polynomial.hermite`) and
lifted polymorphically to any commutative ring through `Polynomial.aeval` — the form the roadmap's
analytic consumers on `ℝ[X]` and `ℂ[X]` want, without a hand-rolled cast at every use site. The
`if Even n` conditional form mirrors Mathlib's `Polynomial.coeff_hermite`, and all lemmas are
stated in the `Polynomial` namespace as upstream candidates, next to `coeff_hermite_explicit`.
-/

public section

namespace TauCeti

open Polynomial
open scoped Nat

/-- **Vanishing at zero of the odd Hermite polynomials.** `H_{2n+1}(0) = 0`: the constant
coefficient of `hermite (2n+1)` is `0` because `(2n+1) + 0` is odd
(`Polynomial.coeff_hermite_of_odd_add`). Not a `simp` lemma: `Polynomial.hermite_succ` is `@[simp]`
in Mathlib and unfolds `hermite (2n+1)` on the left, so this LHS is not simp-normal. -/
theorem _root_.Polynomial.hermite_eval_zero_of_odd (n : ℕ) :
    eval (0 : ℤ) (hermite (2 * n + 1)) = 0 := by
  rw [← coeff_zero_eq_eval_zero]
  exact coeff_hermite_of_odd_add (by
    rw [Nat.add_zero]
    exact ⟨n, by ring⟩)

/-- **Closed form at zero of the even Hermite polynomials.** `H_{2n}(0) = (-1)ⁿ · (2n-1)‼`: read
off the `k = 0` case of `Polynomial.coeff_hermite_explicit` — the constant coefficient of
`hermite (2n)` is `(-1)ⁿ · (2n-1)‼ · C(2n, 0) = (-1)ⁿ · (2n-1)‼`. -/
theorem _root_.Polynomial.hermite_eval_zero_of_even (n : ℕ) :
    eval (0 : ℤ) (hermite (2 * n)) = (-1) ^ n * ((2 * n - 1)‼ : ℤ) := by
  rw [← coeff_zero_eq_eval_zero]
  have h := coeff_hermite_explicit n 0
  rw [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h
  exact h

/-- **The Hermite value at zero, combined form.** `Hₙ(0)` is `0` at odd indices and
`(-1)^(n/2) · (n-1)‼` at even indices; mirrors the `if Even (n + k)` shape of
`Polynomial.coeff_hermite`. -/
theorem _root_.Polynomial.hermite_eval_zero (n : ℕ) :
    eval (0 : ℤ) (hermite n) =
      if Even n then (-1) ^ (n / 2) * ((n - 1)‼ : ℤ) else 0 := by
  split_ifs with hn
  · obtain ⟨m, rfl⟩ := hn
    have hmm : m + m = 2 * m := (two_mul m).symm
    rw [hmm, hermite_eval_zero_of_even, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  · rw [Nat.not_even_iff_odd] at hn
    obtain ⟨m, rfl⟩ := hn
    exact hermite_eval_zero_of_odd m

/-- **Two-step recursion for the Hermite values at zero.** `H_{n+2}(0) = -(n+1) · Hₙ(0)`: evaluate
`Polynomial.hermite_add_two` at `x = 0`, killing the `X · hermite (n+1)` term. Combined with
`H_0(0) = 1` this generates the closed form. -/
theorem _root_.Polynomial.hermite_eval_zero_add_two (n : ℕ) :
    eval (0 : ℤ) (hermite (n + 2))
      = -((n : ℤ) + 1) * eval (0 : ℤ) (hermite n) := by
  rw [hermite_add_two, eval_sub, eval_mul, eval_X, zero_mul, zero_sub, eval_smul,
    nsmul_eq_mul]
  push_cast
  ring

/-- The odd Hermite polynomials vanish at zero, polymorphic form. Not a `simp` lemma for the same
reason as `Polynomial.hermite_eval_zero_of_odd`: `Polynomial.hermite_succ` unfolds `hermite (2n+1)`
on the left, so this LHS is not simp-normal. -/
theorem _root_.Polynomial.hermite_aeval_zero_of_odd {R : Type*} [CommRing R] (n : ℕ) :
    aeval (0 : R) (hermite (2 * n + 1)) = 0 := by
  rw [← coeff_zero_eq_aeval_zero', coeff_zero_eq_eval_zero, hermite_eval_zero_of_odd, map_zero]

/-- Closed form at zero of the even Hermite polynomials, polymorphic form. -/
theorem _root_.Polynomial.hermite_aeval_zero_of_even {R : Type*} [CommRing R] (n : ℕ) :
    aeval (0 : R) (hermite (2 * n)) = (-1) ^ n * ((2 * n - 1)‼ : R) := by
  rw [← coeff_zero_eq_aeval_zero', coeff_zero_eq_eval_zero, hermite_eval_zero_of_even]
  push_cast
  ring

/-- Combined form of the Hermite value at zero, polymorphic version. -/
theorem _root_.Polynomial.hermite_aeval_zero {R : Type*} [CommRing R] (n : ℕ) :
    aeval (0 : R) (hermite n) =
      if Even n then (-1) ^ (n / 2) * ((n - 1)‼ : R) else 0 := by
  rw [← coeff_zero_eq_aeval_zero', coeff_zero_eq_eval_zero, hermite_eval_zero]
  split_ifs
  · push_cast
    ring
  · exact map_zero _

/-- Two-step recursion for the Hermite values at zero, polymorphic form. -/
theorem _root_.Polynomial.hermite_aeval_zero_add_two {R : Type*} [CommRing R] (n : ℕ) :
    aeval (0 : R) (hermite (n + 2))
      = -((n : R) + 1) * aeval (0 : R) (hermite n) := by
  rw [← coeff_zero_eq_aeval_zero' (p := hermite (n + 2)),
    ← coeff_zero_eq_aeval_zero' (p := hermite n),
    coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero,
    hermite_eval_zero_add_two]
  push_cast
  ring

end TauCeti
