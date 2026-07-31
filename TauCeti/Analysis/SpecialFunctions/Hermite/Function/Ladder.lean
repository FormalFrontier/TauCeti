/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Basic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Ladder relations for the Hermite functions

This file adds the **A2 ladder relations** of the `OrthogonalL2Bases` roadmap to the Hermite
function object API (`TauCeti.hermiteFunction`,
`ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)`).

The two relations expose how the position operator `x·` and the derivative `d/dx` shift the Hermite
index:

* `TauCeti.mul_hermiteFunction` — `x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}`;
* `TauCeti.hasDerivAt_hermiteFunction` (and its `deriv` form `TauCeti.deriv_hermiteFunction`) —
  `ψₙ' = √(n/2)·ψ_{n-1} - √((n+1)/2)·ψ_{n+1}`.

Adding and subtracting them yields the annihilation/creation identities for the ladder operators
`a = (x + d/dx)/√2` and `a† = (x - d/dx)/√2`:

* `TauCeti.mul_add_deriv_hermiteFunction` — `x·ψₙ + ψₙ' = √(2n)·ψ_{n-1}` (the annihilation
  identity, `a ψₙ = √n ψ_{n-1}`);
* `TauCeti.mul_sub_deriv_hermiteFunction` — `x·ψₙ - ψₙ' = √(2(n+1))·ψ_{n+1}` (the creation
  identity, `a† ψₙ = √(n+1) ψ_{n+1}`).

All four relations are stated purely pointwise, with no integration involved. This is the level
at which the roadmap wants these identities stated, so that they elevate to the ladder operators
on `𝒮(ℝ)` / `L²(ℝ)` later without re-proof.

The `n = 0` boundary is covered by the `√(n/2) = 0` coefficient, which annihilates the (Nat-clamped)
`ψ_{n-1}` term, so the relations hold uniformly for all `n : ℕ`.
-/

public section

namespace TauCeti

open Polynomial

/-- The Hermite normalization `√(n!·√π)` at successor index: `√((n+1)!·√π) = √(n+1)·√(n!·√π)`. -/
private lemma normFactor_succ (n : ℕ) :
    Real.sqrt (((n + 1).factorial : ℝ) * Real.sqrt Real.pi)
      = Real.sqrt (n + 1) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- `√4 = 2`, used to split the square factor out of `√(2k)`. -/
private lemma sqrt_four : Real.sqrt 4 = 2 := by
  calc
    Real.sqrt 4 = Real.sqrt (2 ^ 2 : ℝ) := by norm_num
    _ = 2 := Real.sqrt_sq (by norm_num)

/-- `2·√(k/2) = √(2k)`: the coefficient identity behind the ladder-operator normalizations.
Regroup `2·k = 4·(k/2)` so the square factor `√4 = 2` splits off `√(k/2)`. -/
private lemma two_mul_sqrt_half (k : ℝ) : 2 * Real.sqrt (k / 2) = Real.sqrt (2 * k) :=
  calc 2 * Real.sqrt (k / 2)
      = Real.sqrt 4 * Real.sqrt (k / 2) := by rw [sqrt_four]
    _ = Real.sqrt (4 * (k / 2)) := (Real.sqrt_mul (by norm_num) _).symm
    _ = Real.sqrt (2 * k) := by congr 1; ring

/-- `√(1/2)·√2 = 1`: the coefficient collapsing the `n = 0` boundary of the ladder relations, where
the `√((n+1)/2) = √(1/2)` prefactor meets the `√2` from the `x√2` argument of `H₀`. -/
private lemma sqrt_half_mul_sqrt_two : Real.sqrt (1 / 2) * Real.sqrt 2 = 1 := by
  calc
    Real.sqrt (1 / 2) * Real.sqrt 2 = Real.sqrt ((1 : ℝ) / 2 * 2) :=
      (Real.sqrt_mul (by norm_num) _).symm
    _ = Real.sqrt 1 := by norm_num
    _ = 1 := Real.sqrt_one

/-- The Gaussian-weighted derivative factor produces the lower Hermite mode:
`H'ₙ(x√2)·√2·e^{-x²/2} / √(n!√π) = √(2n)·ψ_{n-1}(x)`. This isolates the normalization bookkeeping
that the derivative ladder relation shares with nothing else: it turns the `d/dx` of the polynomial
part into a clean multiple of `ψ_{n-1}`, so `hasDerivAt_hermiteFunction` reduces to
`mul_hermiteFunction` by pure algebra. At `n = 0` both sides vanish. -/
private lemma sqrt_two_mul_aeval_derivative_hermite (n : ℕ) (x : ℝ) :
    aeval (x * Real.sqrt 2) (derivative (hermite n)) * Real.sqrt 2 * Real.exp (-(x ^ 2 / 2))
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
      = Real.sqrt (2 * (n : ℝ)) * hermiteFunction (n - 1) x := by
  rw [Polynomial.derivative_hermite, map_nsmul, nsmul_eq_mul]
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel]
    rw [hermiteFunction_def, normFactor_succ]
    set e := Real.exp (-((x : ℝ) ^ 2 / 2)) with he
    set N := Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) with hN
    have hN0 : N ≠ 0 := (sqrt_factorial_mul_sqrt_pi_pos m).ne'
    have hsm1 : Real.sqrt ((m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsq : Real.sqrt ((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1) = (m : ℝ) + 1 :=
      Real.mul_self_sqrt (by positivity)
    have hmul2 : Real.sqrt (2 * ((m : ℝ) + 1)) = Real.sqrt 2 * Real.sqrt ((m : ℝ) + 1) :=
      Real.sqrt_mul (by norm_num) _
    push_cast
    rw [hmul2]
    field_simp
    linear_combination (-(e * aeval (x * Real.sqrt 2) (hermite m))) * hsq

/-- **Target A2 (position ladder relation).** Multiplying `ψₙ` by `x` mixes the neighbouring modes:
`x·ψₙ = √((n+1)/2)·ψ_{n+1} + √(n/2)·ψ_{n-1}`. -/
@[grind =]
theorem mul_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x =
      Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x
        + Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x := by
  rcases n with _ | m
  · -- `n = 0`: the `√(n/2)` term drops out and the prefactor `√(1/2)·√2` collapses to `1`
    simp only [Nat.cast_zero, zero_add, Nat.zero_sub, hermiteFunction_one, zero_div,
      Real.sqrt_zero, zero_mul, add_zero]
    linear_combination (-(x * hermiteFunction 0 x)) * sqrt_half_mul_sqrt_two
  · -- successor case: reduce to the recurrence `√2·x·Hₘ₊₁ = Hₘ₊₂ + (m+1)·Hₘ`
    -- the `aeval (x√2)` image of the three-term recurrence `Polynomial.hermite_add_two`
    -- (`H_{m+2} = X·H_{m+1} - (m+1)·Hₘ`), rearranged to isolate the `(x√2)·H_{m+1}` term
    have hrec : (x * Real.sqrt 2) * aeval (x * Real.sqrt 2) (hermite (m + 1)) =
        aeval (x * Real.sqrt 2) (hermite (m + 1 + 1))
          + ((m : ℝ) + 1) * aeval (x * Real.sqrt 2) (hermite m) := by
      have h := congrArg (aeval (x * Real.sqrt 2)) (hermite_add_two m)
      rw [map_sub, map_mul, map_nsmul, aeval_X, nsmul_eq_mul] at h
      push_cast at h
      linear_combination -h
    simp only [Nat.add_sub_cancel]
    rw [hermiteFunction_def, hermiteFunction_def, hermiteFunction_def,
      Real.sqrt_div (by positivity), Real.sqrt_div (by positivity)]
    simp only [normFactor_succ]
    set e := Real.exp (-((x : ℝ) ^ 2 / 2)) with he
    set N := Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) with hN
    have hN0 : N ≠ 0 := (sqrt_factorial_mul_sqrt_pi_pos m).ne'
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsm1 : Real.sqrt ((m : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsm2 : Real.sqrt ((m : ℝ) + 1 + 1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have hsq : Real.sqrt (1 + (m : ℝ)) * Real.sqrt (1 + (m : ℝ)) = 1 + (m : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    field_simp
    ring_nf
    ring_nf at hrec
    push_cast
    linear_combination e * hrec - e * aeval (x * Real.sqrt 2) (hermite m) * hsq

/-- **Target A2 (derivative ladder relation).** Differentiating `ψₙ` mixes the neighbouring modes:
`ψₙ' = √(n/2)·ψ_{n-1} - √((n+1)/2)·ψ_{n+1}`. -/
theorem hasDerivAt_hermiteFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteFunction n)
      (Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
        - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x) x := by
  have hP : HasDerivAt (fun x : ℝ => aeval (x * Real.sqrt 2) (hermite n))
      (aeval (x * Real.sqrt 2) (derivative (hermite n)) * Real.sqrt 2) x := by
    have h := (Polynomial.hasDerivAt_aeval (hermite n) (x * Real.sqrt 2)).comp x
      ((hasDerivAt_id x).mul_const (Real.sqrt 2))
    simpa only [Function.comp_def, one_mul, id_eq] using h
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2 / 2)))
      (-x * Real.exp (-(x ^ 2 / 2))) x := by
    have hx2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
      simpa using (hasDerivAt_pow 2 x).div_const 2
    simpa [mul_comm] using hx2.neg.exp
  -- The derivative value from the product rule is `√2·H'ₙ(x√2)·e/N - x·ψₙ`. The first term is the
  -- lower mode `√(2n)·ψ_{n-1}` (`sqrt_two_mul_aeval_derivative_hermite`) and `x·ψₙ` is the position
  -- relation (`mul_hermiteFunction`), so the whole collapses to the claimed combination by algebra,
  -- using `√(2n) = 2·√(n/2)` (`two_mul_sqrt_half`).
  have key :
      (aeval (x * Real.sqrt 2) (derivative (hermite n)) * Real.sqrt 2 * Real.exp (-(x ^ 2 / 2))
          + aeval (x * Real.sqrt 2) (hermite n) * (-x * Real.exp (-(x ^ 2 / 2))))
          / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
        = Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
          - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x := by
    have henv := sqrt_two_mul_aeval_derivative_hermite n x
    have hψ := hermiteFunction_def n x
    have h2 := two_mul_sqrt_half (n : ℝ)
    linear_combination henv + x * hψ - mul_hermiteFunction n x - hermiteFunction (n - 1) x * h2
  have hfun : hermiteFunction n
      = fun x => aeval (x * Real.sqrt 2) (hermite n) * Real.exp (-(x ^ 2 / 2))
          / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
    funext y; exact hermiteFunction_def n y
  rw [hfun]
  exact key ▸ (hP.mul hE).div_const (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi))

/-- The `deriv` form of `hasDerivAt_hermiteFunction`. -/
@[simp, grind =]
theorem deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (hermiteFunction n) x =
      Real.sqrt ((n : ℝ) / 2) * hermiteFunction (n - 1) x
        - Real.sqrt (((n : ℝ) + 1) / 2) * hermiteFunction (n + 1) x :=
  (hasDerivAt_hermiteFunction n x).deriv

/-- **Annihilation identity.** The combination `x·ψₙ + ψₙ' = √(2n)·ψ_{n-1}`; this is the ladder
operator `a = (x + d/dx)/√2` acting as `a ψₙ = √n·ψ_{n-1}`. -/
@[grind =]
theorem mul_add_deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x + deriv (hermiteFunction n) x
      = Real.sqrt (2 * (n : ℝ)) * hermiteFunction (n - 1) x := by
  rw [mul_hermiteFunction, deriv_hermiteFunction, ← two_mul_sqrt_half (n : ℝ)]
  ring

/-- **Creation identity.** The combination `x·ψₙ - ψₙ' = √(2(n+1))·ψ_{n+1}`; this is the ladder
operator `a† = (x - d/dx)/√2` acting as `a† ψₙ = √(n+1)·ψ_{n+1}`. -/
@[grind =]
theorem mul_sub_deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    x * hermiteFunction n x - deriv (hermiteFunction n) x
      = Real.sqrt (2 * ((n : ℝ) + 1)) * hermiteFunction (n + 1) x := by
  rw [mul_hermiteFunction, deriv_hermiteFunction, ← two_mul_sqrt_half ((n : ℝ) + 1)]
  ring

end TauCeti
