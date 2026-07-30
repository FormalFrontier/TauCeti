/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The harmonic-oscillator eigen-equation for the Hermite functions

This file adds the **A2 oscillator milestone** of the `OrthogonalL2Bases` roadmap: the Hermite
functions `ψₙ` (`TauCeti.hermiteFunction`, `ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)`) are the
eigenfunctions of the quantum harmonic oscillator,

`-ψₙ'' + x²·ψₙ = (2n+1)·ψₙ`.

The whole argument stays at the pointwise level and is built directly on the creation and
annihilation identities proved in `TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder`:

* `TauCeti.mul_sub_deriv_hermiteFunction` — `x·ψₙ - ψₙ' = √(2(n+1))·ψ_{n+1}` (creation);
* `TauCeti.mul_add_deriv_hermiteFunction` — `x·ψₙ + ψₙ' = √(2n)·ψ_{n-1}` (annihilation).

Writing `c = √(2(n+1))`, the creation identity gives `ψₙ' = x·ψₙ - c·ψ_{n+1}`, so differentiating
once more (product rule) and eliminating `ψ_{n+1}'` through the annihilation identity at index
`n+1` (`x·ψ_{n+1} + ψ_{n+1}' = c·ψₙ`, since `√(2(n+1))` is again `c`) collapses every neighbouring
mode, using only `c² = 2(n+1)`:

`ψₙ'' = ψₙ + x·ψₙ' - c·ψ_{n+1}' = x²·ψₙ - (2n+1)·ψₙ`.

The main results are the closed form of the second derivative,
`TauCeti.deriv_deriv_hermiteFunction` (`ψₙ'' = (x² - (2n+1))·ψₙ`), and the eigen-equation
`TauCeti.hermiteFunction_oscillator` in the roadmap's `-ψₙ'' + x²·ψₙ = (2n+1)·ψₙ` form.

No case split on `n` is needed: the neighbour that would require the Nat-clamped index `n-1` never
enters, because the derivation uses the creation identity at `n` and the annihilation identity at
`n+1`, whose lower index `(n+1)-1 = n` is exact.
-/

public section

namespace TauCeti

open Polynomial

/-- **Second derivative of the Hermite function** (the derivative form). The Hermite function `ψₙ`
solves `ψₙ'' = (x² - (2n+1))·ψₙ`; this states that the derivative of `ψₙ'` at `x` equals
`(x² - (2n+1))·ψₙ(x)`. -/
theorem hasDerivAt_deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    HasDerivAt (deriv (hermiteFunction n))
      ((x ^ 2 - (2 * n + 1)) * hermiteFunction n x) x := by
  set c := Real.sqrt (2 * ((n : ℝ) + 1)) with hc
  have hc2 : c * c = 2 * ((n : ℝ) + 1) := Real.mul_self_sqrt (by positivity)
  -- `ψₙ'` as an explicit function, from the creation identity.
  have hcre_fun : ∀ y : ℝ,
      deriv (hermiteFunction n) y = y * hermiteFunction n y - c * hermiteFunction (n + 1) y := by
    intro y
    have h := mul_sub_deriv_hermiteFunction n y
    rw [← hc] at h
    linarith
  -- The value of `ψₙ''`, assembled from `ψₙ'` and `ψ_{n+1}'` and reduced to `(x² - (2n+1))·ψₙ`.
  have hval :
      (1 * hermiteFunction n x + x * deriv (hermiteFunction n) x)
          - c * deriv (hermiteFunction (n + 1)) x
        = (x ^ 2 - (2 * n + 1)) * hermiteFunction n x := by
    have hcre := hcre_fun x
    have hann : x * hermiteFunction (n + 1) x + deriv (hermiteFunction (n + 1)) x
        = c * hermiteFunction n x := by
      have h := mul_add_deriv_hermiteFunction (n + 1) x
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
      rw [← hc] at h
      exact h
    linear_combination x * hcre - c * hann - hermiteFunction n x * hc2
  -- Differentiate the explicit form of `ψₙ'`, then transport back to `deriv (hermiteFunction n)`.
  have p1 := (hasDerivAt_id' (x := x)).mul
    (hasDerivAt_hermiteFunction n x).differentiableAt.hasDerivAt
  have p2 := ((hasDerivAt_hermiteFunction (n + 1) x).differentiableAt.hasDerivAt).const_mul c
  have hP : HasDerivAt (fun y => y * hermiteFunction n y - c * hermiteFunction (n + 1) y)
      ((x ^ 2 - (2 * n + 1)) * hermiteFunction n x) x := by
    have hsub := p1.sub p2
    rwa [hval] at hsub
  exact hP.congr_of_eventuallyEq (Filter.Eventually.of_forall hcre_fun)

/-- **Second derivative of the Hermite function.** `ψₙ'' = (x² - (2n+1))·ψₙ`; the closed form
behind the harmonic-oscillator eigen-equation. -/
@[simp, grind =]
theorem deriv_deriv_hermiteFunction (n : ℕ) (x : ℝ) :
    deriv (deriv (hermiteFunction n)) x = (x ^ 2 - (2 * n + 1)) * hermiteFunction n x :=
  (hasDerivAt_deriv_hermiteFunction n x).deriv

/-- **The harmonic-oscillator eigen-equation.** The Hermite function `ψₙ` is an eigenfunction of the
Schrödinger operator `-d²/dx² + x²` with eigenvalue `2n+1`:

`-ψₙ'' + x²·ψₙ = (2n+1)·ψₙ`. -/
theorem hermiteFunction_oscillator (n : ℕ) (x : ℝ) :
    -deriv (deriv (hermiteFunction n)) x + x ^ 2 * hermiteFunction n x
      = (2 * n + 1) * hermiteFunction n x := by
  rw [deriv_deriv_hermiteFunction]
  ring

/-- The oscillator eigen-equation phrased with `iteratedDeriv 2`. -/
@[simp, grind =]
theorem iteratedDeriv_two_hermiteFunction (n : ℕ) (x : ℝ) :
    iteratedDeriv 2 (hermiteFunction n) x = (x ^ 2 - (2 * n + 1)) * hermiteFunction n x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_deriv_hermiteFunction]

end TauCeti
