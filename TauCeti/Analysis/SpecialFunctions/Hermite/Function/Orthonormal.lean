/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Lp
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality

/-!
# Orthonormality of the Hermite functions

This file proves that the Hermite functions
`ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)` (`TauCeti.hermiteFunction`) form an orthonormal system in
`L²(ℝ)`, the roadmap milestones **A2** (pointwise) and **A3** (the `Lp` orthonormality the
`hermiteHilbertBasis` construction consumes) of `TauCetiRoadmap/OrthogonalL2Bases/README.md`.

* `TauCeti.integral_hermiteFunction_mul_hermiteFunction`:
  `∫ x, ψₘ(x) · ψₙ(x) = if m = n then 1 else 0`, the pointwise orthonormality relation. It is the
  polynomial orthogonality relation `TauCeti.integral_hermite_mul_hermite_mul_gaussian`
  (`∫ Hₘ Hₙ e^{-x²/2} = if m = n then n!√(2π) else 0`, milestone A1) transported across the
  dilation `u = x√2` (`MeasureTheory.Measure.integral_comp_mul_right`): the Gaussian envelope
  `exp(-x²/2)²` collapses to `exp(-(x√2)²/2)`, and the normalizations `√(n!√π)` cancel the
  `n!√(2π)` self-pairing up to the Jacobian `(√2)⁻¹`.
* `TauCeti.inner_hermiteFunctionLp`:
  `⟪ψₘ, ψₙ⟫ = if m = n then 1 else 0` for the `Lp 𝕜 2 volume` vectors, over any `RCLike` scalar
  field `𝕜`, obtained by rewriting the `L²` inner product as the pointwise integral above.
* `TauCeti.orthonormal_hermiteFunctionLp`: `Orthonormal 𝕜 (hermiteFunctionLp 𝕜)`, immediate from the
  inner-product formula via `orthonormal_iff_ite`.
* `TauCeti.norm_hermiteFunctionLp`: every Hermite mode has `L²` norm one.

The zeroth-mode normalization `TauCeti.integral_hermiteFunction_zero_mul_self` is the `n = 0`
special case of the pointwise result here; the `Lp` counterpart is
`TauCeti.norm_hermiteFunctionLp 0`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real

/-! ## Pointwise orthonormality -/

/-- **Target A2 (orthonormality).** The Hermite functions are pointwise orthonormal in `L²(ℝ)`:
`∫ x, ψₘ(x) · ψₙ(x) = if m = n then 1 else 0`. This is the polynomial orthogonality relation
`integral_hermite_mul_hermite_mul_gaussian` pushed through the dilation `u = x√2`. -/
theorem integral_hermiteFunction_mul_hermiteFunction (m n : ℕ) :
    ∫ x : ℝ, hermiteFunction m x * hermiteFunction n x = if m = n then 1 else 0 := by
  -- The two Gaussian envelopes combine into the envelope at the dilated argument `x√2`.
  have henv : ∀ x : ℝ, Real.exp (-(x ^ 2 / 2)) * Real.exp (-(x ^ 2 / 2))
      = Real.exp (-((x * Real.sqrt 2) ^ 2 / 2)) := by
    intro x
    rw [← Real.exp_add]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  -- Rewrite the integrand as `g (x√2)` divided by the product of the two normalizations.
  have hpt : ∀ x : ℝ, hermiteFunction m x * hermiteFunction n x
      = (aeval (x * Real.sqrt 2) (hermite m) * aeval (x * Real.sqrt 2) (hermite n)
            * Real.exp (-((x * Real.sqrt 2) ^ 2 / 2)))
          / (Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi)
            * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)) := by
    intro x
    rw [hermiteFunction_def, hermiteFunction_def, ← henv x]
    ring
  simp only [hpt]
  rw [integral_div]
  -- Change of variables `u = x√2`.
  have hcov :
      (∫ x : ℝ, aeval (x * Real.sqrt 2) (hermite m) * aeval (x * Real.sqrt 2) (hermite n)
          * Real.exp (-((x * Real.sqrt 2) ^ 2 / 2)))
        = |(Real.sqrt 2)⁻¹| •
            ∫ u : ℝ, aeval u (hermite m) * aeval u (hermite n) * Real.exp (-(u ^ 2 / 2)) :=
    Measure.integral_comp_mul_right
      (fun u : ℝ => aeval u (hermite m) * aeval u (hermite n) * Real.exp (-(u ^ 2 / 2)))
      (Real.sqrt 2)
  rw [hcov, integral_hermite_mul_hermite_mul_gaussian, smul_eq_mul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2))]
  split_ifs with h
  · rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) Real.pi,
      Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (n.factorial : ℝ) * Real.sqrt Real.pi)]
    have h2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hpi : Real.sqrt Real.pi ≠ 0 := Real.sqrt_ne_zero'.mpr Real.pi_pos
    field_simp
  · simp

/-! ## Orthonormality of the `Lp` Hermite vectors -/

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Target A3 (orthonormality, inner-product form).** The `Lp` Hermite vectors satisfy
`⟪ψₘ, ψₙ⟫ = if m = n then 1 else 0`, over any `RCLike` scalar field, by evaluating the `L²` inner
product as the pointwise integral `integral_hermiteFunction_mul_hermiteFunction`. -/
theorem inner_hermiteFunctionLp (m n : ℕ) :
    inner 𝕜 (hermiteFunctionLp 𝕜 m) (hermiteFunctionLp 𝕜 n) = if m = n then (1 : 𝕜) else 0 := by
  calc
    inner 𝕜 (hermiteFunctionLp 𝕜 m) (hermiteFunctionLp 𝕜 n)
      = ∫ x : ℝ, (algebraMap ℝ 𝕜) (hermiteFunction m x * hermiteFunction n x) := by
        rw [MeasureTheory.L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_hermiteFunctionLp (𝕜 := 𝕜) m, coeFn_hermiteFunctionLp (𝕜 := 𝕜) n]
          with x hm hn
        rw [hm, hn]
        exact inner_algebraMap_algebraMap (𝕜 := 𝕜) (hermiteFunction m x) (hermiteFunction n x)
    _ = if m = n then (1 : 𝕜) else 0 := by
        rw [integral_ofReal, integral_hermiteFunction_mul_hermiteFunction]
        split_ifs <;> simp

/-- **Target A3 (orthonormality).** The `Lp` Hermite functions form an orthonormal system in
`L²(ℝ; 𝕜)`, for any `RCLike` scalar field `𝕜`. This is the orthonormality input the
`hermiteHilbertBasis` construction feeds to `HilbertBasis.mkOfOrthogonalEqBot`. -/
theorem orthonormal_hermiteFunctionLp : Orthonormal 𝕜 (hermiteFunctionLp 𝕜) :=
  orthonormal_iff_ite.mpr inner_hermiteFunctionLp

/-- **Target A2 (unit norm).** Every Hermite function has `L²` norm one, over any `RCLike`
scalar field. -/
@[simp]
theorem norm_hermiteFunctionLp (n : ℕ) : ‖hermiteFunctionLp 𝕜 n‖ = 1 :=
  orthonormal_hermiteFunctionLp.norm_eq_one n

end TauCeti
