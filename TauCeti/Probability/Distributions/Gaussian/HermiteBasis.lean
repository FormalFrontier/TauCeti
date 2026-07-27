module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.Probability.Distributions.Gaussian.HermiteMemLp

/-!
# The Hermite polynomials as a Hilbert basis of `L²(γ)`

Roadmap milestone **A3′**: the measure-side one-dimensional Gaussian Hermite basis. Where
`TauCeti.hermiteHilbertBasis` puts the Gaussian envelope inside the *function* (`ψₙ` in `L²(ℝ)`),
this puts it in the *measure*: `Hₙ/√(n!)` is an orthonormal basis of `L²(γ)` for the standard
Gaussian `γ = gaussianReal 0 1`.

That is the form multivariate Gaussian `L²` and chaos expansions consume, and it is the input
`piHilbertBasis` needs for the multidimensional basis of Part D.

## Main statements

* `TauCeti.integral_hermite_mul_hermite_mul_gaussianPDFReal` — the orthogonality relation against
  the standard Gaussian density, with normalization `cₙ = n!`.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real ProbabilityTheory

/-- The standard Gaussian density is `(√(2π))⁻¹·e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  rw [gaussianPDFReal_def]
  norm_num
  exact Or.inl (by ring)

/-- **Orthogonality against the standard Gaussian density.**
`∫ Hₘ Hₙ dγ = δₘₙ · n!`. This is the Hermite orthogonality relation (milestone A1) divided by the
Gaussian normalizing constant `√(2π)`, which is exactly what turns the `n!√(2π)` there into the
`cₙ = n!` the measure-side basis uses. -/
theorem integral_hermite_mul_hermite_mul_gaussianPDFReal (m n : ℕ) :
    (∫ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x)
      = if m = n then (n.factorial : ℝ) else 0 := by
  have h2pi : Real.sqrt (2 * π) ≠ 0 := by
    have : (0 : ℝ) < 2 * π := by positivity
    exact ne_of_gt (Real.sqrt_pos.mpr this)
  have hpt : ∀ x : ℝ, aeval x (hermite m) * aeval x (hermite n) * gaussianPDFReal 0 1 x
      = (Real.sqrt (2 * π))⁻¹
        * (aeval x (hermite m) * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))) := by
    intro x
    rw [gaussianPDFReal_zero_one]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_hermite_mul_hermite_mul_gaussian]
  by_cases hmn : m = n
  · rw [if_pos hmn, if_pos hmn]
    field_simp
  · rw [if_neg hmn, if_neg hmn, mul_zero]

end TauCeti
