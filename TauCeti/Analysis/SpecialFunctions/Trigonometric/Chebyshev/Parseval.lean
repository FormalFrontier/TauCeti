/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis

/-!
# Parseval and expansions for the Chebyshev `T` basis

`TauCeti.chebyshevTHilbertBasis` exhibits the normalized Chebyshev polynomials
`Tₙ / √cₙ`, where `c₀ = π` and `cₙ = π / 2` for `n ≠ 0`, as a Hilbert basis of
`L²(Polynomial.Chebyshev.measureT)`. This file supplies the coefficient, Parseval, and
reconstruction API for that basis. Its coordinate theorem identifies the abstract
`HilbertBasis.repr` coordinate with the Chebyshev-weighted integral against the normalized
polynomial.

The API and proof structure are adapted from
`TauCeti.Probability.Distributions.Gaussian.Hermite.Parseval`.

## Main statements

* `TauCeti.chebyshevTHilbertBasis_repr_apply` identifies each coordinate with its weighted
  integral.
* `TauCeti.tsum_norm_sq_integral_normalizedChebyshevT_mul_measureT` is the norm-square Parseval
  identity for the explicit integral coefficients.
* `TauCeti.summable_norm_sq_integral_normalizedChebyshevT_mul_measureT` gives their
  square-summability.
* `TauCeti.hasSum_chebyshevT_expansion` reconstructs every `L²` vector from its Chebyshev series.

All statements hold over an arbitrary `RCLike` scalar field, simultaneously covering real- and
complex-valued functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `n`-th Chebyshev coordinate is the integral of `f` against the normalized polynomial
`Tₙ / √cₙ` with respect to the Chebyshev measure. -/
@[simp]
theorem chebyshevTHilbertBasis_repr_apply (f : Lp 𝕜 2 measureT) (n : ℕ) :
    (chebyshevTHilbertBasis 𝕜).repr f n =
      ∫ x : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) * f x ∂measureT := by
  rw [(chebyshevTHilbertBasis 𝕜).repr_apply_apply, coe_chebyshevTHilbertBasis,
    MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_normalizedChebyshevTLp (𝕜 := 𝕜) n] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, mul_comm]

/-- **Parseval's identity for the Chebyshev basis.** The squared norms of the explicit
Chebyshev integral coefficients of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_integral_normalizedChebyshevT_mul_measureT (f : Lp 𝕜 2 measureT) :
    ∑' n : ℕ, ‖∫ x : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) * f x ∂measureT‖ ^ 2 =
      ‖f‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, chebyshevTHilbertBasis_repr_apply] using
    (chebyshevTHilbertBasis 𝕜).tsum_norm_sq_inner f

/-- The squared norms of the Chebyshev integral coefficients of an `L²` function are summable. -/
theorem summable_norm_sq_integral_normalizedChebyshevT_mul_measureT (f : Lp 𝕜 2 measureT) :
    Summable fun n : ℕ =>
      ‖∫ x : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) * f x ∂measureT‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, chebyshevTHilbertBasis_repr_apply] using
    (chebyshevTHilbertBasis 𝕜).summable_norm_sq_inner f

/-- **The Chebyshev expansion.** Every `f ∈ L²(measureT)` is the sum of its normalized
Chebyshev-polynomial series. -/
theorem hasSum_chebyshevT_expansion (f : Lp 𝕜 2 measureT) :
    HasSum (fun n : ℕ =>
      (∫ x : ℝ, (algebraMap ℝ 𝕜) (normalizedChebyshevT n x) * f x ∂measureT) •
        normalizedChebyshevTLp 𝕜 n) f := by
  simpa only [chebyshevTHilbertBasis_repr_apply, coe_chebyshevTHilbertBasis,
    Function.comp_apply] using (chebyshevTHilbertBasis 𝕜).hasSum_repr f

end TauCeti
