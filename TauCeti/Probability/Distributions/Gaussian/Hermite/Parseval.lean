/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.Parseval
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Basis

/-!
# Parseval and expansions for the Gaussian Hermite basis

`TauCeti.gaussianHermiteHilbertBasis` exhibits the normalized probabilists' Hermite polynomials
`Hₙ / √(n!)` as a Hilbert basis of `L²(N(0, 1); 𝕜)`. This file supplies the coefficient,
Parseval, and reconstruction API for that basis. In particular, its coordinate theorem writes the
abstract `HilbertBasis.repr` coordinate as the Gaussian integral against `Hₙ / √(n!)`.

## Main statements

* `TauCeti.gaussianHermiteHilbertBasis_repr_apply` identifies each coordinate with its integral.
* `TauCeti.tsum_norm_sq_gaussianHermite_coeff` is Parseval's identity for those coefficients.
* `TauCeti.summable_norm_sq_gaussianHermite_coeff` gives square-summability of the coefficients.
* `TauCeti.hasSum_gaussianHermite_expansion` reconstructs every `L²` vector from its Gaussian
  Hermite series.
* `TauCeti.gaussianHermiteHilbertBasis_repr_self` identifies the coordinates of a basis vector.

All statements hold for an arbitrary `RCLike` scalar field, simultaneously covering real and
complex-valued `L²` functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial ProbabilityTheory

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The `n`-th Gaussian Hermite coordinate is the integral of `f` against the normalized
probabilists' Hermite polynomial `Hₙ / √(n!)`. -/
@[simp]
theorem gaussianHermiteHilbertBasis_repr_apply
    (f : Lp 𝕜 2 (gaussianReal 0 1)) (n : ℕ) :
    (gaussianHermiteHilbertBasis 𝕜).repr f n =
      ∫ x : ℝ, (algebraMap ℝ 𝕜)
        (aeval x (hermite n) / Real.sqrt (n.factorial : ℝ)) * f x ∂(gaussianReal 0 1) := by
  rw [(gaussianHermiteHilbertBasis 𝕜).repr_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_gaussianHermiteHilbertBasis 𝕜 n] with x hx
  rw [hx]
  simp [RCLike.inner_apply, RCLike.conj_ofReal, mul_comm]

/-- **Parseval's identity for the Gaussian Hermite basis.** The squared norms of the Gaussian
Hermite coefficients of `f` sum to `‖f‖²`. -/
theorem tsum_norm_sq_gaussianHermite_coeff (f : Lp 𝕜 2 (gaussianReal 0 1)) :
    ∑' n : ℕ, ‖∫ x : ℝ, (algebraMap ℝ 𝕜)
      (aeval x (hermite n) / Real.sqrt (n.factorial : ℝ)) * f x ∂(gaussianReal 0 1)‖ ^ 2 =
        ‖f‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, gaussianHermiteHilbertBasis_repr_apply] using
    (gaussianHermiteHilbertBasis 𝕜).tsum_norm_sq_inner f

/-- The squared norms of the Gaussian Hermite coefficients of an `L²` function are summable. -/
theorem summable_norm_sq_gaussianHermite_coeff (f : Lp 𝕜 2 (gaussianReal 0 1)) :
    Summable fun n : ℕ => ‖∫ x : ℝ, (algebraMap ℝ 𝕜)
      (aeval x (hermite n) / Real.sqrt (n.factorial : ℝ)) * f x ∂(gaussianReal 0 1)‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, gaussianHermiteHilbertBasis_repr_apply] using
    (gaussianHermiteHilbertBasis 𝕜).summable_norm_sq_inner f

/-- **The Gaussian Hermite expansion.** Every `f ∈ L²(N(0, 1); 𝕜)` is the sum of its
normalized Hermite-polynomial series. -/
theorem hasSum_gaussianHermite_expansion (f : Lp 𝕜 2 (gaussianReal 0 1)) :
    HasSum (fun n : ℕ =>
      (∫ x : ℝ, (algebraMap ℝ 𝕜)
        (aeval x (hermite n) / Real.sqrt (n.factorial : ℝ)) * f x ∂(gaussianReal 0 1)) •
          gaussianHermiteHilbertBasis 𝕜 n) f := by
  simpa only [gaussianHermiteHilbertBasis_repr_apply] using
    (gaussianHermiteHilbertBasis 𝕜).hasSum_repr f

/-- The coordinates of the `n`-th normalized Hermite polynomial are a single `1` in position
`n`. -/
@[simp]
theorem gaussianHermiteHilbertBasis_repr_self (n : ℕ) :
    (gaussianHermiteHilbertBasis 𝕜).repr (gaussianHermiteHilbertBasis 𝕜 n) =
      lp.single 2 n (1 : 𝕜) := by
  classical
  exact (gaussianHermiteHilbertBasis 𝕜).repr_self n

end TauCeti
