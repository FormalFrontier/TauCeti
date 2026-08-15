/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Hermite.Parseval
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Pi.Basis

/-!
# Parseval and expansions for the multivariate Gaussian Hermite basis

`TauCeti.gaussianHermitePiBasis` exhibits the multi-index Hermite products
`Ψ_a(x) = ∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)` as a Hilbert basis of `L²(γ^ι)`, `γ = N(0, 1)`. This file supplies
the coefficient, Parseval, and reconstruction API for that basis: the expansion of an `L²` function
of `ι` independent standard Gaussians into multivariate Hermite polynomials, the finite-dimensional
form of a chaos expansion. It is the `Fintype`-indexed analogue of
`TauCeti.hasSum_gaussianHermite_expansion` and its neighbours.

As in one dimension the coefficient has no name of its own: it is spelled out as the integral
against `∏ᵢ H_{aᵢ}/√(aᵢ!)`, and the Parseval-side lemmas are named after that integral.

At this arity the file additionally gives the coordinate as an integral, proves that its integrand
is integrable, and specializes `TauCeti.piHilbertBasis_repr_L2piMul` to factor the coordinates of a
product function into the one-dimensional coordinates of its factors.

## Main statements

* `TauCeti.gaussianHermitePiBasis_repr_apply` identifies each coordinate with its integral, whose
  integrand is integrable by
  `TauCeti.integrable_prod_hermite_div_sqrt_factorial_mul_pi_gaussianReal`.
* `TauCeti.gaussianHermitePiBasis_repr_L2piMul` factors the coordinates of a product function.
* `TauCeti.tsum_inner_mul_inner_L2piMul_gaussianHermiteHilbertBasis` is Parseval in polarized form.
* `TauCeti.tsum_norm_sq_integral_prod_hermite_mul_pi_gaussianReal` is Parseval's identity for those
  coefficients.
* `TauCeti.summable_norm_sq_integral_prod_hermite_mul_pi_gaussianReal` gives square-summability of
  the coefficients.
* `TauCeti.hasSum_gaussianHermitePi_expansion` reconstructs every `L²(γ^ι)` vector from its
  multivariate Hermite series.

All statements hold for an arbitrary `RCLike` scalar field, simultaneously covering real and
complex-valued `L²` functions.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial ProbabilityTheory

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

/-- The integrand of the coordinate integral below is integrable: it is the pointwise inner product
of two `L²` functions. -/
theorem integrable_prod_hermite_div_sqrt_factorial_mul_pi_gaussianReal
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) (a : ι → ℕ) :
    Integrable (fun x : ι → ℝ => (∏ i, (algebraMap ℝ 𝕜)
      (aeval (x i) (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ))) * f x)
        (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ)) := by
  refine (integrable_L2piMul_mul (fun i => gaussianHermiteHilbertBasis 𝕜 (a i)) f).congr ?_
  filter_upwards [coeFn_L2piMul (fun i => gaussianHermiteHilbertBasis 𝕜 (a i)),
    coeFn_gaussianHermitePiBasis 𝕜 ι a] with x hprod hexplicit
  rw [← hprod, ← gaussianHermitePiBasis_apply, hexplicit]

/-- The `a`-th multivariate Gaussian Hermite coordinate of `f` is the integral of `f` against the
normalized multi-index Hermite product `∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)`. The polynomials are real, so no
complex conjugate survives. -/
theorem gaussianHermitePiBasis_repr_apply
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) (a : ι → ℕ) :
    (gaussianHermitePiBasis 𝕜 ι).repr f a
      = ∫ x : ι → ℝ, (∏ i, (algebraMap ℝ 𝕜)
          (aeval (x i) (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ))) * f x
            ∂(Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ)) := by
  rw [(gaussianHermitePiBasis 𝕜 ι).repr_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_gaussianHermitePiBasis 𝕜 ι a] with x hx
  rw [hx]
  simp [RCLike.algebraMap_eq_ofReal, map_prod, mul_comm]

/-- **The multi-index coordinates of a product function factor.** If `f(x) = ∏ᵢ Fᵢ(xᵢ)` for
one-dimensional `L²(N(0, 1))` factors `Fᵢ`, its `a`-th multivariate Hermite coordinate is the
product of the `aᵢ`-th one-dimensional Hermite coordinates of the factors: a multivariate chaos
expansion of a product of independent variables is computable from one-dimensional ones. -/
theorem gaussianHermitePiBasis_repr_L2piMul
    (F : ι → Lp 𝕜 2 (gaussianReal 0 1)) (a : ι → ℕ) :
    (gaussianHermitePiBasis 𝕜 ι).repr (L2piMul F) a
      = ∏ i, ∫ x : ℝ, (algebraMap ℝ 𝕜)
          (aeval x (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ)) * F i x
            ∂(gaussianReal 0 1) := by
  rw [HilbertBasis.repr_apply_apply, gaussianHermitePiBasis_apply]
  calc
    inner 𝕜 (L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i)) (L2piMul F)
        = ∏ i, (gaussianHermiteHilbertBasis 𝕜).repr (F i) (a i) := by
          simpa only [HilbertBasis.repr_apply_apply, piHilbertBasis_apply] using
            piHilbertBasis_repr_L2piMul (fun _ : ι => gaussianHermiteHilbertBasis 𝕜) F a
    _ = _ := Finset.prod_congr rfl fun i _ => by
      rw [gaussianHermiteHilbertBasis_repr_apply]

/-- **Parseval's identity for the multivariate Gaussian Hermite basis** (polarized form): the
multi-index Gaussian Hermite coordinates of `f` and `g` pair to their inner product. -/
theorem tsum_inner_mul_inner_L2piMul_gaussianHermiteHilbertBasis
    (f g : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :
    ∑' a : ι → ℕ, inner 𝕜 f (L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i))
        * inner 𝕜 (L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i)) g = inner 𝕜 f g := by
  simpa only [gaussianHermitePiBasis_apply] using
    (gaussianHermitePiBasis 𝕜 ι).tsum_inner_mul_inner f g

/-- **Parseval's identity for the multivariate Gaussian Hermite basis.** The squared coefficients
of `f` against the multi-index Hermite products sum to `‖f‖²`. -/
theorem tsum_norm_sq_integral_prod_hermite_mul_pi_gaussianReal
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :
    ∑' a : ι → ℕ, ‖∫ x : ι → ℝ, (∏ i, (algebraMap ℝ 𝕜)
      (aeval (x i) (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ))) * f x
        ∂(Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))‖ ^ 2 = ‖f‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, gaussianHermitePiBasis_repr_apply] using
    (gaussianHermitePiBasis 𝕜 ι).tsum_norm_sq_inner f

/-- The squared multivariate Gaussian Hermite coefficients of an `L²(γ^ι)` function are
summable. -/
theorem summable_norm_sq_integral_prod_hermite_mul_pi_gaussianReal
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :
    Summable fun a : ι → ℕ => ‖∫ x : ι → ℝ, (∏ i, (algebraMap ℝ 𝕜)
      (aeval (x i) (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ))) * f x
        ∂(Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))‖ ^ 2 := by
  simpa only [← HilbertBasis.repr_apply_apply, gaussianHermitePiBasis_repr_apply] using
    (gaussianHermitePiBasis 𝕜 ι).summable_norm_sq_inner f

/-- **The multivariate Gaussian Hermite expansion.** Every `f ∈ L²(γ^ι; 𝕜)` is the sum of its
multi-index Hermite series, summed over multi-indices `a : ι → ℕ` in the unordered sense. -/
theorem hasSum_gaussianHermitePi_expansion
    (f : Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :
    HasSum (fun a : ι → ℕ =>
      (∫ x : ι → ℝ, (∏ i, (algebraMap ℝ 𝕜)
          (aeval (x i) (hermite (a i)) / Real.sqrt ((a i).factorial : ℝ))) * f x
          ∂(Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) •
            L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i)) f := by
  simpa only [gaussianHermitePiBasis_repr_apply, gaussianHermitePiBasis_apply] using
    (gaussianHermitePiBasis 𝕜 ι).hasSum_repr f

end TauCeti
