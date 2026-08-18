/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.L2.Pi
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Basis
public import TauCeti.Probability.Distributions.Gaussian.Pi

/-!
# The multi-index Hermite basis of a multivariate Gaussian `L²`

The `Fintype`-indexed product of the one-dimensional Gaussian Hermite basis: the multi-index family
`Ψ_a(x) = ∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)` is a Hilbert basis of `L²(γ^ι)`, the standard basis for
multivariate Gaussian `L²` and for chaos expansions.

Both inputs are already in place, so the basis itself is a combination: `TauCeti.piHilbertBasis`
builds a Hilbert basis of `L²(Measure.pi μ)` from coordinatewise bases, and
`TauCeti.gaussianHermiteHilbertBasis` is the one-dimensional factor.

The file then relates this measure-side basis to the function-side multi-index Hermite-function
basis `TauCeti.hermiteFunctionPiBasis` of `L²(volume^ι)`. As in one dimension
(`TauCeti.weightL2Isometry_gaussianHermiteHilbertBasis`), the two are *not* interchanged by the
weight-to-function isometry alone: because `ψₙ` is built on the rescaled argument `x√2`, the image
of `Ψ_a` under `TauCeti.weightL2Isometry` for the joint Gaussian density is the **dilated** product
`∏ᵢ 2^{-1/4} ψ_{aᵢ}(xᵢ/√2)`. The dilation and the `2^{-1/4}` appear once per coordinate, which is
exactly the statement the roadmap asks for.

## Main statements

* `TauCeti.gaussianHermitePiBasis` — the multi-index basis.
* `TauCeti.gaussianHermitePiBasis_apply` — the `a`-th vector is the tensor `TauCeti.L2piMul` of the
  one-dimensional Gaussian Hermite vectors, as an equality of `L²` vectors.
* `TauCeti.coeFn_gaussianHermitePiBasis` — the anti-vacuity pin: the `a`-th vector really is the
  product `∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)`.
* `TauCeti.sqrt_prod_gaussianPDFReal_smul_gaussianHermitePiBasis`: scaling the `a`-th vector by
  the square root of the joint Gaussian density gives `∏ᵢ 2^{-1/4} ψ_{aᵢ}(xᵢ/√2)`.
* `TauCeti.weightL2Isometry_gaussianHermitePiBasis`: the same identification at the
  `TauCeti.weightL2Isometry` level.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial ProbabilityTheory

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι]

/-- **The multivariate Gaussian Hermite basis.** `piHilbertBasis` over the one-dimensional Gaussian
Hermite basis in every coordinate. -/
noncomputable def gaussianHermitePiBasis :
    HilbertBasis (ι → ℕ) 𝕜 (Lp 𝕜 2 (Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ))) :=
  piHilbertBasis fun _ => gaussianHermiteHilbertBasis 𝕜

/-- **The `a`-th basis vector is the tensor of the one-dimensional Gaussian Hermite vectors.**
Stated between `L²` vectors, this is what the expansion API rewrites with, since the inner product
against a tensor factors coordinatewise (`TauCeti.inner_L2piMul`);
`TauCeti.coeFn_gaussianHermitePiBasis` below refines it to a pointwise product of polynomials. -/
@[simp]
theorem gaussianHermitePiBasis_apply (a : ι → ℕ) :
    gaussianHermitePiBasis 𝕜 ι a = L2piMul fun i => gaussianHermiteHilbertBasis 𝕜 (a i) := by
  rw [gaussianHermitePiBasis, piHilbertBasis_apply]

/-- **The basis vectors are the multi-index Hermite products.** Without this the construction would
only exhibit *some* Hilbert basis of `L²(γ^ι)`. The coordinatewise identification transfers to the
product measure because each evaluation map pushes the product's a.e. filter into the factor's
(`MeasureTheory.Measure.tendsto_eval_ae_ae`). -/
theorem coeFn_gaussianHermitePiBasis (a : ι → ℕ) :
    ⇑(gaussianHermitePiBasis 𝕜 ι a)
      =ᵐ[Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ)]
        fun x => ∏ i, (algebraMap ℝ 𝕜)
          (aeval (x i) (hermite (a i)) / Real.sqrt (((a i).factorial : ℝ))) := by
  have hcoord : ∀ i : ι,
      ∀ᵐ x : ι → ℝ ∂(Measure.pi fun _ : ι => (gaussianReal 0 1 : Measure ℝ)),
        gaussianHermiteHilbertBasis 𝕜 (a i) (x i)
          = (algebraMap ℝ 𝕜) (aeval (x i) (hermite (a i)) / Real.sqrt (((a i).factorial : ℝ))) :=
    fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : ι => (gaussianReal 0 1 : Measure ℝ)) (i := i)).eventually
        (coeFn_gaussianHermiteHilbertBasis 𝕜 (a i))
  rw [gaussianHermitePiBasis]
  filter_upwards [coeFn_piHilbertBasis (fun _ : ι => gaussianHermiteHilbertBasis 𝕜) a,
    ae_all_iff.2 hcoord] with x hx hall
  rw [hx]
  exact Finset.prod_congr rfl fun i _ => hall i

/-- **The joint Gaussian envelope of a multi-index basis vector is a dilated Hermite-function
product.** Scaling the `a`-th vector of `L²(γ^ι)` by the square root of the joint density gives
`∏ᵢ 2^{-1/4} ψ_{aᵢ}(xᵢ/√2)`, with `2^{-1/4}` written as `(√√2)⁻¹` to stay inside `Real.sqrt`.

Stated `volume^ι`-almost everywhere, the measure the envelope lives on; the move from `γ^ι`-almost
everywhere is legitimate because the joint density never vanishes
(`TauCeti.pi_volume_absolutelyContinuous_pi_gaussianReal`). Every coordinate contributes one factor
of the one-dimensional identity `TauCeti.sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial`, so
the dilation `xᵢ ↦ xᵢ/√2` really is coordinatewise. -/
theorem sqrt_prod_gaussianPDFReal_smul_gaussianHermitePiBasis (a : ι → ℕ) :
    (fun x : ι → ℝ => Real.sqrt (∏ i, gaussianPDFReal 0 1 (x i))
        • (gaussianHermitePiBasis 𝕜 ι a : (ι → ℝ) → 𝕜) x)
      =ᵐ[Measure.pi fun _ : ι => (volume : Measure ℝ)]
        fun x => ∏ i, (algebraMap ℝ 𝕜)
          ((Real.sqrt (Real.sqrt 2))⁻¹ * hermiteFunction (a i) (x i / Real.sqrt 2)) := by
  have hpt : ∀ x : ι → ℝ, Real.sqrt (∏ i, gaussianPDFReal 0 1 (x i))
      * ∏ i, aeval (x i) (hermite (a i)) / Real.sqrt (((a i).factorial : ℝ))
      = ∏ i, (Real.sqrt (Real.sqrt 2))⁻¹ * hermiteFunction (a i) (x i / Real.sqrt 2) := by
    intro x
    rw [Real.sqrt_prod _ fun i _ => (gaussianPDFReal_pos 0 1 (x i) one_ne_zero).le,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← eval_hermiteℝ]
    exact sqrt_gaussianPDFReal_mul_hermiteℝ_div_sqrt_factorial (a i) (x i)
  filter_upwards [(coeFn_gaussianHermitePiBasis 𝕜 ι a).filter_mono
    (pi_volume_absolutelyContinuous_pi_gaussianReal ι).ae_le] with x hx
  rw [hx, Algebra.smul_def, ← map_prod, ← map_mul, hpt x, map_prod]

/-- **The `TauCeti.weightL2Isometry`-image of the multi-index Gaussian Hermite basis is the dilated
multi-index Hermite-function family.** The `a`-th vector goes to
`∏ᵢ 2^{-1/4} • ψ_{aᵢ}(xᵢ/√2)`, pinning the measure-side basis of `L²(γ^ι)` to the function-side
`TauCeti.hermiteFunctionPiBasis` of `L²(volume^ι)` up to that coordinatewise dilation and
normalization.

`TauCeti.weightL2Isometry` has `L²((volume^ι).withDensity …)` as its domain, whereas
`TauCeti.gaussianHermitePiBasis` lives in the propositionally equal `L²(γ^ι)`, so the basis vector
is transported along `TauCeti.pi_gaussianReal_eq_withDensity` before the isometry is applied. The
positivity and measurability of the joint density are supplied here rather than left to the caller;
by proof irrelevance the statement still applies to `TauCeti.weightL2Isometry` built from any other
proofs of those two side conditions. -/
theorem weightL2Isometry_gaussianHermitePiBasis (a : ι → ℕ) :
    weightL2Isometry (Measure.pi fun _ : ι => (volume : Measure ℝ))
        (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i))
        (Filter.Eventually.of_forall (prod_gaussianPDFReal_pos ι))
        (measurable_prod_gaussianPDFReal ι).aemeasurable
        (cast (congrArg (fun m : Measure (ι → ℝ) => (Lp 𝕜 2 m : Type _))
          (pi_gaussianReal_eq_withDensity ι)) (gaussianHermitePiBasis 𝕜 ι a))
      =ᵐ[Measure.pi fun _ : ι => (volume : Measure ℝ)]
        fun x => ∏ i, (algebraMap ℝ 𝕜)
          ((Real.sqrt (Real.sqrt 2))⁻¹ * hermiteFunction (a i) (x i / Real.sqrt 2)) := by
  -- The isometry is multiplication by `√w`, and the transport does not move representatives.
  refine (weightL2Isometry_apply (𝕜 := 𝕜) (Measure.pi fun _ : ι => (volume : Measure ℝ))
    (fun x : ι → ℝ => ∏ i, gaussianPDFReal 0 1 (x i)) _ _ _).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (sqrt_prod_gaussianPDFReal_smul_gaussianHermitePiBasis 𝕜 ι a)
  exact Filter.Eventually.of_forall fun x => by
    simp only [coeFn_cast_lp (pi_gaussianReal_eq_withDensity ι)
      (gaussianHermitePiBasis 𝕜 ι a) x]

end TauCeti
