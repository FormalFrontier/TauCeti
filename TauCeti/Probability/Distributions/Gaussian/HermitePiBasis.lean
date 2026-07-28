module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.InnerProductSpace.L2.Pi
public import TauCeti.Probability.Distributions.Gaussian.HermiteBasis

/-!
# The multi-index Hermite basis of a multivariate Gaussian `L²`

The `Fintype`-indexed product of the one-dimensional Gaussian Hermite basis: the multi-index family
`Ψ_a(x) = ∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)` is a Hilbert basis of `L²(γ^ι)`, the standard basis for
multivariate Gaussian `L²` and for chaos expansions.

Both inputs are already in place, so this file only combines them: `TauCeti.piHilbertBasis` builds
a Hilbert basis of `L²(Measure.pi μ)` from coordinatewise bases, and
`TauCeti.gaussianHermiteHilbertBasis` is the one-dimensional factor.

## Main statements

* `TauCeti.gaussianHermitePiBasis` — the multi-index basis.
* `TauCeti.coeFn_gaussianHermitePiBasis` — the anti-vacuity pin: the `a`-th vector really is the
  product `∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)`.
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

end TauCeti
