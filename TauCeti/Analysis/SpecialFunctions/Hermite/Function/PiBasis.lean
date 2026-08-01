/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.L2.Pi
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis

/-!
# The multi-index Hermite-function basis of `L²(ℝ^ι)`

The `Fintype`-indexed product of the one-dimensional Hermite-function basis: the multi-index family
`Ψ_a(x) = ∏ᵢ ψ_{aᵢ}(xᵢ)` is a Hilbert basis of `L²(volume^ι)`, the standard eigenbasis of the
`ℝ^ι` harmonic oscillator.

This is the Lebesgue-product-measure sibling of `TauCeti.gaussianHermitePiBasis` (which carries the
Gaussian in the measure). Both are `TauCeti.piHilbertBasis` over their respective one-dimensional
factor — here `TauCeti.hermiteHilbertBasis` — so this file only performs the assembly.

## Main statements

* `TauCeti.hermiteFunctionPiBasis` — the multi-index basis.
* `TauCeti.coeFn_hermiteFunctionPiBasis` — the anti-vacuity pin: the `a`-th vector really is the
  product `∏ᵢ ψ_{aᵢ}(xᵢ)`.
-/

public section

namespace TauCeti

open MeasureTheory

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι]

/-- **The multidimensional Hermite-function basis.** `piHilbertBasis` over the one-dimensional
Hermite-function basis in every coordinate — the eigenbasis of the `ℝ^ι` harmonic oscillator. -/
noncomputable def hermiteFunctionPiBasis :
    HilbertBasis (ι → ℕ) 𝕜 (Lp 𝕜 2 (Measure.pi fun _ : ι => (volume : Measure ℝ))) :=
  piHilbertBasis fun _ => hermiteHilbertBasis 𝕜

/-- **The basis vectors are the multi-index Hermite-function products.** Without this the
construction would only exhibit *some* Hilbert basis of `L²(volume^ι)`. The coordinatewise
identification `⇑(hermiteHilbertBasis 𝕜) = hermiteFunctionLp 𝕜` transfers to the product measure
because each evaluation map pushes the product's a.e. filter into the factor's
(`MeasureTheory.Measure.tendsto_eval_ae_ae`). -/
theorem coeFn_hermiteFunctionPiBasis (a : ι → ℕ) :
    ⇑(hermiteFunctionPiBasis 𝕜 ι a)
      =ᵐ[Measure.pi fun _ : ι => (volume : Measure ℝ)]
        fun x => ∏ i, (algebraMap ℝ 𝕜) (hermiteFunction (a i) (x i)) := by
  have hcoord : ∀ i : ι,
      ∀ᵐ x : ι → ℝ ∂(Measure.pi fun _ : ι => (volume : Measure ℝ)),
        hermiteHilbertBasis 𝕜 (a i) (x i)
          = (algebraMap ℝ 𝕜) (hermiteFunction (a i) (x i)) := by
    intro i
    have h1 : ⇑(hermiteHilbertBasis 𝕜 (a i)) =ᵐ[volume]
        fun x => (algebraMap ℝ 𝕜) (hermiteFunction (a i) x) := by
      rw [coe_hermiteHilbertBasis]
      exact coeFn_hermiteFunctionLp (𝕜 := 𝕜) (a i)
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : ι => (volume : Measure ℝ)) (i := i)).eventually h1
  rw [hermiteFunctionPiBasis]
  filter_upwards [coeFn_piHilbertBasis (fun _ : ι => hermiteHilbertBasis 𝕜) a,
    ae_all_iff.2 hcoord] with x hx hall
  rw [hx]
  exact Finset.prod_congr rfl fun i _ => hall i

end TauCeti
