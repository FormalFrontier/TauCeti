/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Analysis.InnerProductSpace.L2.Pi
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis

/-!
# The multi-index Chebyshev `T` basis of `L²(measureT^ι)`

The `Fintype`-indexed product of the one-dimensional Chebyshev basis: the multi-index family
`Ψ_a(x) = ∏ᵢ (T_{aᵢ}(xᵢ))/√(c_{aᵢ})` — with `c₀ = π` and `cₙ = π/2` for `n ≠ 0` — is a Hilbert
basis of the product measure `Measure.pi (fun _ : ι => measureT)` on `ℝ^ι`, the standard basis for
multivariate Chebyshev expansions.

Both inputs are already in place, so the basis itself is a combination: `TauCeti.piHilbertBasis`
(Part B3 of the `OrthogonalL2Bases` roadmap) builds a Hilbert basis of `L²(Measure.pi μ)` from
coordinatewise bases, and `TauCeti.chebyshevTHilbertBasis` is the one-dimensional factor. Mathlib's
`Polynomial.Chebyshev.measureT` is a finite measure
(`TauCeti.chebyshevMeasureT.instIsFiniteMeasure`) and hence σ-finite, so it satisfies the σ-finite
hypothesis `piHilbertBasis` needs.

This is the Chebyshev sibling of `TauCeti.gaussianHermitePiBasis` (Gaussian in the measure) and
`TauCeti.hermiteFunctionPiBasis` (Lebesgue product measure): whichever family a consumer works with,
the multi-index basis is one line of `piHilbertBasis`.

## Main statements

* `TauCeti.chebyshevTPiBasis` — the multi-index Chebyshev basis.
* `TauCeti.coeFn_chebyshevTPiBasis` — the anti-vacuity pin: the `a`-th vector really is the product
  `∏ᵢ normalizedChebyshevT (aᵢ) (xᵢ)` scalar-cast to `𝕜`, almost everywhere for the product measure.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

variable (𝕜 : Type*) [RCLike 𝕜] (ι : Type*) [Fintype ι]

/-- **The multi-index Chebyshev `T` basis.** `piHilbertBasis` over the one-dimensional Chebyshev
basis `TauCeti.chebyshevTHilbertBasis` in every coordinate — the standard basis for multivariate
Chebyshev expansions on the box `[-1, 1]^ι` weighted by `∏ᵢ (1 - xᵢ²)^{-1/2}`. -/
noncomputable def chebyshevTPiBasis :
    HilbertBasis (ι → ℕ) 𝕜 (Lp 𝕜 2 (Measure.pi fun _ : ι => (measureT : Measure ℝ))) :=
  piHilbertBasis fun _ => chebyshevTHilbertBasis 𝕜

/-- **The basis vectors are the multi-index normalized Chebyshev products.** Without this the
construction would only exhibit *some* Hilbert basis of `L²(measureT^ι)`. The coordinatewise
identification `⇑(chebyshevTHilbertBasis 𝕜) = normalizedChebyshevTLp 𝕜` transfers to the product
measure because each evaluation map pushes the product's a.e. filter into the factor's
(`MeasureTheory.Measure.tendsto_eval_ae_ae`). -/
theorem coeFn_chebyshevTPiBasis (a : ι → ℕ) :
    ⇑(chebyshevTPiBasis 𝕜 ι a)
      =ᵐ[Measure.pi fun _ : ι => (measureT : Measure ℝ)]
        fun x => ∏ i, (algebraMap ℝ 𝕜) (normalizedChebyshevT (a i) (x i)) := by
  have hcoord : ∀ i : ι,
      ∀ᵐ x : ι → ℝ ∂(Measure.pi fun _ : ι => (measureT : Measure ℝ)),
        chebyshevTHilbertBasis 𝕜 (a i) (x i)
          = (algebraMap ℝ 𝕜) (normalizedChebyshevT (a i) (x i)) := by
    intro i
    have h1 : ⇑(chebyshevTHilbertBasis 𝕜 (a i)) =ᵐ[measureT]
        fun x => (algebraMap ℝ 𝕜) (normalizedChebyshevT (a i) x) := by
      rw [coe_chebyshevTHilbertBasis]
      exact coeFn_normalizedChebyshevTLp (a i)
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : ι => (measureT : Measure ℝ)) (i := i)).eventually h1
  rw [chebyshevTPiBasis]
  filter_upwards [coeFn_piHilbertBasis (fun _ : ι => chebyshevTHilbertBasis 𝕜) a,
    ae_all_iff.2 hcoord] with x hx hall
  rw [hx]
  exact Finset.prod_congr rfl fun i _ => hall i

end TauCeti
