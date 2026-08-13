/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Restricting a measure-preserving endomorphism to a set it fixes

If `T` preserves `μ` and `T ⁻¹' A = A`, then `T` preserves the restriction `μ.restrict A`, and
consequently precomposition with `T` changes no set-integral over `A`.

Both statements are about an arbitrary endomorphism of an arbitrary measurable space. Nothing here
mentions a shift, a path space, an invariant σ-algebra, or exchangeability: the only input is the
set equation `T ⁻¹' A = A`. Callers holding invariance in the
`MeasurableSpace.invariants`-measurable form obtain that equation from
`MeasurableSpace.measurableSet_invariants`.

## Main results

* `MeasurePreserving.restrict_of_preimage_eq` — the primitive: `T` preserves `μ.restrict A`. This
  is the form Koopman-style arguments want, since `Lp.compMeasurePreserving` consumes a
  `MeasurePreserving` hypothesis rather than an integral identity.
* `MeasurePreserving.setLIntegral_comp_eq_of_preimage_eq` — its `ℝ≥0∞` shadow.
-/

public section

open scoped ENNReal

namespace MeasureTheory

namespace MeasurePreserving

variable {X : Type*} [MeasurableSpace X]

/-- **An endomorphism that fixes a set preserves the restriction to it.** This is the primitive
form: it hands back a `MeasurePreserving`, so consumers can build the Koopman operator on
`Lp (μ.restrict A)` or take Bochner integrals, not only `ℝ≥0∞` ones. -/
theorem restrict_of_preimage_eq {μ : Measure X} {T : X → X} (hT : MeasurePreserving T μ μ)
    {A : Set X} (hA : MeasurableSet A) (hTA : T ⁻¹' A = A) :
    MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
  have h := hT.restrict_preimage hA
  rwa [hTA] at h

/-- **Precomposition with such an endomorphism changes no set-integral over the fixed set.** The
`ℝ≥0∞` shadow of `restrict_of_preimage_eq`. -/
theorem setLIntegral_comp_eq_of_preimage_eq {μ : Measure X} {T : X → X}
    (hT : MeasurePreserving T μ μ) {A : Set X} (hA : MeasurableSet A) (hTA : T ⁻¹' A = A)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in A, f (T x) ∂μ = ∫⁻ x in A, f x ∂μ :=
  (hT.restrict_of_preimage_eq hA hTA).lintegral_comp hf

end MeasurePreserving

end MeasureTheory

end
