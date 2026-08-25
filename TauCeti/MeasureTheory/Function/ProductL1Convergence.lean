/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.BigOperators.ProdSubProd
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `L¹` convergence of a finite product

If finitely many families of unit-ball-valued functions each converge in `L¹`, then their pointwise
product converges in `L¹` to the product of the limits:

```text
∫ ‖∏ i ∈ s, F i j ω - ∏ i ∈ s, g i ω‖ ∂μ → 0.
```

The whole content is the pointwise telescoping bound `norm_prod_sub_prod_le_sum_norm_sub`, which
turns the integrand into a finite sum of the individual discrepancies; integrating and summing then
gives the result with no Hölder or dominated-convergence machinery.

The unit-ball hypotheses are what make the constant `1`: for indicator observables both a block
average and its conditional expectation lie in `[0, 1]`, which is the motivating case. That
motivation is `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** (the L² averaging library and
the standard-Borel de Finetti route): this is the step from "each window average converges in `L¹`"
to "the product of finitely many window averages converges in `L¹`", which the disjoint-window block
factorization consumes. Layer 5's Koopman route needs the same step against a different
conditioning σ-algebra, which is why this is neutral infrastructure rather than living inside
either route.

Everything is stated for an arbitrary `Finset ι` of factors, an arbitrary filter on the
approximating index, and an arbitrary seminormed commutative ring of values, with a.e. bounds and
`AEStronglyMeasurable` hypotheses, since that is all the integral sees. Nothing here mentions a
process, a σ-algebra or exchangeability.
-/

public section

open Filter MeasureTheory

open scoped Topology

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A finite product of unit-ball families converges in `L¹`.** If each of finitely many families
`F i ·` converges to `g i` in `L¹`, and every value lies almost everywhere in the closed unit ball,
then the product `∏ i ∈ s, F i j` converges to `∏ i ∈ s, g i` in `L¹`. -/
theorem tendsto_integral_norm_prod_sub_prod {ι ι' R : Type*} [SeminormedCommRing R]
    [NormOneClass R] {l : Filter ι'} {μ : Measure Ω} [IsFiniteMeasure μ] {s : Finset ι}
    {F : ι → ι' → Ω → R} {g : ι → Ω → R}
    (hF_meas : ∀ i ∈ s, ∀ j, AEStronglyMeasurable (F i j) μ)
    (hg_meas : ∀ i ∈ s, AEStronglyMeasurable (g i) μ)
    (hF_le : ∀ i ∈ s, ∀ j, ∀ᵐ ω ∂μ, ‖F i j ω‖ ≤ 1)
    (hg_le : ∀ i ∈ s, ∀ᵐ ω ∂μ, ‖g i ω‖ ≤ 1)
    (hconv : ∀ i ∈ s, Tendsto (fun j => ∫ ω, ‖F i j ω - g i ω‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun j => ∫ ω, ‖(∏ i ∈ s, F i j ω) - ∏ i ∈ s, g i ω‖ ∂μ) l (𝓝 0) := by
  have hFprod : ∀ j, AEStronglyMeasurable (fun ω => ∏ i ∈ s, F i j ω) μ := fun j =>
    (Finset.aestronglyMeasurable_prod s fun i hi => hF_meas i hi j).congr
      (ae_of_all _ fun ω => Finset.prod_apply ω s _)
  have hgprod : AEStronglyMeasurable (fun ω => ∏ i ∈ s, g i ω) μ :=
    (Finset.aestronglyMeasurable_prod s fun i hi => hg_meas i hi).congr
      (ae_of_all _ fun ω => Finset.prod_apply ω s _)
  -- Every discrepancy is bounded by `2`, so it is integrable against a finite measure.
  have hsub_int : ∀ i ∈ s, ∀ j, Integrable (fun ω => ‖F i j ω - g i ω‖) μ := by
    intro i hi j
    refine (integrable_const (2 : ℝ)).mono'
      ((hF_meas i hi j).sub (hg_meas i hi)).norm ?_
    filter_upwards [hF_le i hi j, hg_le i hi] with ω h1 h2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by linarith)
  -- The telescoping bound, almost everywhere in `ω`, for each index `j`.
  have hpoint : ∀ j, ∀ᵐ ω ∂μ,
      ‖(∏ i ∈ s, F i j ω) - ∏ i ∈ s, g i ω‖ ≤ ∑ i ∈ s, ‖F i j ω - g i ω‖ := by
    intro j
    filter_upwards [(Filter.eventually_all_finset s).2 fun i hi => hF_le i hi j,
      (Filter.eventually_all_finset s).2 hg_le] with ω hF hg
    exact norm_prod_sub_prod_le_sum_norm_sub s (fun i hi => hF i hi) fun i hi => hg i hi
  -- The telescoping bound already dominates the integrand by an integrable function.
  have hprod_int : ∀ j, Integrable
      (fun ω => ‖(∏ i ∈ s, F i j ω) - ∏ i ∈ s, g i ω‖) μ := fun j =>
    (integrable_finsetSum _ fun i hi => hsub_int i hi j).mono'
      ((hFprod j).sub hgprod).norm (by
        filter_upwards [hpoint j] with ω hω
        rwa [Real.norm_of_nonneg (norm_nonneg _)])
  have hmaj : Tendsto (fun j => ∑ i ∈ s, ∫ ω, ‖F i j ω - g i ω‖ ∂μ) l (𝓝 0) := by
    simpa using tendsto_finsetSum s fun i hi => hconv i hi
  refine squeeze_zero' (Eventually.of_forall fun j => integral_nonneg fun _ => norm_nonneg _)
    (Eventually.of_forall fun j => ?_) hmaj
  calc ∫ ω, ‖(∏ i ∈ s, F i j ω) - ∏ i ∈ s, g i ω‖ ∂μ
      ≤ ∫ ω, ∑ i ∈ s, ‖F i j ω - g i ω‖ ∂μ :=
        integral_mono_ae (hprod_int j)
          (integrable_finsetSum _ fun i hi => hsub_int i hi j) (hpoint j)
    _ = ∑ i ∈ s, ∫ ω, ‖F i j ω - g i ω‖ ∂μ := integral_finsetSum _ fun i hi => hsub_int i hi j

end MeasureTheory

end TauCeti

end
