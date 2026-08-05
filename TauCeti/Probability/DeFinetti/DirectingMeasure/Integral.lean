/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating finite products of directing-measure evaluations

Two facts about `∏ i, directingMeasure μ X ω (B i)`, read as a function of `ω`, that the de Finetti
rectangle arguments need: it is integrable in its real form, and its real integral agrees with its
`ℝ≥0∞` integral.

## Main results

* `integrable_prod_directingMeasure_real` — the product of the real evaluations is `[0,1]`-valued
  and measurable, hence integrable against a finite measure.
* `ofReal_integral_eq_lintegral_prod_directingMeasure` — the real integral of that product is the
  `ℝ≥0∞` integral of the product of the evaluations themselves.

In both, the measure in the integration slot is independent of the measure `μ` that defines the
directing measure: `μ` is only the directing-measure parameter, and the integral is taken against a
separate `ν`. The set-integral forms are the instances at `ν := μ.restrict A`. Neither mentions
conditional independence, block factorization, or any cylinder: they are facts about the directing
measure alone, which is why they live here rather than in the summit modules that consume them
(`DeFinetti/BlockFactorization.lean` and `DeFinetti/JointRectangle.lean`).

This module is separate from `DirectingMeasure/Basic.lean` so that the measurability and evaluation
API there stays free of the Bochner/Lebesgue integration dependencies these two results need.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace α]

/-- The directing-measure product is a `[0,1]`-valued measurable function, hence integrable against
a finite measure. Only tail-measurability of the process and measurability of the blocks are used;
the integration measure `ν` is unrelated to the `μ` defining the directing measure. -/
lemma integrable_prod_directingMeasure_real [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ω} [IsFiniteMeasure ν] {X : ℕ → Ω → α}
    (hTail : tailProcess X ≤ mΩ) {r : ℕ} {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    Integrable (fun ω => ∏ i, (directingMeasure μ X ω).real (B i)) ν := by
  have hg_meas : Measurable fun ω => ∏ i, (directingMeasure μ X ω).real (B i) :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hB i)).ennreal_toReal
  refine (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [measureReal_def]
  rw [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)

/-- The real integral of the directing-measure product is its `ℝ≥0∞` integral, factor by factor:
each factor is a finite measure of a set, so `ENNReal.ofReal_toReal` applies. As above, `ν` is an
arbitrary integration measure, so the set-integral form is the instance `ν := μ.restrict A`. -/
lemma ofReal_integral_eq_lintegral_prod_directingMeasure [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ν : Measure Ω} {X : ℕ → Ω → α} {r : ℕ}
    {B : Fin r → Set α}
    (hg_int : Integrable (fun ω => ∏ i, (directingMeasure μ X ω).real (B i)) ν) :
    ENNReal.ofReal (∫ ω, ∏ i, (directingMeasure μ X ω).real (B i) ∂ν)
      = ∫⁻ ω, ∏ i, directingMeasure μ X ω (B i) ∂ν := by
  rw [ofReal_integral_eq_lintegral_ofReal hg_int
    (ae_of_all _ fun ω => Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
  refine lintegral_congr fun ω => ?_
  simp only [measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

end Probability

end TauCeti

end

end
