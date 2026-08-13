/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- Non-public: the Giry σ-algebra's `∫⁻` measurability and the bounded-integrability criterion are
-- used only inside the proof.
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrating a bounded observable depends measurably on the measure

`MeasureTheory.Measure.measurable_lintegral` says that `μ ↦ ∫⁻ f dμ` is measurable for the Giry
σ-algebra. Its Bochner counterpart is not automatic — a measure against which `f` fails to be
integrable contributes the junk value `0` — but for a **bounded** measurable real observable and a
*probability* measure there is no junk value to worry about, and the Bochner integral is the
difference of the two `∫⁻` halves.

## Main results

* `TauCeti.MeasureTheory.measurable_probabilityMeasure_integral`

This is the observable-valued companion of the fixed-set evaluations
`measurable_probabilityMeasure_toMeasure_apply` in
`TauCeti.MeasureTheory.Measure.ProbabilityMeasureExt`: measurability of `P ↦ ∫ f dP` is what a
statement about a *random* probability measure needs before its limit can be recognized as a
measurable function of that measure.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **Integrating a bounded observable is measurable in the measure.** For a bounded measurable
`f : α → ℝ`, the map `P ↦ ∫ f dP` on `ProbabilityMeasure α` is measurable.

Boundedness is what removes the Bochner integral's junk value: it makes `f` integrable against
every probability measure, so the positive/negative part decomposition holds at every point and
`Measure.measurable_lintegral` applies to each half. -/
theorem measurable_probabilityMeasure_integral {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hbdd : ∀ x, |f x| ≤ C) :
    Measurable fun P : ProbabilityMeasure α => ∫ y, f y ∂(P : Measure α) := by
  have hint : ∀ P : ProbabilityMeasure α, Integrable f (P : Measure α) := fun _ =>
    Integrable.of_bound hf.aestronglyMeasurable C
      (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbdd x)
  have key : ∀ P : ProbabilityMeasure α, ∫ y, f y ∂(P : Measure α) =
      (∫⁻ y, ENNReal.ofReal (f y) ∂(P : Measure α)).toReal -
        (∫⁻ y, ENNReal.ofReal (-f y) ∂(P : Measure α)).toReal := fun P =>
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint P)
  simp_rw [key]
  exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf)).comp
      measurable_subtype_coe).ennreal_toReal.sub
    ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.neg)).comp
      measurable_subtype_coe).ennreal_toReal

end MeasureTheory

end TauCeti
