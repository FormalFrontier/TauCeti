/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Measurability of measure-valued maps

This file supplies general-purpose measurability results for maps into the Giry measurable space
of measures.

## Main results

* `TauCeti.MeasureTheory.measurable_sum_smul_dirac` — a countable mixture of Dirac measures at
  fixed atoms is measurable when each weight is measurable.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

/-- A countable mixture of Dirac measures at fixed atoms `g i` is measurable in the weights.

Evaluating on a measurable set turns the measure into the sum
`∑' i, f b i * 1_{g i ∈ s}`, and a `tsum` of measurable functions is measurable. The atoms are
indexed by a countable type of their own, so the ambient space `α` may be uncountable. -/
theorem measurable_sum_smul_dirac {β ι α : Type*} [MeasurableSpace β] [MeasurableSpace α]
    [Countable ι] {f : β → ι → ℝ≥0∞} {g : ι → α}
    (hf : ∀ i, Measurable fun b => f b i) :
    Measurable fun b => Measure.sum fun i => f b i • Measure.dirac (g i) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  exact Measurable.tsum fun i => (hf i).mul_const _

end MeasureTheory

end TauCeti
