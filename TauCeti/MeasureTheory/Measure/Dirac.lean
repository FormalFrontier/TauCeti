/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Pushing a Dirac measure forward along an a.e. measurable map

Mathlib's `MeasureTheory.Measure.map_dirac'` computes `(Measure.dirac x).map T = Measure.dirac
(T x)` for a measurable `T`. A Dirac measure leaves a map no room to be modified on a null set:
its only null sets avoid `x`, so a `Measure.dirac x`-a.e. measurable map already agrees at `x`
with the measurable representative it is a.e. equal to. The pushforward formula therefore holds
under that weaker hypothesis, which is the one a.e.-measurable interfaces such as
`ProbabilityTheory.HasLaw` provide.

## Main results

* `Measure.map_dirac_of_aemeasurable` — the Dirac pushforward formula for a map that is
  only a.e. measurable.
-/

public section

open MeasureTheory

namespace Measure

variable {X : Type*} {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {T : X → Y}

/-- A Dirac measure leaves a map no room to be modified on a null set: pushing `Measure.dirac x`
forward along a `Measure.dirac x`-a.e. measurable map is evaluating that map at `x`. -/
@[simp]
theorem map_dirac_of_aemeasurable {x : X} (hT : AEMeasurable T (Measure.dirac x)) :
    (Measure.dirac x).map T = Measure.dirac (T x) := by
  have hx : T x = hT.mk T x := by
    by_contra hne
    have h0 : Measure.dirac x {y | ¬T y = hT.mk T y} = 0 := ae_iff.1 hT.ae_eq_mk
    rw [Measure.dirac_apply_of_mem hne] at h0
    exact one_ne_zero h0
  rw [Measure.map_congr hT.ae_eq_mk, Measure.map_dirac' hT.measurable_mk, ← hx]

end Measure
