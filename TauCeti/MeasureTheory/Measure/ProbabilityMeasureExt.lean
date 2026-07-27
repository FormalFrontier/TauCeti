/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Constructions.Cylinders

/-!
# Finite evaluation laws determine a measure on `ProbabilityMeasure α`

Work in progress.
-/

public section

noncomputable section

open MeasureTheory Set MeasurableSpace

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The Giry σ-algebra on `Measure α` is the σ-algebra pulled back from the product σ-algebra
along the all-evaluations map `μ ↦ (s ↦ μ s)`, indexed by the measurable sets.

This is a repackaging of the definition: the instance is already an `iSup` of comaps of the
individual evaluations, and `comap_iSup` turns the comap of the product σ-algebra into that same
`iSup`. -/
theorem measurableSpace_measure_eq_comap_eval :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure α))
      = MeasurableSpace.comap
          (fun μ : Measure α => fun s : {s : Set α // MeasurableSet s} => μ s.1)
          MeasurableSpace.pi := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def]
  rw [Measure.instMeasurableSpace, iSup_subtype]
  simp only [← BorelSpace.measurable_eq (α := ENNReal)]

end MeasureTheory

end TauCeti
