/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure

/-!
# The invariant measure on `ℍ` and the Lebesgue measure on `ℂ`

Comparison of Mathlib's invariant measure `volume : Measure ℍ` (`dx dy / y²`) with the
pullback of the Lebesgue measure along the embedding `ℍ ↪ ℂ`: the two are mutually
absolutely continuous, since the density `(Im τ)⁻²` is everywhere positive. Consequently
the invariant measure is positive on nonempty open sets, and preimages of Lebesgue-null
subsets of `ℂ` are null in `ℍ`.

## Main results

* `UpperHalfPlane.volume_absolutelyContinuous_comap`,
  `UpperHalfPlane.comap_absolutelyContinuous_volume`: mutual absolute continuity.
* the `IsOpenPosMeasure` instance for `volume : Measure ℍ`.
* `UpperHalfPlane.volume_preimage_coe_null`: preimages of Lebesgue-null sets are null.

Split out of the Petersson inner-product development ported from the AINTLIB
`LeanModularForms` project
(<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>,
`Modularforms/PeterssonInnerProduct.lean`, Chris Birkbeck).
-/

public section

noncomputable section

open MeasureTheory Measure Set

open scoped NNReal

namespace UpperHalfPlane

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is positive on nonempty open sets. -/
instance : IsOpenPosMeasure (Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)) :=
  IsOpenPosMeasure.comap volume isOpenEmbedding_coe

/-- The invariant measure is absolutely continuous w.r.t. the pullback of the Lebesgue
measure along `ℍ ↪ ℂ`. -/
theorem volume_absolutelyContinuous_comap :
    (volume : Measure ℍ) ≪ Measure.comap UpperHalfPlane.coe volume := by
  rw [volume_def]
  exact withDensity_absolutelyContinuous _ _

/-- The pullback of the Lebesgue measure along `ℍ ↪ ℂ` is absolutely continuous w.r.t. the
invariant measure, since the density `(Im τ)⁻²` is everywhere positive on `ℍ`. -/
theorem comap_absolutelyContinuous_volume :
    Measure.comap UpperHalfPlane.coe (volume : Measure ℂ) ≪ (volume : Measure ℍ) := by
  rw [volume_def]
  refine withDensity_absolutelyContinuous' ?_ (ae_of_all _ fun τ ↦ ?_)
  · exact (measurable_coe_nnreal_ennreal.comp (by fun_prop)).aemeasurable
  · have h1 : (1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ≠ 0 := by
      rw [one_div, ne_eq, inv_eq_zero]
      exact fun h ↦ τ.im_pos.ne' (congrArg NNReal.toReal h)
    exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ h1)

/-- The invariant measure gives positive mass to nonempty open sets. -/
instance : IsOpenPosMeasure (volume : Measure ℍ) :=
  comap_absolutelyContinuous_volume.isOpenPosMeasure

/-- If a subset of `ℂ` has zero Lebesgue measure, its preimage in `ℍ` has zero invariant
measure. -/
theorem volume_preimage_coe_null {S : Set ℂ} (hS : volume S = 0) :
    (volume : Measure ℍ) (UpperHalfPlane.coe ⁻¹' S) = 0 := by
  refine volume_absolutelyContinuous_comap ?_
  rw [isOpenEmbedding_coe.measurableEmbedding.comap_apply]
  exact measure_mono_null (image_preimage_subset _ _) hS

end UpperHalfPlane
