/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Sard's lemma when the source has smaller dimension

This file proves the lower-dimensional-source case of finite-dimensional Sard's theorem. If a
`C¹` map goes from a finite-dimensional real normed space to one of strictly larger dimension,
then the image of every subset of the source has additive Haar measure zero. In particular, the
whole range is null.

Every derivative in this dimension range is nonsurjective, so the range is exactly the set of
critical values. The proof uses the Hausdorff-dimension route already developed in Mathlib:
`ContDiffOn.dimH_image_le` says that `C¹` maps do not increase dimension, and
`measure_zero_of_dimH_lt` turns the resulting strict dimension bound into nullity. Uniqueness of
additive Haar measure transfers the statement from Hausdorff measure to any Haar normalization.

This supplies the source-dimension-smaller-than-target case of finite-dimensional Sard in Lane F0
of the analytic Heegaard Floer roadmap. Together with the equal-dimensional case, it isolates the
higher-regularity Morse--Sard argument to the remaining case where the source dimension is larger.

## Main declarations

* `TauCeti.ContDiffOn.addHaar_image_eq_zero_of_dimH_lt_finrank`: a `C¹` map on a convex set sends
  each subset of sufficiently small Hausdorff dimension to an additive-Haar-null set.
* `TauCeti.ContDiff.addHaar_image_eq_zero_of_finrank_lt_finrank`: a `C¹` map into a
  strictly higher-dimensional space sends every subset to an additive-Haar-null set.
* `TauCeti.ContDiff.addHaar_range_eq_zero_of_finrank_lt_finrank`: the whole range of such a map is
  additive-Haar-null.
* `TauCeti.not_surjective_fderiv_of_finrank_lt_finrank`: every derivative in this dimension range
  is nonsurjective.
* `TauCeti.setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank`: every point belongs to the
  critical locus in this dimension range.
* `TauCeti.ContDiff.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank`: the critical
  values are additive-Haar-null, in the form used by Sard's theorem.

The Hausdorff-dimension argument follows the one used for the lower-dimensional Sard corollary in
Mathlib's `Topology.MetricSpace.HausdorffDimension`.
-/

public section

open Function MeasureTheory MeasureTheory.Measure Module Set

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {s t : Set E} {f : E → F}
  (ν : Measure F) [IsAddHaarMeasure ν]

/-- A `C¹` map on a convex set sends every subset whose Hausdorff dimension is strictly smaller
than the dimension of the codomain to an additive-Haar-null set.

The domain and codomain may carry arbitrary finite-dimensional norms, and `ν` may be any
normalization of additive Haar measure. -/
theorem ContDiffOn.addHaar_image_eq_zero_of_dimH_lt_finrank
    (hf : ContDiffOn ℝ 1 f s) (hs : Convex ℝ s) (ht : t ⊆ s)
    (htF : dimH t < finrank ℝ F) : ν (f '' t) = 0 := by
  have hν : ν ≪ (μH[(finrank ℝ F : ℝ)] : Measure F) :=
    absolutelyContinuous_isAddHaarMeasure ν _
  apply measure_zero_of_dimH_lt (d := (finrank ℝ F : NNReal)) hν
  simpa only [ENNReal.coe_natCast] using
    (hf.dimH_image_le hs ht).trans_lt htF

/-- A `C¹` map from a finite-dimensional real normed space to a strictly higher-dimensional one
sends every subset of its domain to an additive-Haar-null set. -/
theorem ContDiff.addHaar_image_eq_zero_of_finrank_lt_finrank
    (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) (t : Set E) :
    ν (f '' t) = 0 := by
  apply ContDiffOn.addHaar_image_eq_zero_of_dimH_lt_finrank
    ν hf.contDiffOn convex_univ (subset_univ t)
  exact (dimH_mono (subset_univ t)).trans_lt <| by
    simpa only [Real.dimH_univ_eq_finrank, Nat.cast_lt] using hEF

/-- A `C¹` map from a finite-dimensional real normed space to a strictly higher-dimensional one
has additive-Haar-null range. This is the lower-dimensional-source case of Sard's theorem: every
point of the source is critical because no derivative can be surjective. -/
theorem ContDiff.addHaar_range_eq_zero_of_finrank_lt_finrank
    (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) :
    ν (range f) = 0 := by
  rw [← image_univ]
  exact ContDiff.addHaar_image_eq_zero_of_finrank_lt_finrank ν hf hEF univ

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- When the source has strictly smaller finite dimension than the codomain, every Fréchet
derivative is nonsurjective. Thus every source point is critical, independently of the regularity
of the function. -/
theorem not_surjective_fderiv_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank ℝ E < finrank ℝ F) (x : E) :
    ¬ Surjective (fderiv ℝ f x) := by
  intro hsurj
  exact (not_le_of_gt hEF) (LinearMap.finrank_le_finrank_of_surjective hsurj)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- When the source has strictly smaller finite dimension than the codomain, the critical locus
of any function is the whole source. -/
@[simp]
theorem setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank (f : E → F)
    (hEF : finrank ℝ E < finrank ℝ F) :
    {x | ¬ Surjective (fderiv ℝ f x)} = (univ : Set E) :=
  eq_univ_of_forall fun x ↦ not_surjective_fderiv_of_finrank_lt_finrank f hEF x

/-- The critical values of a `C¹` map from a finite-dimensional real normed space to a strictly
higher-dimensional one have additive Haar measure zero. In this dimension range every point is
critical, but stating the result for the critical locus gives the Sard form consumed by later
regular-value arguments. -/
theorem ContDiff.addHaar_image_not_surjective_fderiv_eq_zero_of_finrank_lt_finrank
    (hf : ContDiff ℝ 1 f) (hEF : finrank ℝ E < finrank ℝ F) :
    ν (f '' {x | ¬ Surjective (fderiv ℝ f x)}) = 0 := by
  rw [setOf_not_surjective_fderiv_eq_univ_of_finrank_lt_finrank f hEF, image_univ]
  exact ContDiff.addHaar_range_eq_zero_of_finrank_lt_finrank ν hf hEF

end TauCeti

end
