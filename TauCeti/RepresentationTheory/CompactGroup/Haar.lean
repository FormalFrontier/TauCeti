/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Normalized Haar measure on compact groups

This file normalizes Mathlib's Haar measure on a compact topological group to a probability
measure, and records its left, right, and inversion invariance.

Since `haarProb` is a Haar measure and a probability measure, Mathlib's generic API applies to
it directly: `MeasureTheory.Measure.isHaarMeasure_eq_of_isProbabilityMeasure` identifies it with
any other Haar probability measure, and `MeasureTheory.integral_mul_left_eq_self`,
`MeasureTheory.integral_mul_right_eq_self` and `MeasureTheory.integral_inv_eq_self` give the
translation and inversion identities used for averaging representations.
-/

public section

open MeasureTheory Set

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure of a compact group has finite total mass. -/
theorem haar_univ_lt_top : (Measure.haar : Measure G) univ < ⊤ :=
  measure_lt_top _ _

/-- Haar measure of a nonempty compact group has nonzero total mass. -/
theorem haar_univ_ne_zero : (Measure.haar : Measure G) univ ≠ 0 :=
  (Measure.measure_pos_of_nonempty_interior (μ := Measure.haar) (by simp)).ne'

/-- Haar probability measure on a compact topological group. -/
@[expose] noncomputable def haarProb : Measure G :=
  ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar

/-- The definition of normalized Haar measure as a rescaling of Mathlib's Haar measure. -/
theorem haarProb_def :
    haarProb G = ((Measure.haar : Measure G) univ)⁻¹ • Measure.haar :=
  rfl

/-- The normalized Haar measure of the whole group is `1`.

This is not a `simp` lemma: once `isProbabilityMeasure_haarProb` is available, `measure_univ`
already puts the left-hand side in simp-normal form. -/
theorem haarProb_apply_univ : haarProb G univ = 1 := by
  rw [haarProb_def, Measure.smul_apply]
  exact ENNReal.inv_mul_cancel (haar_univ_ne_zero G) (haar_univ_lt_top G).ne

instance isProbabilityMeasure_haarProb : IsProbabilityMeasure (haarProb G) :=
  ⟨haarProb_apply_univ G⟩

instance isMulLeftInvariant_haarProb : (haarProb G).IsMulLeftInvariant := by
  rw [haarProb_def]
  infer_instance

instance isHaarMeasure_haarProb : (haarProb G).IsHaarMeasure := by
  rw [haarProb_def]
  exact Measure.IsHaarMeasure.smul Measure.haar
    (ENNReal.inv_ne_zero.mpr (haar_univ_lt_top G).ne)
    (ENNReal.inv_ne_top.mpr (haar_univ_ne_zero G))

/-- Normalized Haar measure is invariant under right multiplication. -/
instance isMulRightInvariant_haarProb : (haarProb G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    let μ := haarProb G
    haveI : μ.IsHaarMeasure := isHaarMeasure_haarProb G
    haveI : IsProbabilityMeasure μ := isProbabilityMeasure_haarProb G
    haveI : (Measure.map (· * g) μ).IsHaarMeasure := by
      convert Measure.isHaarMeasure_map_smul μ (MulOpposite.op g) using 1
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    haveI : IsProbabilityMeasure (Measure.map (· * g) μ) :=
      Measure.isProbabilityMeasure_map
        (continuous_id.mul continuous_const).measurable.aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- Normalized Haar measure is invariant under inversion. -/
instance isInvInvariant_haarProb : (haarProb G).IsInvInvariant where
  inv_eq_self := by
    let μ := haarProb G
    haveI : μ.IsHaarMeasure := isHaarMeasure_haarProb G
    haveI : IsProbabilityMeasure μ := isProbabilityMeasure_haarProb G
    haveI : μ.IsMulRightInvariant := isMulRightInvariant_haarProb G
    letI : (μ.inv).IsHaarMeasure := {
      toIsFiniteMeasureOnCompacts := inferInstance
      toIsMulLeftInvariant := inferInstance
      toIsOpenPosMeasure := inferInstance }
    haveI : IsProbabilityMeasure μ.inv := by
      rw [Measure.inv_def]
      exact Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
    change μ.inv = μ
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end CompactGroup

end TauCeti
