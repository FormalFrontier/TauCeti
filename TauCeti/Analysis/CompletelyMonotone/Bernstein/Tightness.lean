/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Measures

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Tightness of the Chafaï approximating measures

This file proves the tightness input for the Prokhorov extraction step in Bernstein's theorem.
For a completely monotone function `f`, the rescaled Chafaï measures have uniformly bounded
first moment:

`∫⁻ p, p ∂(chafaiRescaled f n) ≤ -f'(0)`.

Markov's inequality therefore bounds their mass outside `[0, R]` by `-f'(0) / R`, uniformly in
`n`. Since the intervals `[0, R]` are compact in `ℝ≥0`, this proves that the whole family is
tight.

## Main declarations

* `TauCeti.chafaiRescaled_measure_Ioi_le`: the uniform first-moment tail bound.
* `TauCeti.isTightMeasureSet_range_chafaiRescaled`: the rescaled Chafaï measures form a tight
  family.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B, Bernstein's theorem
  milestone (“measure extraction via Prokhorov tightness”).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Ch. 1.
* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-- The rescaled Chafaï measures satisfy the uniform Markov tail estimate

`chafaiRescaled f n (R, ∞) ≤ ofReal (-f'(0)) / R`

for every positive `R`. The derivative is taken within `[0, ∞)`, as in the definition of
complete monotonicity. -/
lemma chafaiRescaled_measure_Ioi_le (hcm : IsCompletelyMonotone f) (n : ℕ) {R : ℝ≥0} (hR : R ≠ 0) :
    chafaiRescaled f n (Ioi R) ≤
      ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) := by
  let μ := chafaiRescaled f n
  let moment : ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (p : ℝ)
  have hmoment_meas : AEMeasurable moment μ :=
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun p : ℝ≥0 => (p : ℝ)))
      |>.aemeasurable
  have hsubset : Ioi R ⊆ {p | (R : ℝ≥0∞) ≤ moment p} := by
    intro p hp
    simpa [moment, ENNReal.ofReal_coe_nnreal] using hp.le
  calc
    μ (Ioi R) ≤ μ {p | (R : ℝ≥0∞) ≤ moment p} := measure_mono hsubset
    _ ≤ (∫⁻ p, moment p ∂μ) / (R : ℝ≥0∞) :=
      meas_ge_le_lintegral_div hmoment_meas (by simpa using hR) (by simp)
    _ ≤ ENNReal.ofReal (-derivWithin f (Ici 0) 0) / (R : ℝ≥0∞) :=
      ENNReal.div_le_div_right (chafaiRescaled_lintegral_coe_le f hcm n) _

/-- The family of all rescaled Chafaï approximating measures of a completely monotone function
is tight. Equivalently, for every positive error tolerance there is a compact interval
`[0, R] ⊆ ℝ≥0` whose complement has at most that much mass for every approximation order. -/
theorem isTightMeasureSet_range_chafaiRescaled (hcm : IsCompletelyMonotone f) :
    IsTightMeasureSet (range (chafaiRescaled f)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · refine ⟨∅, isCompact_empty, fun μ _ => ?_⟩
    simp [hε_top]
  let D : ℝ≥0 := ⟨-derivWithin f (Ici 0) 0,
    neg_nonneg.mpr (hcm.derivWithin_nonpos le_rfl)⟩
  let R : ℝ≥0 := D / ε.toNNReal + 1
  have hR : R ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_add_self))
  have hcompact : IsCompact (Iic R) := by
    have hset : Iic R = Icc (0 : ℝ≥0) R := by
      ext p
      simp
    rw [hset]
    exact isCompact_Icc
  refine ⟨Iic R, hcompact, ?_⟩
  intro μ hμ
  obtain ⟨n, rfl⟩ := hμ
  rw [compl_Iic]
  refine (chafaiRescaled_measure_Ioi_le hcm n hR).trans ?_
  have hD : ENNReal.ofReal (-derivWithin f (Ici 0) 0) = (D : ℝ≥0∞) := by
    exact (ENNReal.coe_nnreal_eq D).symm
  rw [hD]
  have hR_gt : D / ε.toNNReal < R := lt_add_one _
  have hε_toNNReal : ε.toNNReal ≠ 0 :=
    ENNReal.toNNReal_ne_zero.mpr ⟨hε.ne', hε_top⟩
  have hR_gt' : (D : ℝ≥0∞) / (ε.toNNReal : ℝ≥0∞) < (R : ℝ≥0∞) := by
    rw [← ENNReal.coe_div hε_toNNReal]
    exact_mod_cast hR_gt
  rw [ENNReal.coe_toNNReal hε_top] at hR_gt'
  exact (ENNReal.div_le_iff (by simpa using hR) (by simp)).2
    ((ENNReal.div_le_iff' hε.ne' hε_top).1 hR_gt'.le)

end TauCeti

end
