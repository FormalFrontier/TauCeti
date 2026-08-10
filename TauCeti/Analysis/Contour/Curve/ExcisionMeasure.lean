/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# The excised parameter set shrinks to nothing

An `ε`-excision deletes from the parameter interval every time at which the curve comes within
`ε` of one of finitely many centres. This file records that the deleted set carries no length in
the limit: the integral of the excision's indicator over `[a, b]` tends to `b - a` as `ε → 0⁺`.

Two properties of the curve are used, for two different parts of the argument. **Measurability**
makes each excised set measurable. **Nullity of the times the curve spends exactly
at a centre** gives the almost-everywhere convergence: away from those times the curve keeps a
positive distance from the finite centre set, so the excision condition eventually fails
outright. Injectivity on `[a, b]` is one convenient sufficient condition for the second — it
makes those times finite — and is recorded separately as
`measure_setOf_mem_eq_zero_of_injOn`; a curve may revisit centres, so long as it does so on a
null set of times.

## Main results

* `TauCeti.Contour.nullMeasurableSet_excision`: the excised parameter set is null-measurable
  against any measure for which the curve is a.e. measurable.
* `TauCeti.Contour.measurableSet_excision`: its measurable specialization.
* `TauCeti.Contour.measure_setOf_mem_eq_zero_of_injOn`: an injective curve meets a finite set at
  a null set of times.
* `TauCeti.Contour.tendsto_intervalIntegral_excisionIndicator`: the excision indicator's integral
  over `[a, b]` tends to `b - a` as `ε → 0⁺`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development. This file adapts the measure-theoretic step of
  `ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`
  (`arc_non_excluded_measure_tendsto`, with its `arc_preimage_subsingleton` and
  `arc_min_dist_pos` helpers) onto the current Mathlib pin, restated for an arbitrary curve
  rather than the fundamental-domain arc.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Contour

/-- **The excised parameter set is null-measurable.** The finite union, over the centres, of the
sublevel sets of `t ↦ ‖γ t - s‖`, each null-measurable because `γ` is a.e. measurable. Stated for
an arbitrary measure so that it serves both the ambient statement and the restricted-measure one
that interval integrability needs. -/
theorem nullMeasurableSet_excision {γ : ℝ → ℂ} {μ : MeasureTheory.Measure ℝ}
    (hγ : AEMeasurable γ μ) (S : Finset ℂ) (ε : ℝ) :
    MeasureTheory.NullMeasurableSet {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} μ := by
  have h : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} = ⋃ s ∈ S, {t | ‖γ t - s‖ ≤ ε} := by ext; simp
  exact h ▸ Finset.nullMeasurableSet_biUnion S fun s _ =>
    nullMeasurableSet_le ((hγ.sub_const s).norm) aemeasurable_const

/-- **The excised parameter set is measurable.** It is the finite union, over the centres, of the
preimages of the ray `(-∞, ε]` under `t ↦ ‖γ t - s‖`, each measurable because `γ` is. -/
theorem measurableSet_excision {γ : ℝ → ℂ} (hγm : Measurable γ) (S : Finset ℂ) (ε : ℝ) :
    MeasurableSet {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} := by
  have h : {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} = ⋃ s ∈ S, {t | ‖γ t - s‖ ≤ ε} := by ext; simp
  rw [h]
  exact Finset.measurableSet_biUnion _ fun s _ =>
    measurableSet_le ((hγm.sub_const s).norm) measurable_const

/-- A point lying off a finite set stays off it by a fixed positive margin. -/
private theorem exists_pos_le_norm_sub_of_notMem {S : Finset ℂ} {z : ℂ} (hz : z ∉ S) :
    ∃ δ > 0, ∀ s ∈ S, δ ≤ ‖z - s‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · refine ⟨Metric.infDist z S, ?_, fun s hs => ?_⟩
    · exact (S.finite_toSet.isClosed.notMem_iff_infDist_pos (by exact_mod_cast hne)).mp
        (by exact_mod_cast hz)
    · rw [← dist_eq_norm]
      exact Metric.infDist_le_dist_of_mem (by exact_mod_cast hs)

/-- **An injective curve meets a finite set at a null set of times.** It meets it at finitely
many times — at most one per centre — so those times carry no length. This is the convenient
sufficient condition for `tendsto_intervalIntegral_excisionIndicator`'s hypothesis. -/
theorem measure_setOf_mem_eq_zero_of_injOn {γ : ℝ → ℂ} {a b : ℝ} (hγ : InjOn γ (Icc a b))
    (S : Finset ℂ) : volume {t ∈ Icc a b | γ t ∈ S} = 0 :=
  (Set.Finite.of_injOn (fun _ ht => ht.2) (hγ.mono fun _ ht => ht.1)
    S.finite_toSet).measure_zero volume

/-- **The excised parameter set shrinks to nothing.** Deleting from `[a, b]` the times at which
the curve comes within `ε` of one of finitely many centres costs no length as `ε → 0⁺`: what
survives tends to the whole length `b - a`.

The curve must be measurable, and must spend only a null set of times exactly at a centre —
`measure_setOf_mem_eq_zero_of_injOn` supplies the latter from injectivity. -/
theorem tendsto_intervalIntegral_excisionIndicator {γ : ℝ → ℂ} (hγm : Measurable γ) {a b : ℝ}
    (hab : a ≤ b) (S : Finset ℂ) (hnull : volume {t ∈ Icc a b | γ t ∈ S} = 0) :
    Tendsto (fun ε => ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
      (𝓝[>] 0) (𝓝 (b - a)) := by
  set As : ℝ → Set ℝ := fun ε => Ioc a b \ {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} with hAs_def
  have hAs : ∀ ε, MeasurableSet (As ε) := fun ε =>
    measurableSet_Ioc.diff (measurableSet_excision hγm S ε)
  -- The integral is exactly the surviving set's length.
  have hint : ∀ ε : ℝ, (∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
      = volume.real (As ε) := fun ε => by
    have hcongr : EqOn (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
        ((As ε).indicator 1) (Ioc a b) := fun t ht => by
      by_cases hb : ∃ s ∈ S, ‖γ t - s‖ ≤ ε <;>
        simp [hAs_def, ht, hb]
    rw [intervalIntegral.integral_of_le hab, setIntegral_congr_fun measurableSet_Ioc hcongr,
      setIntegral_indicator (hAs ε), Set.inter_eq_self_of_subset_right Set.sdiff_subset]
    simp [hAs_def]
  simp only [hint]
  -- Away from the null set of exact hits, the excision condition eventually fails outright.
  have hlim : Tendsto (fun ε => volume (As ε)) (𝓝[>] (0 : ℝ)) (𝓝 (volume (Ioc a b))) := by
    refine tendsto_measure_of_ae_tendsto_indicator (𝓝[>] (0 : ℝ)) measurableSet_Ioc hAs
      measurableSet_Ioc
      measure_Ioc_lt_top.ne (Eventually.of_forall fun ε => Set.sdiff_subset) ?_
    refine measure_mono_null (fun t ht => ?_) hnull
    by_contra hnot
    refine ht ?_
    simp only [Set.mem_ofPred_eq]
    by_cases hmem : t ∈ Ioc a b
    · obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_sub_of_notMem (S := S) (z := γ t)
        fun h => hnot ⟨⟨hmem.1.le, hmem.2⟩, h⟩
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      simp only [hAs_def, Set.mem_sdiff, Set.mem_ofPred_eq, hmem, true_and, iff_true, not_exists]
      exact fun s => by push Not; exact fun hs => hε.2.trans_le (hδle s hs)
    · exact Eventually.of_forall fun ε => by simp [hAs_def, hmem]
  simpa only [Function.comp_def, ← measureReal_def, Real.volume_real_Ioc_of_le hab] using
    (ENNReal.tendsto_toReal measure_Ioc_lt_top.ne).comp hlim

end TauCeti.Contour
