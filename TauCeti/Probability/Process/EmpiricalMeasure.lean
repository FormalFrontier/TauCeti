/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Empirical measures of sequences

This file defines the empirical probability measure of the first `n + 1` terms of a sequence and
gives its basic evaluation, integration, and measurability API.  The successor indexing makes the
object a probability measure without a nonemptiness side condition and matches the form used in
limit theorems.

The construction is a uniform finite sum of Dirac measures.  It is the process-level prerequisite
for the empirical-measure form of de Finetti's theorem in the `Exchangeability` roadmap.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α Ω E : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

/-- The empirical probability measure of the first `n + 1` terms of a sequence. -/
def empiricalMeasure (x : ℕ → α) (n : ℕ) : ProbabilityMeasure α :=
  ⟨∑ i ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)), by
    refine ⟨?_⟩
    have hn0 : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    have hntop : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := by simp
    simpa using ENNReal.mul_inv_cancel hn0 hntop⟩

/-- The measure underlying an empirical measure is the uniform finite sum of Dirac measures. -/
@[simp]
theorem empiricalMeasure_toMeasure (x : ℕ → α) (n : ℕ) :
    (empiricalMeasure x n : Measure α) =
      ∑ i ∈ Finset.range (n + 1), (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ • Measure.dirac (x i)) :=
  (rfl)

/-- Evaluation of an empirical measure on a measurable set is its empirical frequency. -/
theorem empiricalMeasure_apply {x : ℕ → α} {n : ℕ} {s : Set α} (hs : MeasurableSet s) :
    (empiricalMeasure x n : Measure α) s =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), s.indicator (1 : α → ℝ≥0∞) (x i) := by
  rw [empiricalMeasure_toMeasure]
  simp only [Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hs, Finset.mul_sum]

/-- The real-valued form of `empiricalMeasure_apply`. -/
theorem empiricalMeasure_apply_toReal {x : ℕ → α} {n : ℕ} {s : Set α}
    (hs : MeasurableSet s) :
    ((empiricalMeasure x n : Measure α) s).toReal =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), s.indicator (1 : α → ℝ) (x i) := by
  rw [empiricalMeasure_apply hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  · rw [ENNReal.toReal_natCast, ENNReal.toReal_sum]
    · congr 1
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hxi : x i ∈ s <;> simp [hxi]
    · intro i hi
      by_cases hxi : x i ∈ s <;> simp [hxi]

omit [MeasurableSpace Ω] in
/-- Evaluation of a path's empirical measure, written as indicators on the sample space. -/
theorem empiricalMeasure_process_apply_toReal {X : ℕ → Ω → α} {ω : Ω} {n : ℕ}
    {s : Set α} (hs : MeasurableSet s) :
    ((empiricalMeasure (fun i => X i ω) n : Measure α) s).toReal =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), (X i ⁻¹' s).indicator (1 : Ω → ℝ) ω := by
  rw [empiricalMeasure_apply_toReal hs]
  refine congrArg (fun z : ℝ => ((n + 1 : ℕ) : ℝ)⁻¹ * z) ?_
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : X i ω ∈ s <;> simp [hxi]

/-- Integrating against an empirical measure is averaging over the sampled values. -/
theorem integral_empiricalMeasure [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {x : ℕ → α} {n : ℕ} {f : α → E} (hf : StronglyMeasurable f) :
    ∫ y, f y ∂(empiricalMeasure x n : Measure α) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), f (x i) := by
  rw [empiricalMeasure_toMeasure, integral_finsetSum_measure]
  · simp_rw [integral_smul_measure, integral_dirac' f _ hf]
    rw [← Finset.smul_sum]
    congr 1
    rw [ENNReal.toReal_inv]
    norm_cast
  · intro i hi
    exact (integrable_dirac' hf (by simp)).smul_measure (by simp)

/-- Empirical measures depend measurably on a sequence of measurable observations. -/
theorem measurable_empiricalMeasure {X : ℕ → Ω → α}
    (n : ℕ) (hX : ∀ i ∈ Finset.range (n + 1), Measurable (X i)) :
    Measurable fun ω => empiricalMeasure (fun i => X i ω) n := by
  have hmeasure : Measurable fun ω =>
      (empiricalMeasure (fun i => X i ω) n : Measure α) := by
    simp_rw [empiricalMeasure_toMeasure]
    exact Finset.measurable_fun_sum _ fun i hi =>
      Measure.measurable_of_measurable_coe _ fun s hs => by
        simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
        exact measurable_const.mul (measurable_one.indicator (hX i hi hs))
  exact hmeasure.subtype_mk

end Probability

end TauCeti
