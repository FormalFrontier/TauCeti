/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
import Mathlib.MeasureTheory.Measure.Real

/-!
# Zero-one criteria and almost surely constant maps

A zero-one measure gives every measurable set mass `0` or `1`. Mathlib's
`MeasureTheory.IsZeroOneMeasure.exists_eq_dirac` identifies such a measure with a Dirac mass, but
only when the carrier is standard Borel. This file records the form that survives on an arbitrary
carrier: a measurable map *into* a standard Borel space is almost surely constant, because its
pushforward is again a zero-one probability measure and is therefore Dirac.

The carrier itself needs no Borel structure, so this applies to a space that carries a measurable
map into a standard Borel space without being one — for instance `ProbabilityMeasure α` for a
countably generated `α`, which
`TauCeti.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac_probabilityMeasure` evaluates into a
countable power of `ℝ≥0∞`.

## Main results

* `TauCeti.MeasureTheory.measure_eq_zero_or_one_of_forall_approx_factorization`: a null-measurable
  event is trivial when it admits arbitrarily close pairs whose intersection mass factors;
* `TauCeti.MeasureTheory.IsZeroOneMeasure.exists_ae_eq_const`: under a zero-one measure, an
  almost-everywhere measurable map into a standard Borel space agrees almost everywhere with a
  single value.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal symmDiff

namespace TauCeti

namespace MeasureTheory

/-- `|x y - q²| ≤ e (2q + e)` when `x` and `y` are within `e` of `q ≥ 0` and `y ≥ 0`. -/
private theorem abs_mul_sub_mul_self_le {x y q e : ℝ} (hx : |x - q| ≤ e) (hy : |y - q| ≤ e)
    (hy0 : 0 ≤ y) (hq0 : 0 ≤ q) (he : 0 ≤ e) :
    |x * y - q * q| ≤ e * (2 * q + e) := by
  have heq : x * y - q * q = (x - q) * y + q * (y - q) := by ring
  have hyq : y ≤ q + e := by linarith [(abs_le.1 hy).2]
  calc |x * y - q * q| ≤ |(x - q) * y| + |q * (y - q)| := by
        rw [heq]; exact abs_add_le _ _
    _ = |x - q| * y + q * |y - q| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy0, abs_of_nonneg hq0]
    _ ≤ e * (q + e) + q * e := by gcongr
    _ = e * (2 * q + e) := by ring

/-- Two events within `e` of `s` have intersection within `2e` of `s`. -/
private theorem abs_measureReal_inter_sub_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {A B s : Set Ω}
    (hA : NullMeasurableSet A μ) (hB : NullMeasurableSet B μ) (hs : NullMeasurableSet s μ)
    {e : ℝ} (h1 : μ.real (symmDiff A s) < e) (h2 : μ.real (symmDiff B s) < e) :
    |μ.real (A ∩ B) - μ.real s| < 2 * e := by
  have hsub : symmDiff (A ∩ B) s ⊆ symmDiff A s ∪ symmDiff B s := by
    simpa only [← compl_inter, compl_symmDiff_compl] using
      (Set.union_symmDiff_subset (s := Aᶜ) (t := Bᶜ) (u := sᶜ))
  have hIS : μ.real (symmDiff (A ∩ B) s) < 2 * e :=
    calc μ.real (symmDiff (A ∩ B) s)
        ≤ μ.real (symmDiff A s ∪ symmDiff B s) := measureReal_mono hsub (by finiteness)
      _ ≤ μ.real (symmDiff A s) + μ.real (symmDiff B s) := measureReal_union_le _ _
      _ < 2 * e := by linarith
  exact lt_of_le_of_lt (abs_measureReal_sub_le_measureReal_symmDiff (hA.inter hB) hs) hIS

/-- With `e ≤ 1`, the two-sided approximation forces `|μ s - (μ s)²| ≤ e (2 μ s + 3)`. -/
private theorem abs_measureReal_sub_mul_self_le_of_symmDiff_lt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {t t' s : Set Ω} (ht : NullMeasurableSet t μ) (ht' : NullMeasurableSet t' μ)
    (hs : NullMeasurableSet s μ) {e : ℝ} (he : e ≤ 1) (h1 : μ.real (symmDiff t s) < e)
    (h2 : μ.real (symmDiff t' s) < e)
    (hinter : μ.real (t ∩ t') = μ.real t * μ.real t') :
    |μ.real s - μ.real s * μ.real s| ≤ e * (2 * μ.real s + 3) := by
  have hbt : |μ.real t - μ.real s| ≤ e :=
    (abs_measureReal_sub_le_measureReal_symmDiff ht hs).trans h1.le
  have hbt' : |μ.real t' - μ.real s| ≤ e :=
    (abs_measureReal_sub_le_measureReal_symmDiff ht' hs).trans h2.le
  have he0 : 0 ≤ e := (abs_nonneg _).trans hbt
  have hbi : |μ.real (t ∩ t') - μ.real s| < 2 * e :=
    abs_measureReal_inter_sub_lt ht ht' hs h1 h2
  have hprod : |μ.real t * μ.real t' - μ.real s * μ.real s| ≤ e * (2 * μ.real s + e) :=
    abs_mul_sub_mul_self_le hbt hbt' measureReal_nonneg measureReal_nonneg he0
  rw [hinter] at hbi
  have hsplit : μ.real s - μ.real s * μ.real s =
      (μ.real s - μ.real t * μ.real t') + (μ.real t * μ.real t' - μ.real s * μ.real s) := by ring
  calc |μ.real s - μ.real s * μ.real s|
      ≤ |μ.real s - μ.real t * μ.real t'| + |μ.real t * μ.real t' - μ.real s * μ.real s| := by
        rw [hsplit]; exact abs_add_le _ _
    _ ≤ 2 * e + e * (2 * μ.real s + e) := by rw [abs_sub_comm]; linarith
    _ ≤ e * (2 * μ.real s + 3) := by nlinarith [measureReal_nonneg (μ := μ) (s := s)]

/-- **Arbitrarily close factoring approximants force a zero-one event.** Suppose that for every
`ε > 0`, the event `s` is within `ε` in symmetric-difference measure of two events `t` and `t'`
whose intersection mass factors. Then `s` has measure `0` or `1`; the measure need only be finite.

The two approximants need not have the same measure and need not themselves be independent as
random objects; only the displayed factorization of their intersection is used. -/
theorem measure_eq_zero_or_one_of_forall_approx_factorization {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {s : Set Ω} (hs : NullMeasurableSet s μ)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ t t' : Set Ω, NullMeasurableSet t μ ∧ NullMeasurableSet t' μ ∧
        μ.real (symmDiff t s) < ε ∧ μ.real (symmDiff t' s) < ε ∧
        μ.real (t ∩ t') = μ.real t * μ.real t') :
    μ s = 0 ∨ μ s = 1 := by
  have hsq : μ.real s = μ.real s * μ.real s := by
    by_contra hne
    set d : ℝ := |μ.real s - μ.real s * μ.real s| with hd
    have hd0 : 0 < d := hd ▸ abs_pos.mpr (sub_ne_zero.mpr hne)
    have hq0 : 0 ≤ μ.real s := measureReal_nonneg
    -- an `ε` at most `1` and small enough that `ε (2 μ s + 3) < d`
    set e : ℝ := min 1 (d / (2 * (2 * μ.real s + 3))) with he
    have he0 : 0 < e := lt_min one_pos (by positivity)
    obtain ⟨t, t', ht, ht', h1, h2, hinter⟩ := happrox e he0
    have hfinal := abs_measureReal_sub_mul_self_le_of_symmDiff_lt ht ht' hs (min_le_left _ _)
      h1 h2 hinter
    rw [← hd] at hfinal
    have hle : e * (2 * μ.real s + 3) ≤ d / 2 := by
      calc e * (2 * μ.real s + 3) ≤ d / (2 * (2 * μ.real s + 3)) * (2 * μ.real s + 3) := by
            gcongr; exact min_le_right _ _
        _ = d / 2 := by field_simp
    linarith
  have hfin : μ s ≠ ∞ := measure_ne_top μ s
  have h01 : μ.real s = 0 ∨ μ.real s = 1 := by
    have hz : μ.real s * (1 - μ.real s) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [measureReal_def] at h01
  rcases h01 with h0 | h1
  · exact Or.inl (((ENNReal.toReal_eq_zero_iff (μ s)).mp h0).resolve_right hfin)
  · exact Or.inr ((ENNReal.toReal_eq_one_iff (μ s)).mp h1)

/-- **A zero-one law is almost surely constant along a measurable map.** The pushforward of a
nonzero zero-one measure along `f` is again a zero-one probability measure; on a standard Borel
space it is therefore a Dirac mass at some `q`, and `f` equals `q` almost everywhere.

The carrier `Ω` needs no topological or Borel structure of its own, and `f` need only be
almost-everywhere measurable. -/
theorem IsZeroOneMeasure.exists_ae_eq_const {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [StandardBorelSpace β] {π : Measure Ω} [NeZero π] [_root_.MeasureTheory.IsZeroOneMeasure π]
    {f : Ω → β} (hf : AEMeasurable f π) :
    ∃ q : β, ∀ᵐ ω ∂π, f ω = q := by
  have : IsProbabilityMeasure π := by
    rcases IsZeroOrProbabilityMeasure.measure_univ (μ := π) with (h | h)
    · simp_all
    · exact ⟨h⟩
  have : _root_.MeasureTheory.IsZeroOneMeasure (π.map f) := {
    zero_one₀ := fun s hs => by
      rw [Measure.map_apply_of_aemeasurable hf hs]
      exact _root_.MeasureTheory.Measure.zero_one π (f ⁻¹' s) }
  obtain ⟨q, hq⟩ := _root_.MeasureTheory.IsZeroOneMeasure.exists_eq_dirac (μ := π.map f)
  refine ⟨q, ae_of_ae_map (p := fun y => y = q) hf ?_⟩
  rw [hq]
  simp

end MeasureTheory

end TauCeti
