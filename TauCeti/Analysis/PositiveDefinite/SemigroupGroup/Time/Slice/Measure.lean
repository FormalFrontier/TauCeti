/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Bochner.BochnerTheorem
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Difference
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Basic

/-!
# The spatial Bochner measures of a Berg--Christensen--Ressel positive-definite function

Let `F` be a bounded continuous positive-definite function on the involutive semigroup
`ℝ≥0 × V`, with `V` a finite-dimensional real inner-product space. Freezing the time variable
leaves the continuous positive-definite function `F (t, ·)` on `V`, so Bochner's theorem produces
a finite measure `bochnerMeasure (F (t, ·))` on `V`. The Berg--Christensen--Ressel representation
`F (t, a) = ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) ∂μ` prescribes exactly these measures as the
spatial slices of `μ` (`TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`), so the
existence half of the representation is the problem of realizing the family `t ↦ bochnerMeasure
(F (t, ·))` as the Laplace-weighted slices of a single measure on `ℝ≥0 × V`.

This file develops the time regularity of that family, which is what a Bernstein-type argument
consumes. The input is the alternating time-difference positivity of `Time/Difference.lean`: for
every step `h`, the function `(t, v) ↦ F (t, v) - F (t + h, v)` is again bounded, continuous and
positive definite. Bochner's theorem is additive, so the Bochner measure of a time slice splits
as the Bochner measure of that difference plus the Bochner measure of the translated slice. Three
consequences follow.

* The family decreases in time, so each slab mass `t ↦ (bochnerMeasure (F (t, ·))).real B` is
  antitone and bounded by `(F (0, 0)).re`.
* Each slab mass is *continuous*: a decrease of the mass of `B` between two times is dominated by
  the decrease of the total mass, which is the continuous function `t ↦ (F (t, 0)).re`.
* Every iterated alternating difference of a slab mass is nonnegative, since it is again the mass
  of `B` under the Bochner measure of an iterated time difference of `F`.

Together the last two say that each slab mass is a bounded continuous function on `[0,∞)` all of
whose alternating finite differences have the sign `(-1)ⁿ`, the hypothesis of the
Hausdorff--Bernstein--Widder theorem in its difference form. The reverse reading is already
available for a function that *is* represented
(`TauCeti.RepresentsLaplaceFourier.representsLaplace_bochnerMeasure`).

## Main declarations

* `TauCeti.bochnerMeasure_timeSlice_eq_add`: the Bochner measure of a time slice splits as the
  Bochner measure of a time difference plus the Bochner measure of the translated slice.
* `TauCeti.bochnerMeasure_timeSlice_antitone` and
  `TauCeti.bochnerMeasure_timeSlice_real_antitone`: the family of Bochner measures, and each of
  its slab masses, decrease in time.
* `TauCeti.bochnerMeasure_timeSlice_real_univ`, `TauCeti.bochnerMeasure_timeSlice_real_le` and
  `TauCeti.isBounded_range_bochnerMeasure_timeSlice_real`: the total mass is `(F (t, 0)).re`, and
  every slab mass is bounded by `(F (0, 0)).re`, hence has bounded range.
* `TauCeti.sub_bochnerMeasure_timeSlice_real_le_sub_timeAxis_re` and
  `TauCeti.continuous_bochnerMeasure_timeSlice_real`: a slab mass drops by at most the drop of
  the total mass, so it is a continuous function of the time.
* `TauCeti.bochnerMeasure_timeSlice_real_iteratedTimeDifference` and
  `TauCeti.neg_one_pow_mul_fwdDiff_bochnerMeasure_timeSlice_real_nonneg`: the iterated forward
  differences of a slab mass are the slab masses of the iterated time differences of `F`, hence
  alternate in sign.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), the existence half.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {F : ℝ≥0 × V → ℂ}

/-- **Splitting a time slice along a time difference.** For a bounded continuous
Berg--Christensen--Ressel positive-definite function `F`, the Bochner measure of the slice at
time `t` is the Bochner measure of the slice of the time difference `F (·, ·) - F (· + h, ·)`
plus the Bochner measure of the slice at time `t + h`. This is Bochner additivity applied to the
decomposition `F (t, a) = (F (t, a) - F (t + h, a)) + F (t + h, a)`, both summands being
continuous positive-definite functions on `V`. -/
theorem bochnerMeasure_timeSlice_eq_add (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) (t h : ℝ≥0) :
    (bochnerMeasure fun a => F (t, a))
      = (bochnerMeasure fun a => timeDifference h F (t, a))
        + bochnerMeasure fun a => F (t + h, a) := by
  have hDcont : Continuous fun a : V => timeDifference h F (t, a) :=
    (continuous_timeDifference hFcont h).comp (.prodMk_right t)
  have hDpd : IsPositiveDefiniteSub fun a : V => timeDifference h F (t, a) :=
    (hFpd.timeDifference hFbdd h).isPositiveDefiniteSub_timeSlice t
  have hGcont : Continuous fun a : V => F (t + h, a) := hFcont.comp (.prodMk_right _)
  have hGpd : IsPositiveDefiniteSub fun a : V => F (t + h, a) :=
    hFpd.isPositiveDefiniteSub_timeSlice _
  have hfun : (fun a : V => timeDifference h F (t, a) + F (t + h, a)) = fun a : V => F (t, a) := by
    funext a
    simp only [timeDifference_apply]
    ring
  rw [← hfun, bochnerMeasure_add hDcont hDpd hGcont hGpd]

/-- **The Bochner measures of the time slices decrease in time.** Each step forward in time
removes the Bochner measure of the corresponding time difference, which is a measure. -/
theorem bochnerMeasure_timeSlice_antitone (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) :
    Antitone fun t : ℝ≥0 => bochnerMeasure fun a => F (t, a) := by
  intro t s hts
  have hsplit := bochnerMeasure_timeSlice_eq_add hFpd hFcont hFbdd t (s - t)
  rw [add_tsub_cancel_of_le hts] at hsplit
  exact le_trans (Measure.le_add_left le_rfl) hsplit.ge

/-- The mass a fixed measurable set receives from the Bochner measures of the time slices
decreases in time. -/
theorem bochnerMeasure_timeSlice_real_antitone (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (B : Set V) :
    Antitone fun t : ℝ≥0 => (bochnerMeasure fun a => F (t, a)).real B := by
  intro t s hts
  simp only [measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (bochnerMeasure_timeSlice_antitone hFpd hFcont hFbdd hts B)

/-- The total mass of the Bochner measure of the time slice at `t` is `(F (t, 0)).re`. -/
theorem bochnerMeasure_timeSlice_real_univ (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (t : ℝ≥0) : (bochnerMeasure fun a => F (t, a)).real univ = (F (t, 0)).re :=
  bochnerMeasure_real_univ (hFcont.comp (.prodMk_right t)) (hFpd.isPositiveDefiniteSub_timeSlice t)

/-- Every slab mass of the family of Bochner measures is bounded by `(F (0, 0)).re`. -/
theorem bochnerMeasure_timeSlice_real_le (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) (B : Set V) (t : ℝ≥0) :
    (bochnerMeasure fun a => F (t, a)).real B ≤ (F (0, 0)).re := by
  have hmass : (bochnerMeasure fun a => F (t, a)).real univ
      ≤ (bochnerMeasure fun a => F ((0 : ℝ≥0), a)).real univ :=
    bochnerMeasure_timeSlice_real_antitone hFpd hFcont hFbdd univ (zero_le : (0 : ℝ≥0) ≤ t)
  calc (bochnerMeasure fun a => F (t, a)).real B
      ≤ (bochnerMeasure fun a => F (t, a)).real univ := measureReal_mono (subset_univ B)
    _ ≤ (bochnerMeasure fun a => F ((0 : ℝ≥0), a)).real univ := hmass
    _ = (F (0, 0)).re := bochnerMeasure_timeSlice_real_univ hFpd hFcont 0

/-- **The slab masses form a bounded family.** Every value of the slab mass lies in the interval
`[0, (F (0, 0)).re]`, so its range is bounded; this is the boundedness hypothesis of the
Hausdorff--Bernstein--Widder theorem. -/
theorem isBounded_range_bochnerMeasure_timeSlice_real (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (B : Set V) :
    Bornology.IsBounded (range fun t : ℝ≥0 => (bochnerMeasure fun a => F (t, a)).real B) :=
  (Metric.isBounded_Icc 0 (F (0, 0)).re).subset <| range_subset_iff.2 fun t =>
    ⟨measureReal_nonneg, bochnerMeasure_timeSlice_real_le hFpd hFcont hFbdd B t⟩

/-- **The slab masses lose no more than the total mass.** Between two times the mass of a
measurable set `B` drops by at most the drop of the total mass, because the mass of `Bᶜ` also
drops. -/
theorem sub_bochnerMeasure_timeSlice_real_le_sub_timeAxis_re
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) {B : Set V}
    (hB : MeasurableSet B) {t s : ℝ≥0} (hts : t ≤ s) :
    (bochnerMeasure fun a => F (t, a)).real B - (bochnerMeasure fun a => F (s, a)).real B
      ≤ (F (t, 0)).re - (F (s, 0)).re := by
  have ht := measureReal_add_measureReal_compl (μ := bochnerMeasure fun a => F (t, a)) hB
  have hs := measureReal_add_measureReal_compl (μ := bochnerMeasure fun a => F (s, a)) hB
  rw [bochnerMeasure_timeSlice_real_univ hFpd hFcont t] at ht
  rw [bochnerMeasure_timeSlice_real_univ hFpd hFcont s] at hs
  have hc : (bochnerMeasure fun a => F (s, a)).real Bᶜ
      ≤ (bochnerMeasure fun a => F (t, a)).real Bᶜ :=
    bochnerMeasure_timeSlice_real_antitone hFpd hFcont hFbdd Bᶜ hts
  linarith

/-- **The slab masses are continuous in time.** The variation of the mass of `B` is dominated by
the variation of the total mass `t ↦ (F (t, 0)).re`, which is continuous because `F` is. -/
theorem continuous_bochnerMeasure_timeSlice_real (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) {B : Set V}
    (hB : MeasurableSet B) :
    Continuous fun t : ℝ≥0 => (bochnerMeasure fun a => F (t, a)).real B := by
  have hmass : Continuous fun t : ℝ≥0 => (F (t, 0)).re :=
    Complex.continuous_re.comp (hFcont.comp (continuous_id.prodMk continuous_const))
  have key : ∀ t s : ℝ≥0, t ≤ s →
      |(bochnerMeasure fun a => F (t, a)).real B - (bochnerMeasure fun a => F (s, a)).real B|
        ≤ |(F (t, 0)).re - (F (s, 0)).re| := by
    intro t s hts
    have hmono : (bochnerMeasure fun a => F (s, a)).real B
        ≤ (bochnerMeasure fun a => F (t, a)).real B :=
      bochnerMeasure_timeSlice_real_antitone hFpd hFcont hFbdd B hts
    have h1 : 0 ≤ (bochnerMeasure fun a => F (t, a)).real B
        - (bochnerMeasure fun a => F (s, a)).real B := sub_nonneg.2 hmono
    have h2 := sub_bochnerMeasure_timeSlice_real_le_sub_timeAxis_re hFpd hFcont hFbdd hB hts
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  have hdist : ∀ t s : ℝ≥0,
      dist ((bochnerMeasure fun a => F (t, a)).real B)
          ((bochnerMeasure fun a => F (s, a)).real B)
        ≤ dist ((F (t, 0)).re) ((F (s, 0)).re) := by
    intro t s
    rw [Real.dist_eq, Real.dist_eq]
    rcases le_total t s with hle | hle
    · exact key t s hle
    · rw [abs_sub_comm, abs_sub_comm ((F (t, 0)).re)]
      exact key s t hle
  refine Metric.continuous_iff.2 fun b ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hmass b ε hε
  exact ⟨δ, hδ, fun a ha => (hdist a b).trans_lt (hδ' a ha)⟩

/-- **The iterated forward differences of a slab mass are slab masses.** The `n`-th forward
difference with step `h` of `t ↦ (bochnerMeasure (F (t, ·))).real B`, corrected by the sign
`(-1)ⁿ`, is the mass of `B` under the Bochner measure of the time slice of the `n`-th iterated
alternating time difference of `F`. -/
theorem bochnerMeasure_timeSlice_real_iteratedTimeDifference (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (B : Set V) (h : ℝ≥0)
    (n : ℕ) (t : ℝ≥0) :
    (bochnerMeasure fun a => iteratedTimeDifference n h F (t, a)).real B
      = (-1) ^ n * (fwdDiff h)^[n]
          (fun s : ℝ≥0 => (bochnerMeasure fun a => F (s, a)).real B) t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      have hGpd := hFpd.iteratedTimeDifference hFbdd n h
      have hGcont := continuous_iteratedTimeDifference hFcont n h
      have hGbdd := isBounded_range_iteratedTimeDifference hFbdd n h
      have hsplit := bochnerMeasure_timeSlice_eq_add hGpd hGcont hGbdd t h
      have hdiff :
          (bochnerMeasure fun a => timeDifference h (iteratedTimeDifference n h F) (t, a)).real B
            = (bochnerMeasure fun a => iteratedTimeDifference n h F (t, a)).real B
              - (bochnerMeasure fun a => iteratedTimeDifference n h F (t + h, a)).real B := by
        rw [hsplit, measureReal_add_apply]
        ring
      rw [iteratedTimeDifference_succ, hdiff, ih t, ih (t + h), Function.iterate_succ_apply']
      simp only [fwdDiff]
      ring

/-- **The slab masses have alternating forward differences.** Every iterated forward difference
of `t ↦ (bochnerMeasure (F (t, ·))).real B` has the sign `(-1)ⁿ`: this is the complete
monotonicity, in the finite-difference sense, that a Bernstein-type representation of the slab
masses needs. -/
theorem neg_one_pow_mul_fwdDiff_bochnerMeasure_timeSlice_real_nonneg
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) (B : Set V) (h : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    0 ≤ (-1) ^ n * (fwdDiff h)^[n]
        (fun s : ℝ≥0 => (bochnerMeasure fun a => F (s, a)).real B) t := by
  rw [← bochnerMeasure_timeSlice_real_iteratedTimeDifference hFpd hFcont hFbdd B h n t]
  exact measureReal_nonneg

end TauCeti
