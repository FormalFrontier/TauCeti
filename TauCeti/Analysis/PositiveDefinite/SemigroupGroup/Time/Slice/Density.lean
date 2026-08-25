/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.NNRat.Encodable
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Laplace
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Rational
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Measure

/-!
# The fibrewise spatial densities of a Berg--Christensen--Ressel positive-definite function

Let `F` be a bounded continuous positive-definite function on the involutive semigroup `ℝ≥0 × V`,
with `V` a finite-dimensional real inner-product space. Its spatial Bochner measures
`bochnerMeasure (F (t, ·))` decrease in time, so each of them has a Radon--Nikodym derivative
against the one at time `0`
(`TauCeti.withDensity_rnDeriv_bochnerMeasure_timeSlice`). The existence half of the
Berg--Christensen--Ressel representation is exactly the problem of realizing that family of
densities as a family of *fibrewise Laplace transforms*
(`TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel`), which is a Bernstein problem in
the time variable at almost every spatial frequency.

This file supplies the input of that Bernstein problem. Two obstacles have to be cleared.

* A Radon--Nikodym derivative is defined only up to a null set, so the alternating time
  differences of the densities can only be controlled at *countably many* times at once, whereas
  complete monotonicity quantifies over all real times. The countable version is
  `TauCeti.toReal_rnDeriv_bochnerMeasure_timeSlice_listTimeDifference`: the density of the Bochner
  measure of a list time difference of `F` is, almost everywhere, the corresponding mixed forward
  difference of the densities, and it is nonnegative because it is a density.
* The version of the density that is used must be right-continuous in time, since
  `TauCeti.isDifferenceCompletelyMonotone_of_forall_rat` upgrades rational data to real data only
  for a right-continuous function. `TauCeti.timeSliceDensity` is that version: the supremum of the
  Radon--Nikodym derivatives over rational times `r > t`. Being a supremum over a shrinking family
  of rational times it is antitone and right-continuous *for every* spatial frequency, with no null
  set attached, and it agrees almost everywhere with the Radon--Nikodym derivative at each fixed
  time (`TauCeti.timeSliceDensity_ae_eq_rnDeriv`) because the total masses are continuous in time.

The conclusion is `TauCeti.ae_isContinuousCompletelyMonotoneOnIoi_timeSliceDensity`: almost every
fibre of `TauCeti.timeSliceDensity` is a completely monotone function of time, hence a Laplace
transform.

## Main declarations

* `TauCeti.bochnerMeasure_timeSlice_listTimeDifference_le`: the Bochner measure of a list time
  difference is dominated by the Bochner measure of the time slice it differences.
* `TauCeti.toReal_rnDeriv_bochnerMeasure_timeSlice_listTimeDifference`: mixed forward differences
  of the densities are themselves densities, almost everywhere.
* `TauCeti.timeSliceDensity`: the right-continuous version of the family of densities.
* `TauCeti.timeSliceDensity_ae_eq_rnDeriv`: it is a Radon--Nikodym derivative at every fixed time.
* `TauCeti.ae_isDifferenceCompletelyMonotone_timeSliceDensity` and
  `TauCeti.ae_isContinuousCompletelyMonotoneOnIoi_timeSliceDensity`: almost every fibre is
  completely monotone in time.
* `TauCeti.ae_timeSliceDensity_zero_eq_one`: almost every fibre is normalized at time `0`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), the existence half.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {F : ℝ≥0 × V → ℂ}

/-! ## Time differences of the spatial Bochner measures -/

/-- **A list time difference has a smaller Bochner measure than the slice it differences.** Each
further first difference splits the Bochner measure of the previous one into two summands
(`TauCeti.bochnerMeasure_timeSlice_eq_add`), and a summand of measures is dominated by their
sum. -/
theorem bochnerMeasure_timeSlice_listTimeDifference_le (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (l : List ℝ≥0) (t : ℝ≥0) :
    (bochnerMeasure fun a => listTimeDifference l F (t, a))
      ≤ bochnerMeasure fun a => F (t, a) := by
  induction l with
  | nil => simp
  | cons h l ih =>
      have hsplit := bochnerMeasure_timeSlice_eq_add (hFpd.listTimeDifference hFbdd l)
        (continuous_listTimeDifference hFcont l) (isBounded_range_listTimeDifference hFbdd l) t h
      rw [listTimeDifference_cons]
      exact ((Measure.le_add_right le_rfl).trans hsplit.ge).trans ih

/-- **The densities decrease in time**, almost everywhere against the time-`0` Bochner measure:
the earlier spatial measure is the later one plus the Bochner measure of the time difference
between them. -/
theorem rnDeriv_bochnerMeasure_timeSlice_ae_le (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) {t s : ℝ≥0} (hts : t ≤ s) :
    (bochnerMeasure fun a => F (s, a)).rnDeriv (bochnerMeasure fun a => F (0, a))
      ≤ᵐ[bochnerMeasure fun a => F (0, a)]
        (bochnerMeasure fun a => F (t, a)).rnDeriv (bochnerMeasure fun a => F (0, a)) := by
  have hsplit := bochnerMeasure_timeSlice_eq_add hFpd hFcont hFbdd t (s - t)
  rw [add_tsub_cancel_of_le hts] at hsplit
  filter_upwards [Measure.rnDeriv_add (bochnerMeasure fun a => timeDifference (s - t) F (t, a))
    (bochnerMeasure fun a => F (s, a)) (bochnerMeasure fun a => F (0, a))] with q hq
  rw [hsplit, hq, Pi.add_apply]
  exact le_add_self

/-- **Mixed forward differences of the densities are densities.** The Radon--Nikodym derivative of
the Bochner measure of a list time difference of `F` is, almost everywhere, the corresponding
mixed forward difference of the Radon--Nikodym derivatives of the time slices. Since the left-hand
side is a density it is nonnegative, which is the sign condition of the
Hausdorff--Bernstein--Widder theorem at the times involved. -/
theorem toReal_rnDeriv_bochnerMeasure_timeSlice_listTimeDifference (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (l : List ℝ≥0) (t : ℝ≥0) :
    ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)),
      ((bochnerMeasure fun a => listTimeDifference l F (t, a)).rnDeriv
          (bochnerMeasure fun a => F (0, a)) q).toReal
        = (-1) ^ l.length * fwdDiffList (l.map (fun h : ℝ≥0 => (h : ℝ)))
            (fun s : ℝ => ((bochnerMeasure fun a => F (s.toNNReal, a)).rnDeriv
              (bochnerMeasure fun a => F (0, a)) q).toReal) (t : ℝ) := by
  induction l generalizing t with
  | nil =>
      filter_upwards with q
      simp
  | cons h l ih =>
      have hsplit := bochnerMeasure_timeSlice_eq_add (hFpd.listTimeDifference hFbdd l)
        (continuous_listTimeDifference hFcont l) (isBounded_range_listTimeDifference hFbdd l) t h
      filter_upwards [ih t, ih (t + h),
        Measure.rnDeriv_add
          (bochnerMeasure fun a => timeDifference h (listTimeDifference l F) (t, a))
          (bochnerMeasure fun a => listTimeDifference l F (t + h, a))
          (bochnerMeasure fun a => F (0, a)),
        Measure.rnDeriv_lt_top
          (bochnerMeasure fun a => timeDifference h (listTimeDifference l F) (t, a))
          (bochnerMeasure fun a => F (0, a)),
        Measure.rnDeriv_lt_top (bochnerMeasure fun a => listTimeDifference l F (t + h, a))
          (bochnerMeasure fun a => F (0, a))] with q ht hth hadd hfin₁ hfin₂
      have hsum : ((bochnerMeasure fun a => listTimeDifference l F (t, a)).rnDeriv
            (bochnerMeasure fun a => F (0, a)) q).toReal
          = ((bochnerMeasure fun a => timeDifference h (listTimeDifference l F) (t, a)).rnDeriv
              (bochnerMeasure fun a => F (0, a)) q).toReal
            + ((bochnerMeasure fun a => listTimeDifference l F (t + h, a)).rnDeriv
              (bochnerMeasure fun a => F (0, a)) q).toReal := by
        rw [hsplit, hadd, Pi.add_apply, ENNReal.toReal_add hfin₁.ne hfin₂.ne]
      rw [listTimeDifference_cons, List.map_cons, List.length_cons]
      simp only [fwdDiffList_cons, fwdDiff]
      have hcoe : ((t + h : ℝ≥0) : ℝ) = (t : ℝ) + (h : ℝ) := NNReal.coe_add t h
      rw [hcoe] at hth
      rw [pow_succ]
      nlinarith [hsum, ht, hth]

/-! ## The right-continuous version of the densities -/

/-- **The right-continuous spatial density** of a function on `ℝ≥0 × V` at time `t`: the supremum,
over rational times `r > t`, of the Radon--Nikodym derivative of the spatial Bochner measure at
time `r` against the one at time `0`.

Taking the supremum over rational times to the right of `t` costs nothing at a fixed time — the
family of Radon--Nikodym derivatives decreases in time and the total masses are continuous, so
`TauCeti.timeSliceDensity_ae_eq_rnDeriv` identifies this with the Radon--Nikodym derivative itself
— while it buys antitonicity and right-continuity in time at *every* point of `V`, with no null
set attached. That is what makes a fibrewise Bernstein argument possible. -/
def timeSliceDensity (F : ℝ≥0 × V → ℂ) (t : ℝ≥0) (q : V) : ℝ≥0∞ :=
  ⨆ r : {r : ℚ≥0 // t < (r : ℝ≥0)},
    (bochnerMeasure fun a => F ((r.1 : ℝ≥0), a)).rnDeriv (bochnerMeasure fun a => F (0, a)) q

/-- Each Radon--Nikodym derivative at a rational time to the right of `t` is dominated by the
right-continuous density at `t`. -/
theorem rnDeriv_le_timeSliceDensity (F : ℝ≥0 × V → ℂ) {t : ℝ≥0} {r : ℚ≥0}
    (hr : t < (r : ℝ≥0)) (q : V) :
    (bochnerMeasure fun a => F ((r : ℝ≥0), a)).rnDeriv (bochnerMeasure fun a => F (0, a)) q
      ≤ timeSliceDensity F t q :=
  le_iSup (fun r : {r : ℚ≥0 // t < (r : ℝ≥0)} =>
    (bochnerMeasure fun a => F ((r.1 : ℝ≥0), a)).rnDeriv
      (bochnerMeasure fun a => F (0, a)) q) ⟨r, hr⟩

/-- The right-continuous density decreases in time, at every point. -/
theorem timeSliceDensity_antitone (F : ℝ≥0 × V → ℂ) (q : V) :
    Antitone fun t => timeSliceDensity F t q := fun _ _ htt' =>
  iSup_le fun r => le_iSup_of_le ⟨r.1, htt'.trans_lt r.2⟩ le_rfl

@[fun_prop]
theorem measurable_timeSliceDensity (F : ℝ≥0 × V → ℂ) (t : ℝ≥0) :
    Measurable (timeSliceDensity F t) :=
  Measurable.iSup fun _ => Measure.measurable_rnDeriv _ _

/-- A sequence of rational times decreasing to a given time. -/
private theorem exists_seq_nnrat_tendsto (t : ℝ≥0) :
    ∃ r : ℕ → ℚ≥0, (∀ n, t < (r n : ℝ≥0)) ∧
      Tendsto (fun n => (((r n : ℝ≥0)) : ℝ)) atTop (𝓝 (t : ℝ)) := by
  have hlt : ∀ n : ℕ, ∃ r : ℚ≥0, t < (r : ℝ≥0) ∧
      ((r : ℝ≥0) : ℝ) < (t : ℝ) + 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hgap : (t : ℝ) < (t : ℝ) + 1 / ((n : ℝ) + 1) := by linarith
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hgap
    have hq₀ : (0 : ℚ) ≤ q := by exact_mod_cast t.coe_nonneg.trans hq₁.le
    have hcast : ((q.toNNRat : ℝ≥0) : ℝ) = (q : ℝ) := by
      have hstep : ((q.toNNRat : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := by norm_cast
      rw [hstep, Rat.coe_toNNRat _ hq₀]
    exact ⟨q.toNNRat, by rw [← NNReal.coe_lt_coe, hcast]; exact hq₁, by rw [hcast]; exact hq₂⟩
  choose r hr₁ hr₂ using hlt
  refine ⟨r, hr₁, ?_⟩
  have hup : Tendsto (fun n : ℕ => (t : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 ((t : ℝ) + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hup
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (NNReal.coe_lt_coe.2 (hr₁ n)).le) fun n => (hr₂ n).le

/-- The right-continuous density is dominated by the Radon--Nikodym derivative at the same time. -/
theorem timeSliceDensity_le_rnDeriv (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) (t : ℝ≥0) :
    timeSliceDensity F t
      ≤ᵐ[bochnerMeasure fun a => F (0, a)]
        (bochnerMeasure fun a => F (t, a)).rnDeriv (bochnerMeasure fun a => F (0, a)) := by
  filter_upwards [ae_all_iff.2 fun r : {r : ℚ≥0 // t < (r : ℝ≥0)} =>
    rnDeriv_bochnerMeasure_timeSlice_ae_le hFpd hFcont hFbdd r.2.le] with q hq
  exact iSup_le hq

/-- **The right-continuous density is a Radon--Nikodym derivative at every fixed time.** The
supremum over rational times to the right loses no mass, because the total mass
`t ↦ (F (t, 0)).re` is continuous. -/
theorem timeSliceDensity_ae_eq_rnDeriv (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) (t : ℝ≥0) :
    timeSliceDensity F t
      =ᵐ[bochnerMeasure fun a => F (0, a)]
        (bochnerMeasure fun a => F (t, a)).rnDeriv (bochnerMeasure fun a => F (0, a)) := by
  have hac := bochnerMeasure_timeSlice_absolutelyContinuous hFpd hFcont hFbdd
  have hle := timeSliceDensity_le_rnDeriv hFpd hFcont hFbdd t
  have hmass : ∀ s : ℝ≥0, (bochnerMeasure fun a => F (s, a)) univ
      = ENNReal.ofReal ((F (s, 0)).re) := fun s =>
    bochnerMeasure_univ (hFcont.comp (.prodMk_right s)) (hFpd.isPositiveDefiniteSub_timeSlice s)
  have hint : ∫⁻ q, (bochnerMeasure fun a => F (t, a)).rnDeriv
        (bochnerMeasure fun a => F (0, a)) q ∂(bochnerMeasure fun a => F (0, a))
      ≤ ∫⁻ q, timeSliceDensity F t q ∂(bochnerMeasure fun a => F (0, a)) := by
    rw [Measure.lintegral_rnDeriv (hac t), hmass t]
    obtain ⟨r, hr, hrt⟩ := exists_seq_nnrat_tendsto t
    have hstep : ∀ n, ENNReal.ofReal ((F (((r n : ℝ≥0)), 0)).re)
        ≤ ∫⁻ q, timeSliceDensity F t q ∂(bochnerMeasure fun a => F (0, a)) := by
      intro n
      rw [← hmass, ← Measure.lintegral_rnDeriv (hac _)]
      exact lintegral_mono fun q => rnDeriv_le_timeSliceDensity F (hr n) q
    have hFt : Tendsto (fun n => F (((r n : ℝ≥0)), 0)) atTop (𝓝 (F (t, 0))) :=
      (hFcont.tendsto (t, 0)).comp ((NNReal.tendsto_coe.1 hrt).prodMk_nhds tendsto_const_nhds)
    exact le_of_tendsto
      ((ENNReal.continuous_ofReal.tendsto _).comp ((Complex.continuous_re.tendsto _).comp hFt))
      (Eventually.of_forall hstep)
  refine ae_eq_of_ae_le_of_lintegral_le hle ?_
    (Measure.measurable_rnDeriv _ _).aemeasurable hint
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hle)
  rw [Measure.lintegral_rnDeriv (hac t)]
  exact measure_ne_top _ _

/-- Almost every fibre of the right-continuous density is normalized at time `0`. -/
theorem ae_timeSliceDensity_zero_eq_one (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (hFbdd : Bornology.IsBounded (range F)) :
    ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)), timeSliceDensity F 0 q = 1 := by
  filter_upwards [timeSliceDensity_ae_eq_rnDeriv hFpd hFcont hFbdd 0,
    Measure.rnDeriv_self (bochnerMeasure fun a => F (0, a))] with q h₁ h₂
  rw [h₁, h₂]

/-- **The right-continuous density is right-continuous in time.** No null set is involved: the
supremum defining it runs over the rational times to the right of `t`, so it is both antitone and
its own right limit. -/
theorem tendsto_timeSliceDensity_nhdsGT (F : ℝ≥0 × V → ℂ) (t : ℝ≥0) (q : V) :
    Tendsto (fun s => timeSliceDensity F s q) (𝓝[>] t) (𝓝 (timeSliceDensity F t q)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨r, hr⟩ := lt_iSup_iff.1 ha
    filter_upwards [Ioo_mem_nhdsGT r.2] with s hs
    exact hr.trans_le (rnDeriv_le_timeSliceDensity F hs.2 q)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (timeSliceDensity_antitone F q (mem_Ioi.1 hs).le).trans_lt hb

/-- The real-valued time profile of a fibre, reparametrized by a real time, is right-continuous
at every nonnegative time where its value is finite. -/
theorem tendsto_toReal_timeSliceDensity_nhdsGT (F : ℝ≥0 × V → ℂ) {q : V}
    {u : ℝ} (hq : timeSliceDensity F u.toNNReal q ≠ ⊤) (hu : 0 ≤ u) :
    Tendsto (fun s : ℝ => (timeSliceDensity F s.toNNReal q).toReal) (𝓝[>] u)
      (𝓝 ((timeSliceDensity F u.toNNReal q).toReal)) := by
  have htoNN : Tendsto (fun s : ℝ => s.toNNReal) (𝓝[>] u) (𝓝[>] u.toNNReal) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_real_toNNReal.tendsto u).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact mem_Ioi.2 ((Real.toNNReal_lt_toNNReal_iff_of_nonneg hu).2 (mem_Ioi.1 hs))
  exact (ENNReal.tendsto_toReal hq).comp ((tendsto_timeSliceDensity_nhdsGT F _ q).comp htoNN)

/-! ## Complete monotonicity of the fibres -/

/-- **Almost every fibre of the right-continuous density is completely monotone in the
finite-difference sense.** The mixed forward differences at rational data are densities of the
Bochner measures of the corresponding list time differences of `F`, hence nonnegative; rational
data suffice because the fibres are right-continuous
(`TauCeti.isDifferenceCompletelyMonotone_of_forall_rat`). -/
theorem ae_isDifferenceCompletelyMonotone_timeSliceDensity (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) :
    ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)),
      IsDifferenceCompletelyMonotone fun s : ℝ => (timeSliceDensity F s.toNNReal q).toReal := by
  have hfin : ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)), timeSliceDensity F 0 q ≠ ⊤ := by
    filter_upwards [ae_timeSliceDensity_zero_eq_one hFpd hFcont hFbdd] with q hq
    rw [hq]
    exact ENNReal.one_ne_top
  have hDd : ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)), ∀ r : ℚ, 0 ≤ r →
      timeSliceDensity F (Real.toNNReal (r : ℝ)) q
        = (bochnerMeasure fun a => F (Real.toNNReal (r : ℝ), a)).rnDeriv
            (bochnerMeasure fun a => F (0, a)) q := by
    refine ae_all_iff.2 fun r => ?_
    filter_upwards [timeSliceDensity_ae_eq_rnDeriv hFpd hFcont hFbdd
      (Real.toNNReal (r : ℝ))] with q hq _ using hq
  have hsign : ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)), ∀ p : List ℚ × ℚ,
      (∀ h ∈ p.1, 0 ≤ h) → 0 ≤ p.2 →
      0 ≤ (-1) ^ p.1.length * fwdDiffList (p.1.map (Rat.cast))
        (fun s : ℝ => ((bochnerMeasure fun a => F (s.toNNReal, a)).rnDeriv
          (bochnerMeasure fun a => F (0, a)) q).toReal) ((p.2 : ℝ)) := by
    refine ae_all_iff.2 fun p => ?_
    filter_upwards [toReal_rnDeriv_bochnerMeasure_timeSlice_listTimeDifference hFpd hFcont hFbdd
      (p.1.map fun r : ℚ => Real.toNNReal (r : ℝ)) (Real.toNNReal (p.2 : ℝ))] with q hq hl hs
    have hlist : (p.1.map fun r : ℚ => Real.toNNReal (r : ℝ)).map (fun h : ℝ≥0 => (h : ℝ))
        = p.1.map (Rat.cast) := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      exact Real.coe_toNNReal (r : ℝ) (by exact_mod_cast hl r hr)
    rw [hlist, List.length_map, Real.coe_toNNReal (p.2 : ℝ) (by exact_mod_cast hs)] at hq
    rw [← hq]
    exact ENNReal.toReal_nonneg
  filter_upwards [hfin, hDd, hsign] with q hq₁ hq₂ hq₃
  have hfin_at (u : ℝ) : timeSliceDensity F u.toNNReal q ≠ ⊤ :=
    ne_top_of_le_ne_top hq₁
      (timeSliceDensity_antitone F q (zero_le : (0 : ℝ≥0) ≤ u.toNNReal))
  refine isDifferenceCompletelyMonotone_of_forall_rat
    (fun u hu => tendsto_toReal_timeSliceDensity_nhdsGT F (hfin_at u) hu)
    fun l hl s hs => ?_
  have hcongr : fwdDiffList (l.map (Rat.cast))
        (fun s : ℝ => (timeSliceDensity F s.toNNReal q).toReal) ((s : ℝ))
      = fwdDiffList (l.map (Rat.cast))
        (fun s : ℝ => ((bochnerMeasure fun a => F (s.toNNReal, a)).rnDeriv
          (bochnerMeasure fun a => F (0, a)) q).toReal) ((s : ℝ)) := by
    refine fwdDiffList_congr_of_add_mem (S := {u : ℝ | ∃ r : ℚ, 0 ≤ r ∧ (r : ℝ) = u}) ?_
      ⟨s, hs, rfl⟩ ?_
    · rintro h hh u ⟨r, hr₀, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hh
      exact ⟨r + k, add_nonneg hr₀ (hl k hk), by push_cast; ring⟩
    · rintro u ⟨r, hr₀, rfl⟩
      rw [hq₂ r hr₀]
  rw [hcongr]
  exact hq₃ (l, s) hl hs

/-- **Almost every fibre of the right-continuous density is a completely monotone function of
time.** This is the hypothesis of `TauCeti.bernsteinMeasureKernel`, so almost every fibre carries a
Bernstein representing measure on `ℝ≥0`. -/
theorem ae_isContinuousCompletelyMonotoneOnIoi_timeSliceDensity (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) :
    ∀ᵐ q ∂(bochnerMeasure fun a => F (0, a)),
      IsContinuousCompletelyMonotoneOnIoi fun s : ℝ =>
        (timeSliceDensity F s.toNNReal q).toReal := by
  filter_upwards [ae_isDifferenceCompletelyMonotone_timeSliceDensity hFpd hFcont hFbdd,
    ae_timeSliceDensity_zero_eq_one hFpd hFcont hFbdd] with q hq hone
  refine hq.isContinuousCompletelyMonotoneOnIoi (continuousWithinAt_Ioi_iff_Ici.1 ?_)
  exact tendsto_toReal_timeSliceDensity_nhdsGT F
    (by simpa only [Real.toNNReal_zero, hone] using ENNReal.one_ne_top) le_rfl

end TauCeti

end

end
