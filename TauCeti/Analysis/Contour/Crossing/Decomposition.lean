/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.CapAngle
public import TauCeti.Analysis.Contour.Crossing.FiniteExcision
public import TauCeti.Analysis.Contour.Winding.Number.Concat

/-!
# Winding-number accounting for finitely many crossing excisions

Hungerbühler--Wasem Proposition 2.2 replaces finitely many pairwise disjoint crossing windows of
a closed piecewise-`C¹` immersion by circular caps. `Crossing.FiniteExcision` constructs a
simultaneously excised curve from a supplied list of windows, while `Crossing.CapAngle` computes
the winding number of a local loop under explicit geometric hypotheses. This file proves the
finite accounting identity

`n_s(γ) = n_s(exciseCrossings γ s windows) + ∑ localContribution`.

The proof partitions the curve at the window endpoints and compares the original and excised
curves piece by piece. Pairwise disjointness ensures that an earlier replacement does not change a
later window, so every local term in the final sum is computed on the original curve. The
conditional angle form merely substitutes caller-supplied local equalities. In particular, this
file does not construct windows from the actual crossings or discharge those equalities from
`windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi`; those are still needed to obtain the
full proposition.

For windows satisfying the additional geometric hypotheses, the integer part can be identified:
when the original curve is closed, the windows cover its crossings, and their cap endpoints agree
with the original curve, the first term is the winding number of the explicitly constructed closed
avoiding curve, hence is an integer.

## Main results

* `TauCeti.Contour.windingNumber_eq_exciseCrossings_add_sum`: exact winding accounting for a
  finite list of cap replacements.
* `TauCeti.Contour.windingNumber_eq_exciseCrossings_add_sum_crossingAngle_of_localContribution`:
  the conditional rewrite obtained when each local contribution is supplied as a crossing angle.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.

No external formalization is copied or adapted here; the proof composes Tau Ceti's finite-excision
and one-window winding APIs.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}

/-- The contribution of one circular-cap window: the winding number of the original curve across
the window minus the cap's angular term. Under the nondegeneracy hypotheses of
`localContribution_eq_sub_windingNumber_cap`, this is the window winding number minus the cap
winding number. -/
def CircularCapWindow.localContribution (W : CircularCapWindow) (γ : ℝ → ℂ) (s : ℂ) : ℂ :=
  windingNumber γ W.lower W.upper s -
    ((W.endAngle - W.startAngle : ℝ) : ℂ) / (2 * (Real.pi : ℂ))

/-- The defining window-minus-angular-term formula for a local contribution. -/
theorem CircularCapWindow.localContribution_def
    (W : CircularCapWindow) (γ : ℝ → ℂ) (s : ℂ) :
    W.localContribution γ s = windingNumber γ W.lower W.upper s -
      ((W.endAngle - W.startAngle : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [localContribution]

/-- The local contribution is the difference between the window winding number and the winding
number of the prescribed cap. -/
theorem CircularCapWindow.localContribution_eq_sub_windingNumber_cap
    (W : CircularCapWindow) (γ : ℝ → ℂ) (s : ℂ) (hr : W.radius ≠ 0)
    (hlu : W.lower ≠ W.upper) :
    W.localContribution γ s =
      windingNumber γ W.lower W.upper s - windingNumber (W.cap s) W.lower W.upper s := by
  rw [localContribution, W.windingNumber_cap s hr hlu]

/-- Pointwise congruence of the input curves is preserved by a fixed list of cap replacements. -/
private theorem exciseCrossings_apply_congr {γ δ : ℝ → ℂ} {s : ℂ}
    (windows : List CircularCapWindow) {t : ℝ} (h : γ t = δ t) :
    exciseCrossings γ s windows t = exciseCrossings δ s windows t := by
  induction windows generalizing γ δ with
  | nil => simpa only [exciseCrossings_nil] using h
  | cons W windows ih =>
      rw [exciseCrossings_cons, exciseCrossings_cons]
      apply ih
      by_cases ht : t ∈ W.interval
      · rw [W.excise_of_mem ht, W.excise_of_mem ht]
      · rw [W.excise_of_notMem ht, W.excise_of_notMem ht, h]

/-- Windows listed from left to right have pairwise disjoint closed intervals. -/
private theorem pairwise_disjoint_interval_of_pairwise_upper_lt_lower
    {windows : List CircularCapWindow}
    (hordered : windows.Pairwise fun W V => W.upper < V.lower) :
    windows.Pairwise fun W V => Disjoint W.interval V.interval := by
  induction windows with
  | nil => simp
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered ⊢
      refine ⟨fun V hV => Set.disjoint_left.mpr fun _ htW htV => ?_, ih hordered.2⟩
      rw [CircularCapWindow.mem_interval_iff] at htW htV
      linarith [hordered.1 V hV]

/-- Restrict piecewise regularity to the interval before the first window. -/
private theorem piecewiseC1On_left_of_inside (W : CircularCapWindow)
    (hγ : IsPiecewiseC1On γ a b) (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b) :
    IsPiecewiseC1On γ a W.lower := by
  apply hγ.mono
  rw [uIcc_of_le hW.1.le, uIcc_of_le (by linarith [hW.1, hW.2.1, hW.2.2] : a ≤ b)]
  exact Icc_subset_Icc_right (by linarith [hW.2.1, hW.2.2])

/-- Restrict piecewise regularity to the interval after the first window. -/
private theorem piecewiseC1On_tail_of_inside (W : CircularCapWindow)
    (hγ : IsPiecewiseC1On γ a b) (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b) :
    IsPiecewiseC1On γ W.upper b := by
  apply hγ.mono
  rw [uIcc_of_le hW.2.2.le, uIcc_of_le (by linarith [hW.1, hW.2.1, hW.2.2] : a ≤ b)]
  exact Icc_subset_Icc_left (by linarith [hW.1, hW.2.1])

/-- Avoidance off all ordered windows implies avoidance before the first window. -/
private theorem avoid_left_of_ordered_windows (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hordered : ∀ V ∈ windows, W.upper < V.lower)
    (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (havoid : ∀ t ∈ Icc a b,
      (∀ V ∈ W :: windows, t ∉ Ioo V.lower V.upper) → γ t ≠ s) :
    ∀ t ∈ uIcc a W.lower, γ t ≠ s := by
  rw [uIcc_of_le hW.1.le]
  intro t ht
  apply havoid t ⟨ht.1, by linarith [ht.2, hW.2.1, hW.2.2]⟩
  intro V hV
  rcases List.mem_cons.mp hV with rfl | hV
  · exact fun htIoo => (not_lt_of_ge ht.2) htIoo.1
  · exact fun htIoo => by linarith [ht.2, hordered V hV, htIoo.1]

/-- The windows after the head remain strictly inside the tail interval. -/
private theorem inside_tail_of_ordered_windows (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hordered : ∀ V ∈ windows, W.upper < V.lower)
    (hinside : ∀ V ∈ W :: windows,
      a < V.lower ∧ V.lower < V.upper ∧ V.upper < b) :
    ∀ V ∈ windows, W.upper < V.lower ∧ V.lower < V.upper ∧ V.upper < b := by
  intro V hV
  exact ⟨hordered V hV, (hinside V (List.mem_cons_of_mem W hV)).2⟩

/-- Avoidance off all ordered windows restricts to avoidance off the tail windows. -/
private theorem avoid_tail_of_ordered_windows (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (havoid : ∀ t ∈ Icc a b,
      (∀ V ∈ W :: windows, t ∉ Ioo V.lower V.upper) → γ t ≠ s) :
    ∀ t ∈ Icc W.upper b,
      (∀ V ∈ windows, t ∉ Ioo V.lower V.upper) → γ t ≠ s := by
  intro t ht hnot
  apply havoid t ⟨by linarith [hW.1, ht.1], ht.2⟩
  intro V hV
  rcases List.mem_cons.mp hV with rfl | hV
  · exact fun htIoo => (not_lt_of_ge ht.1) htIoo.2
  · exact hnot V hV

/-- Before the first ordered window, simultaneous excision agrees with the original curve. -/
private theorem eqOn_left_exciseCrossings_cons (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hordered : ∀ V ∈ windows, W.upper < V.lower) (haW : a < W.lower)
    (hlu : W.lower < W.upper) :
    EqOn γ (exciseCrossings γ s (W :: windows)) (uIoo a W.lower) := by
  intro t ht
  rw [uIoo_of_le haW.le] at ht
  exact (exciseCrossings_apply_of_forall_notMem fun V hV htV => by
    rw [CircularCapWindow.mem_interval_iff] at htV
    rcases List.mem_cons.mp hV with rfl | hV
    · linarith [ht.2, htV.1]
    · linarith [ht.2, hordered V hV, htV.1]).symm

/-- On the first ordered window, simultaneous excision agrees with its cap. -/
private theorem eqOn_window_exciseCrossings_cons (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hordered : (W :: windows).Pairwise fun U V => U.upper < V.lower)
    (hlu : W.lower < W.upper) :
    EqOn (W.cap s) (exciseCrossings γ s (W :: windows)) (uIoo W.lower W.upper) := by
  have hpw : (W :: windows).Pairwise fun U V => Disjoint U.interval V.interval :=
    pairwise_disjoint_interval_of_pairwise_upper_lt_lower hordered
  intro t ht
  rw [uIoo_of_le hlu.le] at ht
  exact (exciseCrossings_eqOn_window hpw List.mem_cons_self (by
    rw [CircularCapWindow.mem_interval_iff]
    exact ⟨ht.1.le, ht.2.le⟩)).symm

/-- After the first window, simultaneous excision agrees with excision by the tail. -/
private theorem eqOn_tail_exciseCrossings_cons (W : CircularCapWindow)
    (windows : List CircularCapWindow) (hWb : W.upper < b) :
    EqOn (exciseCrossings γ s windows) (exciseCrossings γ s (W :: windows))
      (uIoo W.upper b) := by
  intro t ht
  rw [uIoo_of_le hWb.le] at ht
  rw [exciseCrossings_cons]
  apply exciseCrossings_apply_congr
  exact (W.excise_of_notMem fun htW =>
    (not_lt_of_ge (CircularCapWindow.mem_interval_iff.mp htW).2) ht.1).symm

/-- The Cauchy-kernel principal value exists after gluing finitely many ordered crossing windows
to the point-avoiding pieces between them. -/
private theorem cauchyPVExistsAt_of_ordered_windows {windows : List CircularCapWindow}
    (hγ : IsPiecewiseC1On γ a b) (hab : a ≤ b)
    (hordered : windows.Pairwise fun W V => W.upper < V.lower)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (havoid : ∀ t ∈ Icc a b,
      (∀ W ∈ windows, t ∉ Ioo W.lower W.upper) → γ t ≠ s)
    (hpv : ∀ W ∈ windows,
      CauchyPVExistsAt γ W.lower W.upper (fun z => (z - s)⁻¹) s) :
    CauchyPVExistsAt γ a b (fun z => (z - s)⁻¹) s := by
  induction windows generalizing a γ with
  | nil =>
      have hγavoid : ∀ t ∈ uIcc a b, γ t ≠ s := by
        rw [uIcc_of_le hab]
        exact fun t ht => havoid t ht (by simp)
      exact cauchyPVExistsAt_of_avoidance hγ.continuousOn hγavoid
        (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hγavoid
          hγ.intervalIntegrable_deriv)
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered
      have hW := hinside W List.mem_cons_self
      have hleft := piecewiseC1On_left_of_inside W hγ hW
      have hleftAvoid := avoid_left_of_ordered_windows W hordered.1 hW havoid
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_of_avoidance hleft.continuousOn hleftAvoid
          (intervalIntegrable_inv_sub_mul_deriv hleft.continuousOn hleftAvoid
            hleft.intervalIntegrable_deriv)
      have htail := piecewiseC1On_tail_of_inside W hγ hW
      have hinsideTail := inside_tail_of_ordered_windows W hordered.1 hinside
      have havoidTail := avoid_tail_of_ordered_windows W hW havoid
      exact hpvLeft.concat <| (hpv W List.mem_cons_self).concat <|
        ih htail (by linarith [hW.2.2]) hordered.2 hinsideTail havoidTail
          (fun V hV => hpv V (List.mem_cons_of_mem W hV))

/-- The Cauchy-kernel principal value along the finitely excised curve is obtained by gluing the
original point-avoiding gaps to the circular caps. -/
private theorem cauchyPVExistsAt_exciseCrossings_of_ordered_windows
    {windows : List CircularCapWindow} (hγ : IsPiecewiseC1On γ a b) (hab : a ≤ b)
    (hordered : windows.Pairwise fun W V => W.upper < V.lower)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (havoid : ∀ t ∈ Icc a b,
      (∀ W ∈ windows, t ∉ Ioo W.lower W.upper) → γ t ≠ s) :
    CauchyPVExistsAt (exciseCrossings γ s windows) a b (fun z => (z - s)⁻¹) s := by
  induction windows generalizing a γ with
  | nil =>
      have hγavoid : ∀ t ∈ uIcc a b, γ t ≠ s := by
        rw [uIcc_of_le hab]
        exact fun t ht => havoid t ht (by simp)
      simpa only [exciseCrossings_nil] using
        cauchyPVExistsAt_of_avoidance hγ.continuousOn hγavoid
          (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn hγavoid
            hγ.intervalIntegrable_deriv)
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered
      have hW := hinside W List.mem_cons_self
      have hleft := piecewiseC1On_left_of_inside W hγ hW
      have hleftAvoid := avoid_left_of_ordered_windows W hordered.1 hW havoid
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_of_avoidance hleft.continuousOn hleftAvoid
          (intervalIntegrable_inv_sub_mul_deriv hleft.continuousOn hleftAvoid
            hleft.intervalIntegrable_deriv)
      have htail := piecewiseC1On_tail_of_inside W hγ hW
      have hinsideTail := inside_tail_of_ordered_windows W hordered.1 hinside
      have havoidTail := avoid_tail_of_ordered_windows W hW havoid
      have hpvTail := ih htail (by linarith [hW.2.2]) hordered.2 hinsideTail havoidTail
      let excised := exciseCrossings γ s (W :: windows)
      have heqLeft : EqOn γ excised (uIoo a W.lower) :=
        eqOn_left_exciseCrossings_cons W hordered.1 hW.1 hW.2.1
      have heqWindow : EqOn (W.cap s) excised (uIoo W.lower W.upper) :=
        eqOn_window_exciseCrossings_cons W
          (List.pairwise_cons.mpr ⟨hordered.1, hordered.2⟩) hW.2.1
      have heqTail : EqOn (exciseCrossings γ s windows) excised (uIoo W.upper b) :=
        eqOn_tail_exciseCrossings_cons W windows hW.2.2
      exact (hpvLeft.congr_curve heqLeft).concat <|
        ((W.cauchyPVExistsAt_cap s W.lower W.upper).congr_curve heqWindow).concat <|
          hpvTail.congr_curve heqTail

/-- **Finite crossing excision decomposes the winding number.** Replacing disjoint windows,
listed from left to right, of a piecewise-`C¹` curve by nonzero-radius circular caps
changes its winding number by the sum of the local window-minus-cap contributions.

The original curve need not be closed and the windows need not contain crossings. The hypotheses
state exactly what makes the surgery and the principal values well-defined: the windows lie
strictly inside `[a, b]`, the curve avoids `s` off their open interiors, and the Cauchy-kernel
principal value exists on each window. Endpoint values do not affect this winding identity;
matching endpoints are instead needed when applying the regularity results for the excised
curve. -/
theorem windingNumber_eq_exciseCrossings_add_sum {windows : List CircularCapWindow}
    (hγ : IsPiecewiseC1On γ a b)
    (hordered : windows.Pairwise fun W V => W.upper < V.lower)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (hr : ∀ W ∈ windows, W.radius ≠ 0)
    (havoid : ∀ t ∈ Icc a b,
      (∀ W ∈ windows, t ∉ Ioo W.lower W.upper) → γ t ≠ s)
    (hpv : ∀ W ∈ windows,
      CauchyPVExistsAt γ W.lower W.upper (fun z => (z - s)⁻¹) s) :
    windingNumber γ a b s = windingNumber (exciseCrossings γ s windows) a b s +
      (windows.map fun W => W.localContribution γ s).sum := by
  induction windows generalizing a γ with
  | nil => simp
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered
      have hW := hinside W List.mem_cons_self
      have hrW := hr W List.mem_cons_self
      have htail := piecewiseC1On_tail_of_inside W hγ hW
      have hinsideTail := inside_tail_of_ordered_windows W hordered.1 hinside
      have havoidTail := avoid_tail_of_ordered_windows W hW havoid
      have htailEq := ih htail hordered.2 hinsideTail
        (fun V hV => hr V (List.mem_cons_of_mem W hV))
        havoidTail
        (fun V hV => hpv V (List.mem_cons_of_mem W hV))
      have hleft := piecewiseC1On_left_of_inside W hγ hW
      have hleftAvoid := avoid_left_of_ordered_windows W hordered.1 hW havoid
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_of_avoidance hleft.continuousOn hleftAvoid
          (intervalIntegrable_inv_sub_mul_deriv hleft.continuousOn hleftAvoid
            hleft.intervalIntegrable_deriv)
      have hpvW := hpv W List.mem_cons_self
      have hpvTail := cauchyPVExistsAt_of_ordered_windows htail (by linarith [hW.2.2])
        hordered.2 hinsideTail
        havoidTail (fun V hV => hpv V (List.mem_cons_of_mem W hV))
      have hpvTailExc : CauchyPVExistsAt (exciseCrossings γ s windows) W.upper b
          (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_exciseCrossings_of_ordered_windows htail
          (by linarith [hW.2.2]) hordered.2 hinsideTail havoidTail
      let excised := exciseCrossings γ s (W :: windows)
      -- Compare the original and excised curves on the left gap, head window, and tail.
      have heqLeft : EqOn γ excised (uIoo a W.lower) :=
        eqOn_left_exciseCrossings_cons W hordered.1 hW.1 hW.2.1
      have heqWindow : EqOn (W.cap s) excised (uIoo W.lower W.upper) :=
        eqOn_window_exciseCrossings_cons W
          (List.pairwise_cons.mpr ⟨hordered.1, hordered.2⟩) hW.2.1
      have heqTail : EqOn (exciseCrossings γ s windows) excised (uIoo W.upper b) :=
        eqOn_tail_exciseCrossings_cons W windows hW.2.2
      have hpvExcLeft := hpvLeft.congr_curve heqLeft
      have hpvExcWindow :=
        (W.cauchyPVExistsAt_cap s W.lower W.upper).congr_curve heqWindow
      have hpvExcTail := hpvTailExc.congr_curve heqTail
      have hsplit : windingNumber γ a b s = windingNumber γ a W.lower s +
          windingNumber γ W.lower W.upper s + windingNumber γ W.upper b s := by
        rw [windingNumber_concat hpvLeft (hpvW.concat hpvTail),
          windingNumber_concat hpvW hpvTail]
        ring
      have hsplitExc : windingNumber excised a b s = windingNumber γ a W.lower s +
          windingNumber (W.cap s) W.lower W.upper s +
            windingNumber (exciseCrossings γ s windows) W.upper b s := by
        rw [windingNumber_concat hpvExcLeft (hpvExcWindow.concat hpvExcTail),
          windingNumber_concat hpvExcWindow hpvExcTail,
          ← windingNumber_congr_curve heqLeft, ← windingNumber_congr_curve heqWindow,
          ← windingNumber_congr_curve heqTail]
        ring
      rw [List.map_cons, List.sum_cons, hsplit, hsplitExc, htailEq,
        W.localContribution_eq_sub_windingNumber_cap γ s hrW hW.2.1.ne]
      ring

/-- **Conditional crossing-angle summation for supplied windows.** If the window-minus-cap
contribution is supplied as a crossing angle over `2π` for every window, then the finite excision
identity rewrites as the sum of those angles.

Here `crossingParameter` is only an indexing function and `hlocal` assumes the essential local
geometric equality. This lemma neither constructs windows around the actual crossings nor derives
`hlocal` from `windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi`; consequently it is an
assembly lemma toward, rather than a formalization of, Hungerbühler--Wasem Proposition 2.2. -/
theorem windingNumber_eq_exciseCrossings_add_sum_crossingAngle_of_localContribution
    {windows : List CircularCapWindow} (crossingParameter : CircularCapWindow → ℝ)
    (hγ : IsPiecewiseC1On γ a b)
    (hordered : windows.Pairwise fun W V => W.upper < V.lower)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (hr : ∀ W ∈ windows, W.radius ≠ 0)
    (havoid : ∀ t ∈ Icc a b,
      (∀ W ∈ windows, t ∉ Ioo W.lower W.upper) → γ t ≠ s)
    (hpv : ∀ W ∈ windows,
      CauchyPVExistsAt γ W.lower W.upper (fun z => (z - s)⁻¹) s)
    (hlocal : ∀ W ∈ windows, W.localContribution γ s =
      (crossingAngle γ (crossingParameter W) : ℂ) / (2 * (Real.pi : ℂ))) :
    windingNumber γ a b s = windingNumber (exciseCrossings γ s windows) a b s +
      (((windows.map fun W => crossingAngle γ (crossingParameter W)).sum : ℝ) : ℂ) /
        (2 * (Real.pi : ℂ)) := by
  have hdecomp := windingNumber_eq_exciseCrossings_add_sum hγ hordered hinside hr havoid hpv
  have hsum : (windows.map fun W => W.localContribution γ s).sum =
      (((windows.map fun W => crossingAngle γ (crossingParameter W)).sum : ℝ) : ℂ) /
        (2 * (Real.pi : ℂ)) := by
    have hsumAux : ∀ ws : List CircularCapWindow,
        (∀ W ∈ ws, W.localContribution γ s =
          (crossingAngle γ (crossingParameter W) : ℂ) / (2 * (Real.pi : ℂ))) →
        (ws.map fun W => W.localContribution γ s).sum =
          (((ws.map fun W => crossingAngle γ (crossingParameter W)).sum : ℝ) : ℂ) /
            (2 * (Real.pi : ℂ)) := by
      intro ws hws
      induction ws with
      | nil => simp
      | cons W ws ih =>
          rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
            hws W List.mem_cons_self,
            ih (fun V hV => hws V (List.mem_cons_of_mem W hV))]
          push_cast
          ring
    exact hsumAux windows hlocal
  rw [hdecomp, hsum]

end TauCeti.Contour

end
