/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.FiniteExcision
public import TauCeti.Analysis.Contour.Winding.Number.Concat
import TauCeti.Analysis.Contour.Winding.Integer

/-!
# Winding-number accounting for finitely many crossing excisions

Hungerbühler--Wasem Proposition 2.2 replaces finitely many crossing windows of a closed
piecewise-`C¹` immersion by circular caps. `Crossing.FiniteExcision` constructs a simultaneously
excised curve from a supplied list of windows. This file proves the finite accounting identity

`n_s(γ) = n_s(exciseCrossings γ s windows) + ∑ localContribution`.

The proof partitions the curve at the window endpoints and compares the original and excised
curves piece by piece. The windows must be listed in strictly increasing order: every earlier
window satisfies `W.upper < V.lower` for every later window. Pairwise disjointness alone does not
suffice for the recursive left-to-right accounting. The ordering ensures that an earlier
replacement does not change a later window, so every local term is computed on the original curve.

This file does not construct windows from the actual crossings or identify their local
contributions with crossing angles; those geometric steps remain downstream inputs to the full
proposition.

## Main results

* `TauCeti.Contour.windingNumber_eq_exciseCrossings_add_sum`: exact winding accounting for a
  finite list of cap replacements.
* `TauCeti.Contour.windingNumber_eq_exciseCrossing_add`: the one-window specialization.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.

## Provenance

Independently reconstructed; no formalization is vendored. The `ContourIntegration` roadmap
designates the AINTLIB `LeanModularForms` development
([github.com/CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB), Apache-2.0) as the existing
source for this area. Its `ForMathlib/HungerbuhlerWasem/Crossing.lean` and
`ForMathlib/HungerbuhlerWasem/MultiCrossingCPV.lean` were consulted at revision `340875a`.
The former supplies sector geometry and the latter a multi-crossing principal-value engine; neither
contains this excise-and-cap winding-number accounting identity. The proof below instead composes
Tau Ceti's finite-excision, concatenation, cap, and winding-number APIs.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

variable {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}

/-- A piecewise-`C¹` curve avoiding the centre has the Cauchy-kernel principal value. -/
private theorem IsPiecewiseC1On.cauchyPVExistsAt_inv_sub_of_avoidance
    (hγ : IsPiecewiseC1On γ a b) (havoid : ∀ t ∈ uIcc a b, γ t ≠ s) :
    CauchyPVExistsAt γ a b (fun z => (z - s)⁻¹) s :=
  cauchyPVExistsAt_of_avoidance hγ.continuousOn havoid
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn havoid
      hγ.intervalIntegrable_deriv)

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

/-- Restrict piecewise regularity to the interval before the first window. -/
private theorem isPiecewiseC1On_left_of_inside (W : CircularCapWindow)
    (hγ : IsPiecewiseC1On γ a b) (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b) :
    IsPiecewiseC1On γ a W.lower := by
  apply hγ.mono
  rw [uIcc_of_le hW.1.le, uIcc_of_le (by linarith [hW.1, hW.2.1, hW.2.2] : a ≤ b)]
  exact Icc_subset_Icc_right (by linarith [hW.2.1, hW.2.2])

/-- Restrict piecewise regularity to the interval after the first window. -/
private theorem isPiecewiseC1On_tail_of_inside (W : CircularCapWindow)
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

/-- The original curve has the Cauchy-kernel principal value on the gap before the first ordered
window. -/
private theorem cauchyPVExistsAt_left_of_ordered_windows (W : CircularCapWindow)
    {windows : List CircularCapWindow}
    (hγ : IsPiecewiseC1On γ a b) (hordered : ∀ V ∈ windows, W.upper < V.lower)
    (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (havoid : ∀ t ∈ Icc a b,
      (∀ V ∈ W :: windows, t ∉ Ioo V.lower V.upper) → γ t ≠ s) :
    CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
  (isPiecewiseC1On_left_of_inside W hγ hW).cauchyPVExistsAt_inv_sub_of_avoidance
    (avoid_left_of_ordered_windows W hordered hW havoid)

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

/-- Simultaneous excision agrees with the original left gap, the head cap, and tail excision on
the three consecutive open pieces determined by the first ordered window. -/
private theorem eqOn_pieces_exciseCrossings_cons (W : CircularCapWindow)
    (windows : List CircularCapWindow)
    (hordered : (W :: windows).Pairwise fun U V => U.upper < V.lower)
    (hW : a < W.lower ∧ W.lower < W.upper ∧ W.upper < b) :
    EqOn γ (exciseCrossings γ s (W :: windows)) (uIoo a W.lower) ∧
      EqOn (W.cap s) (exciseCrossings γ s (W :: windows)) (uIoo W.lower W.upper) ∧
        EqOn (exciseCrossings γ s windows) (exciseCrossings γ s (W :: windows))
          (uIoo W.upper b) := by
  rw [List.pairwise_cons] at hordered
  exact ⟨eqOn_left_exciseCrossings_cons W hordered.1 hW.1 hW.2.1,
    eqOn_window_exciseCrossings_cons W (List.pairwise_cons.mpr hordered) hW.2.1,
    eqOn_tail_exciseCrossings_cons W windows hW.2.2⟩

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
      exact hγ.cauchyPVExistsAt_inv_sub_of_avoidance hγavoid
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered
      have hW := hinside W List.mem_cons_self
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_left_of_ordered_windows W hγ hordered.1 hW havoid
      have htail := isPiecewiseC1On_tail_of_inside W hγ hW
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
        hγ.cauchyPVExistsAt_inv_sub_of_avoidance hγavoid
  | cons W windows ih =>
      rw [List.pairwise_cons] at hordered
      have hW := hinside W List.mem_cons_self
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_left_of_ordered_windows W hγ hordered.1 hW havoid
      have htail := isPiecewiseC1On_tail_of_inside W hγ hW
      have hinsideTail := inside_tail_of_ordered_windows W hordered.1 hinside
      have havoidTail := avoid_tail_of_ordered_windows W hW havoid
      have hpvTail := ih htail (by linarith [hW.2.2]) hordered.2 hinsideTail havoidTail
      let excised := exciseCrossings γ s (W :: windows)
      obtain ⟨heqLeft, heqWindow, heqTail⟩ :=
        eqOn_pieces_exciseCrossings_cons W windows
          (List.pairwise_cons.mpr ⟨hordered.1, hordered.2⟩) hW
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
      have htail := isPiecewiseC1On_tail_of_inside W hγ hW
      have hinsideTail := inside_tail_of_ordered_windows W hordered.1 hinside
      have havoidTail := avoid_tail_of_ordered_windows W hW havoid
      have htailEq := ih htail hordered.2 hinsideTail
        (fun V hV => hr V (List.mem_cons_of_mem W hV))
        havoidTail
        (fun V hV => hpv V (List.mem_cons_of_mem W hV))
      have hpvLeft : CauchyPVExistsAt γ a W.lower (fun z => (z - s)⁻¹) s :=
        cauchyPVExistsAt_left_of_ordered_windows W hγ hordered.1 hW havoid
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
      obtain ⟨heqLeft, heqWindow, heqTail⟩ :=
        eqOn_pieces_exciseCrossings_cons W windows
          (List.pairwise_cons.mpr ⟨hordered.1, hordered.2⟩) hW
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

/-- **Excising one crossing decomposes the winding number.** This is the singleton-window
specialization of `windingNumber_eq_exciseCrossings_add_sum`. The curve need not be closed and no
endpoint conditions relating it to the cap are needed, because winding numbers are insensitive to
endpoint values. -/
theorem windingNumber_eq_exciseCrossing_add {l u r θ θ' : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hal : a < l) (hlu : l < u) (hub : u < b) (hr : r ≠ 0)
    (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s)
    (hpv : CauchyPVExistsAt γ l u (fun z => (z - s)⁻¹) s) :
    windingNumber γ a b s
      = windingNumber (exciseCrossing γ s r l u θ θ') a b s
        + (windingNumber γ l u s - ((θ' - θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) := by
  let W : CircularCapWindow := ⟨r, l, u, θ, θ'⟩
  have hinside : ∀ V ∈ [W], a < V.lower ∧ V.lower < V.upper ∧ V.upper < b := by
    intro V hV
    simp only [List.mem_singleton] at hV
    subst V
    exact ⟨hal, hlu, hub⟩
  have hradius : ∀ V ∈ [W], V.radius ≠ 0 := by
    intro V hV
    simp only [List.mem_singleton] at hV
    subst V
    exact hr
  have havoid' : ∀ t ∈ Icc a b,
      (∀ V ∈ [W], t ∉ Ioo V.lower V.upper) → γ t ≠ s := by
    intro t ht hnot
    exact havoid t ht (hnot W (by simp))
  have hpv' : ∀ V ∈ [W],
      CauchyPVExistsAt γ V.lower V.upper (fun z => (z - s)⁻¹) s := by
    intro V hV
    simp only [List.mem_singleton] at hV
    subst V
    exact hpv
  have hmain := windingNumber_eq_exciseCrossings_add_sum (windows := [W]) hγ
    (by simp) hinside hradius havoid' hpv'
  simpa only [exciseCrossings_cons, exciseCrossings_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, W, CircularCapWindow.excise_def,
    CircularCapWindow.localContribution_def] using hmain

/-- **One-window integrality consequence of crossing excision.** Under the hypotheses of
`windingNumber_eq_exciseCrossing_add` on a closed curve, its winding number is an integer plus the
window's local contribution. This is not yet Hungerbühler--Wasem Proposition 2.2: that proposition
also requires identifying the local contribution with the crossing angle. The witness here is the
winding number of the closed, point-avoiding excised curve. -/
theorem exists_int_windingNumber_eq_add_windingNumber_sub_angle_div_two_pi
    {l u r θ θ' : ℝ} (hγ : IsPiecewiseC1On γ a b) (hal : a < l)
    (hlu : l < u) (hub : u < b) (hr : r ≠ 0) (hclosed : γ a = γ b)
    (hθ : γ l = circleMap s r θ) (hθ' : γ u = circleMap s r θ')
    (havoid : ∀ t ∈ Icc a b, t ∉ Ioo l u → γ t ≠ s)
    (hpv : CauchyPVExistsAt γ l u (fun z => (z - s)⁻¹) s) :
    ∃ k : ℤ, windingNumber γ a b s
      = k + (windingNumber γ l u s - ((θ' - θ : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) := by
  have hab : a ≤ b := by linarith
  have hE := hγ.exciseCrossing hal hlu hub hθ hθ'
  obtain ⟨k, hk⟩ := hE.exists_int_windingNumber (exciseCrossing_closed hal hub hclosed θ θ')
    (fun t ht => exciseCrossing_ne_center hr θ θ' havoid t ((uIcc_of_le hab) ▸ ht))
  exact ⟨k, by rw [windingNumber_eq_exciseCrossing_add hγ hal hlu hub hr havoid hpv, hk]⟩

end TauCeti.Contour

end
