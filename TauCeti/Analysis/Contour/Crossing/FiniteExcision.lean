/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Excision

/-!
# Simultaneous excision of finitely many crossing windows

Hungerbühler–Wasem Proposition 2.2 replaces every crossing of a closed piecewise-`C¹`
immersion by a circular cap. `Crossing.Excision` constructs this replacement for one window;
this file iterates that construction over a finite list of pairwise disjoint windows.

`CircularCapWindow` records the five parameters of one replacement. Applying
`exciseCrossings` to a pairwise disjoint list has the expected simultaneous description: it is
the prescribed cap on each window and the original curve off their union. Consequently the
result remains piecewise `C¹` and closed, and it avoids the crossing centre when the windows
cover every parameter at which the original curve meets that centre.

This is the finite geometric surgery producing the modified curve in Proposition 2.2. The winding
number accounting is deliberately separate: `Winding.Number.Partition` supplies finite
additivity, while the local crossing contribution is computed by the crossing-angle theory.

## Main definitions

* `TauCeti.Contour.CircularCapWindow` — the parameters of one circular-cap replacement.
* `TauCeti.Contour.exciseCrossings` — iteration of `exciseCrossing` over a finite list.

## Main results

* `TauCeti.Contour.exciseCrossings_eqOn_window` and
  `TauCeti.Contour.exciseCrossings_eqOn_compl` — the simultaneous pointwise description.
* `TauCeti.Contour.IsPiecewiseC1On.exciseCrossings` — finite excision preserves piecewise
  `C¹` regularity.
* `TauCeti.Contour.exciseCrossings_closed` — finite excision preserves closedness.
* `TauCeti.Contour.exciseCrossings_ne_center` — the resulting curve avoids the centre when
  the windows cover every crossing.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.2.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Set

/-- The parameters of a circular cap replacing one crossing window. Every field contributes to
the replacement: `lower` and `upper` delimit the window, `radius` is the signed radial scale,
and `startAngle` and `endAngle` specify the cap's angular sweep. -/
structure CircularCapWindow where
  /-- Signed radial scale of the cap. -/
  radius : ℝ
  /-- Lower endpoint of the parameter window. -/
  lower : ℝ
  /-- Upper endpoint of the parameter window. -/
  upper : ℝ
  /-- Angle of the cap at the lower endpoint. -/
  startAngle : ℝ
  /-- Angle of the cap at the upper endpoint. -/
  endAngle : ℝ

namespace CircularCapWindow

/-- The closed parameter interval replaced by a circular cap. -/
def interval (W : CircularCapWindow) : Set ℝ := Icc W.lower W.upper

/-- The circular cap prescribed by a crossing window. -/
def cap (W : CircularCapWindow) (s : ℂ) : ℝ → ℂ :=
  circleCap s W.radius W.lower W.upper W.startAngle W.endAngle

/-- Replace one crossing window of `γ` by its prescribed circular cap about `s`. -/
def excise (W : CircularCapWindow) (γ : ℝ → ℂ) (s : ℂ) : ℝ → ℂ :=
  exciseCrossing γ s W.radius W.lower W.upper W.startAngle W.endAngle

/-- On its window, a one-window excision is the prescribed cap. -/
@[simp]
theorem excise_of_mem (W : CircularCapWindow) {γ : ℝ → ℂ} {s : ℂ} {t : ℝ}
    (ht : t ∈ W.interval) : W.excise γ s t = W.cap s t :=
  exciseCrossing_of_mem ht

/-- Off its window, a one-window excision is the original curve. -/
@[simp]
theorem excise_of_notMem (W : CircularCapWindow) {γ : ℝ → ℂ} {s : ℂ} {t : ℝ}
    (ht : t ∉ W.interval) : W.excise γ s t = γ t :=
  exciseCrossing_of_notMem ht

end CircularCapWindow

/-- Replace each window in `windows` by its circular cap about `s`. Later replacements act on
the curve produced by earlier ones. For pairwise disjoint windows the order is immaterial
pointwise, and `exciseCrossings_eqOn_window` gives the simultaneous description. -/
def exciseCrossings (γ : ℝ → ℂ) (s : ℂ) : List CircularCapWindow → ℝ → ℂ
  | [] => γ
  | W :: windows => exciseCrossings (W.excise γ s) s windows

/-- Away from every window, finite excision agrees with the original curve. -/
theorem exciseCrossings_eqOn_compl {γ : ℝ → ℂ} {s : ℂ}
    {windows : List CircularCapWindow} {S : Set ℝ}
    (hdisj : ∀ W ∈ windows, Disjoint S W.interval) :
    EqOn (exciseCrossings γ s windows) γ S := by
  induction windows generalizing γ with
  | nil => exact fun _ _ => rfl
  | cons W windows ih =>
      have hW : Disjoint S W.interval := hdisj W List.mem_cons_self
      have htail : ∀ V ∈ windows, Disjoint S V.interval :=
        fun V hV => hdisj V (List.mem_cons_of_mem W hV)
      intro t ht
      rw [exciseCrossings]
      calc
        exciseCrossings (W.excise γ s) s windows t = W.excise γ s t := ih htail ht
        _ = γ t := W.excise_of_notMem fun htW => Set.disjoint_left.mp hW ht htW

/-- Pointwise form of `exciseCrossings_eqOn_compl`. -/
theorem exciseCrossings_apply_of_forall_notMem {γ : ℝ → ℂ} {s : ℂ}
    {windows : List CircularCapWindow} {t : ℝ} (ht : ∀ W ∈ windows, t ∉ W.interval) :
    exciseCrossings γ s windows t = γ t := by
  exact exciseCrossings_eqOn_compl
    (S := {t}) (fun W hW => Set.disjoint_left.mpr fun _ ht' htW => ht W hW (ht' ▸ htW))
    (Set.mem_singleton t)

/-- For pairwise disjoint windows, finite excision is the prescribed cap on each window. -/
theorem exciseCrossings_eqOn_window {γ : ℝ → ℂ} {s : ℂ}
    {windows : List CircularCapWindow} (hpw : windows.Pairwise fun W V =>
      Disjoint W.interval V.interval) {W : CircularCapWindow} (hW : W ∈ windows) :
    EqOn (exciseCrossings γ s windows) (W.cap s) W.interval := by
  induction windows generalizing γ with
  | nil => simp at hW
  | cons V windows ih =>
      rw [List.pairwise_cons] at hpw
      rcases List.mem_cons.mp hW with rfl | hW
      · rw [exciseCrossings]
        refine (exciseCrossings_eqOn_compl
          (γ := CircularCapWindow.excise W γ s) (s := s) ?_).trans ?_
        · intro U hU
          exact hpw.1 U hU
        · exact fun _ ht => W.excise_of_mem ht
      · rw [exciseCrossings]
        exact ih hpw.2 hW

/-- Pairwise-disjoint finite excision is independent of the ordering of the windows. -/
theorem exciseCrossings_perm {γ : ℝ → ℂ} {s : ℂ}
    {windows windows' : List CircularCapWindow}
    (hpw : windows.Pairwise fun W V => Disjoint W.interval V.interval)
    (hperm : windows.Perm windows') :
    exciseCrossings γ s windows = exciseCrossings γ s windows' := by
  funext t
  by_cases ht : ∃ W ∈ windows, t ∈ W.interval
  · obtain ⟨W, hW, htW⟩ := ht
    have hpw' : windows'.Pairwise fun U V => Disjoint U.interval V.interval :=
      hpw.perm hperm fun h => h.symm
    rw [exciseCrossings_eqOn_window hpw hW htW,
      exciseCrossings_eqOn_window hpw' (hperm.mem_iff.mp hW) htW]
  · rw [exciseCrossings_apply_of_forall_notMem (fun W hW htW => ht ⟨W, hW, htW⟩),
      exciseCrossings_apply_of_forall_notMem (fun W hW htW =>
        ht ⟨W, hperm.mem_iff.mpr hW, htW⟩)]

/-- Finite excision preserves piecewise-`C¹` regularity when the windows are pairwise disjoint,
strictly inside the parameter interval, and their cap endpoints agree with the original curve. -/
theorem IsPiecewiseC1On.exciseCrossings {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {windows : List CircularCapWindow} (hγ : IsPiecewiseC1On γ a b)
    (hpw : windows.Pairwise fun W V => Disjoint W.interval V.interval)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b)
    (hstart : ∀ W ∈ windows, γ W.lower = circleMap s W.radius W.startAngle)
    (hend : ∀ W ∈ windows, γ W.upper = circleMap s W.radius W.endAngle) :
    IsPiecewiseC1On (exciseCrossings γ s windows) a b := by
  induction windows generalizing γ with
  | nil => exact hγ
  | cons W windows ih =>
      rw [List.pairwise_cons] at hpw
      have hW := hinside W List.mem_cons_self
      have hfirst : IsPiecewiseC1On (W.excise γ s) a b :=
        hγ.exciseCrossing hW.1 hW.2.1 hW.2.2
          (hstart W List.mem_cons_self) (hend W List.mem_cons_self)
      refine ih hfirst hpw.2 (fun V hV => hinside V (List.mem_cons_of_mem W hV)) ?_ ?_
      · intro V hV
        rw [W.excise_of_notMem]
        · exact hstart V (List.mem_cons_of_mem W hV)
        · exact fun hmem => Set.disjoint_left.mp (hpw.1 V hV) hmem
            (left_mem_Icc.mpr (hinside V (List.mem_cons_of_mem W hV)).2.1.le)
      · intro V hV
        rw [W.excise_of_notMem]
        · exact hend V (List.mem_cons_of_mem W hV)
        · exact fun hmem => Set.disjoint_left.mp (hpw.1 V hV) hmem
            (right_mem_Icc.mpr (hinside V (List.mem_cons_of_mem W hV)).2.1.le)

/-- Finite excision preserves closedness when every replacement window lies strictly inside the
parameter interval. -/
theorem exciseCrossings_closed {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {windows : List CircularCapWindow} (hclosed : γ a = γ b)
    (hinside : ∀ W ∈ windows, a < W.lower ∧ W.upper < b) :
    exciseCrossings γ s windows a = exciseCrossings γ s windows b := by
  rw [exciseCrossings_apply_of_forall_notMem (fun W hW hmem =>
      (not_le.mpr (hinside W hW).1) hmem.1),
    exciseCrossings_apply_of_forall_notMem (fun W hW hmem =>
      (not_le.mpr (hinside W hW).2) hmem.2), hclosed]

/-- If pairwise disjoint open windows cover every parameter where `γ` meets `s`, replacing all
of them by nonzero-radius caps produces a curve avoiding `s`. -/
theorem exciseCrossings_ne_center {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {windows : List CircularCapWindow}
    (hpw : windows.Pairwise fun W V => Disjoint W.interval V.interval)
    (hr : ∀ W ∈ windows, W.radius ≠ 0)
    (hcover : ∀ t ∈ Icc a b, γ t = s → ∃ W ∈ windows, t ∈ Ioo W.lower W.upper) :
    ∀ t ∈ Icc a b, exciseCrossings γ s windows t ≠ s := by
  intro t ht
  by_cases hmem : ∃ W ∈ windows, t ∈ W.interval
  · obtain ⟨W, hW, htW⟩ := hmem
    rw [exciseCrossings_eqOn_window hpw hW htW, CircularCapWindow.cap]
    exact circleCap_ne_center (hr W hW)
  · rw [exciseCrossings_apply_of_forall_notMem
      (fun W hW htW => hmem ⟨W, hW, htW⟩)]
    intro hγt
    obtain ⟨W, hW, htW⟩ := hcover t ht hγt
    exact hmem ⟨W, hW, Ioo_subset_Icc_self htW⟩

end TauCeti.Contour

end
