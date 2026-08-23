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
the prescribed cap on each window and the original curve off their union. It remains piecewise
`C¹` when the windows lie strictly inside the parameter interval and their cap endpoints match
the original curve, and remains closed when the interval endpoints lie outside every window.
Without a disjointness assumption, it avoids the crossing centre on `Icc a b` when every window
meeting that interval has nonzero radius and the windows cover every parameter there at which the
original curve meets that centre.

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
* `TauCeti.Contour.exciseCrossings_ne_center` — the resulting curve avoids the centre on
  `Icc a b` when the windows cover every crossing there.

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

/-- Membership in a window is membership in its closed endpoint interval. -/
@[simp]
theorem mem_interval_iff {W : CircularCapWindow} {t : ℝ} :
    t ∈ W.interval ↔ W.lower ≤ t ∧ t ≤ W.upper := by
  rfl

/-- The circular cap prescribed by a crossing window. -/
def cap (W : CircularCapWindow) (s : ℂ) : ℝ → ℂ :=
  circleCap s W.radius W.lower W.upper W.startAngle W.endAngle

/-- At `t`, the bundled cap is the point at the corresponding affine interpolation of its
endpoint angles. -/
theorem cap_apply (W : CircularCapWindow) (s : ℂ) (t : ℝ) :
    W.cap s t = circleMap s W.radius
      (W.startAngle + (W.endAngle - W.startAngle) / (W.upper - W.lower) * (t - W.lower)) := by
  simpa only [cap] using
    circleCap_apply s W.radius W.lower W.upper W.startAngle W.endAngle t

/-- The bundled cap starts at its prescribed angle at the lower endpoint. -/
@[simp]
theorem cap_left (W : CircularCapWindow) (s : ℂ) :
    W.cap s W.lower = circleMap s W.radius W.startAngle := by
  simpa only [cap] using
    circleCap_left s W.radius W.lower W.upper W.startAngle W.endAngle

/-- The bundled cap ends at its prescribed angle at a distinct upper endpoint. -/
@[simp]
theorem cap_right (W : CircularCapWindow) (s : ℂ) (hlu : W.lower ≠ W.upper) :
    W.cap s W.upper = circleMap s W.radius W.endAngle := by
  simpa only [cap] using
    circleCap_right s W.radius hlu W.startAngle W.endAngle

/-- A bundled cap is `C¹`. -/
theorem contDiff_cap (W : CircularCapWindow) (s : ℂ) : ContDiff ℝ 1 (W.cap s) := by
  simpa only [cap] using
    contDiff_circleCap s W.radius W.lower W.upper W.startAngle W.endAngle

/-- A bundled cap with nonzero signed radius misses its centre. -/
theorem cap_ne_center (W : CircularCapWindow) {s : ℂ} (hr : W.radius ≠ 0) {t : ℝ} :
    W.cap s t ≠ s := by
  simpa only [cap] using (circleCap_ne_center (s := s) (r := W.radius) (l := W.lower)
    (u := W.upper) (θ := W.startAngle) (θ' := W.endAngle) (t := t) hr)

/-- The winding number of a nondegenerate bundled cap is its angular extent over `2π`. -/
theorem windingNumber_cap (W : CircularCapWindow) (s : ℂ) (hr : W.radius ≠ 0)
    (hlu : W.lower ≠ W.upper) :
    windingNumber (W.cap s) W.lower W.upper s =
      ((W.endAngle - W.startAngle : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  simpa only [cap] using (windingNumber_circleCap (s := s) (r := W.radius) (l := W.lower)
    (u := W.upper) hr hlu W.startAngle W.endAngle)

/-- Replace one crossing window of `γ` by its prescribed circular cap about `s`. -/
def excise (W : CircularCapWindow) (γ : ℝ → ℂ) (s : ℂ) : ℝ → ℂ :=
  exciseCrossing γ s W.radius W.lower W.upper W.startAngle W.endAngle

/-- On its window, a one-window excision is the prescribed cap. -/
@[simp]
theorem excise_of_mem (W : CircularCapWindow) {γ : ℝ → ℂ} {s : ℂ} {t : ℝ}
    (ht : t ∈ W.interval) : W.excise γ s t = W.cap s t := by
  simpa only [excise, interval, cap] using (exciseCrossing_of_mem ht)

/-- Off its window, a one-window excision is the original curve. -/
@[simp]
theorem excise_of_notMem (W : CircularCapWindow) {γ : ℝ → ℂ} {s : ℂ} {t : ℝ}
    (ht : t ∉ W.interval) : W.excise γ s t = γ t := by
  simpa only [excise, interval] using (exciseCrossing_of_notMem ht)

end CircularCapWindow

/-- Replace each window in `windows` by its circular cap about `s`. Later replacements act on
the curve produced by earlier ones. For pairwise disjoint windows the order is immaterial
pointwise, and `exciseCrossings_eqOn_window` gives the simultaneous description. -/
def exciseCrossings (γ : ℝ → ℂ) (s : ℂ) : List CircularCapWindow → ℝ → ℂ
  := fun windows => windows.foldl (fun δ W => W.excise δ s) γ

/-- Excising an empty list of windows leaves the curve unchanged. -/
@[simp]
theorem exciseCrossings_nil (γ : ℝ → ℂ) (s : ℂ) : exciseCrossings γ s [] = γ := (rfl)

/-- Excising a nonempty list first replaces its head window. -/
@[simp]
theorem exciseCrossings_cons (γ : ℝ → ℂ) (s : ℂ) (W : CircularCapWindow)
    (windows : List CircularCapWindow) :
    exciseCrossings γ s (W :: windows) = exciseCrossings (W.excise γ s) s windows := (rfl)

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
      rw [exciseCrossings_cons]
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
      · rw [exciseCrossings_cons]
        refine (exciseCrossings_eqOn_compl
          (γ := CircularCapWindow.excise W γ s) (s := s) ?_).trans ?_
        · intro U hU
          exact hpw.1 U hU
        · exact fun _ ht => W.excise_of_mem ht
      · rw [exciseCrossings_cons]
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
      rw [exciseCrossings_cons]
      rw [List.pairwise_cons] at hpw
      have hW := hinside W List.mem_cons_self
      have hfirst : IsPiecewiseC1On (W.excise γ s) a b := by
        simpa only [CircularCapWindow.excise] using
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

/-- Finite excision preserves closedness when both parameter endpoints lie outside every
replacement window. -/
theorem exciseCrossings_closed {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {windows : List CircularCapWindow} (hclosed : γ a = γ b)
    (hendpoints : ∀ W ∈ windows, a ∉ W.interval ∧ b ∉ W.interval) :
    exciseCrossings γ s windows a = exciseCrossings γ s windows b := by
  rw [exciseCrossings_apply_of_forall_notMem (fun W hW => (hendpoints W hW).1),
    exciseCrossings_apply_of_forall_notMem (fun W hW => (hendpoints W hW).2), hclosed]

/-- If closed windows cover every parameter in `Icc a b` where `γ` meets `s`, and every window
meeting `Icc a b` has nonzero radius, finite excision produces a curve avoiding `s` there, even
when the windows overlap. -/
theorem exciseCrossings_ne_center {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {windows : List CircularCapWindow}
    (hr : ∀ W ∈ windows, (W.interval ∩ Icc a b).Nonempty → W.radius ≠ 0)
    (hcover : ∀ t ∈ Icc a b, γ t = s → ∃ W ∈ windows, t ∈ W.interval) :
    ∀ t ∈ Icc a b, exciseCrossings γ s windows t ≠ s := by
  induction windows generalizing γ with
  | nil =>
      intro t ht hγt
      obtain ⟨W, hW, -⟩ := hcover t ht hγt
      simp at hW
  | cons W windows ih =>
      rw [exciseCrossings_cons]
      apply ih (fun V hV => hr V (List.mem_cons_of_mem W hV))
      intro t ht hexcise
      by_cases htW : t ∈ W.interval
      · rw [W.excise_of_mem htW] at hexcise
        exact absurd hexcise (W.cap_ne_center (hr W List.mem_cons_self ⟨t, htW, ht⟩))
      · rw [W.excise_of_notMem htW] at hexcise
        obtain ⟨V, hV, htV⟩ := hcover t ht hexcise
        rcases List.mem_cons.mp hV with rfl | hV
        · exact absurd htV htW
        · exact ⟨V, hV, htV⟩

end TauCeti.Contour

end
