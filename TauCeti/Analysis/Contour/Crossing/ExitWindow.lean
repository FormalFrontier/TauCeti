/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.CapAngle
public import TauCeti.Analysis.Contour.Crossing.FiniteExcision
public import TauCeti.Analysis.Contour.ExitTime
import Mathlib.Algebra.Order.Field.Pi

/-!
# Equal-radius cap windows at crossings

Hungerbühler--Wasem Proposition 2.2 removes a small parameter interval about each crossing and
joins its endpoints by a circular cap.  The two endpoints must lie on the same circle about the
crossed point: otherwise the cap does not join both of them.  This file obtains those endpoints
from the left and right first-exit times at a common spatial radius.

`exitCapWindow` packages the resulting interval and the branch-sensitive cap sweep from
`Crossing.CapAngle` as a `CircularCapWindow`.  Its characteristic API proves that the crossing is
strictly inside the window, both endpoint chords have the prescribed norm, and the cap really
joins the original curve.  `exitCapWindows` applies the construction to the sorted members of a
finite crossing set; common symmetric time windows that are separated by more than twice their
half-width produce strictly ordered cap windows.

This is the geometric window construction in Proposition 2.2.  The principal-value calculation on
the generally asymmetric exit-time interval is separate: once that value is supplied,
`windingNumber_exitCapWindow_sub_cap` identifies the local loop with its crossing angle.

## Main definitions

* `TauCeti.Contour.exitCapWindow` -- the cap window determined by two first-exit times.
* `TauCeti.Contour.exitCapWindows` -- the corresponding list for a finite crossing set.

## Main results

* `TauCeti.Contour.exitCapWindow_spec` -- equal radii, strict placement, and endpoint matching.
* `TauCeti.Contour.exists_exitCapWindows` -- existence of one common spatial radius for the
  finite family.
* `TauCeti.Contour.pairwise_exitCapWindows` -- the finite windows are strictly ordered.
* `TauCeti.Contour.windingNumber_exitCapWindow_sub_cap` -- the exact local angle contribution,
  conditional only on the principal-value value for the asymmetric window.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.

No external formalization is copied or adapted here.  The construction composes Tau Ceti's
first-exit-time, circular-cap, and crossing-angle APIs.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

/-- The circular-cap window whose endpoints are the first exits from the radius-`ε` circle on
the two sides of a crossing `t₀`.  Its cap starts in the direction of the left endpoint chord and
uses `crossingCapSweep` to reach the right endpoint without an undetected full turn. -/
def exitCapWindow (γ : ℝ → ℂ) (s : ℂ) (t₀ δ ε : ℝ) (L_R L_L : ℂ) : CircularCapWindow where
  radius := ε
  lower := firstExitTimeLeft γ t₀ δ s ε
  upper := firstExitTimeRight γ t₀ δ s ε
  startAngle := (γ (firstExitTimeLeft γ t₀ δ s ε) - s).arg
  endAngle := (γ (firstExitTimeLeft γ t₀ δ s ε) - s).arg +
    crossingCapSweep γ t₀ L_R L_L (γ (firstExitTimeLeft γ t₀ δ s ε) - s)
      (γ (firstExitTimeRight γ t₀ δ s ε) - s)

/-- The signed radius of an exit-time cap window is the prescribed spatial exit radius. -/
@[simp] theorem exitCapWindow_radius : (exitCapWindow γ s t₀ δ ε L_R L_L).radius = ε := (rfl)

/-- The lower endpoint of an exit-time cap window is the left first-exit time. -/
@[simp] theorem exitCapWindow_lower :
    (exitCapWindow γ s t₀ δ ε L_R L_L).lower = firstExitTimeLeft γ t₀ δ s ε := (rfl)

/-- The upper endpoint of an exit-time cap window is the right first-exit time. -/
@[simp] theorem exitCapWindow_upper :
    (exitCapWindow γ s t₀ δ ε L_R L_L).upper = firstExitTimeRight γ t₀ δ s ε := (rfl)

/-- The cap starts at the argument of the left endpoint chord. -/
@[simp] theorem exitCapWindow_startAngle :
    (exitCapWindow γ s t₀ δ ε L_R L_L).startAngle =
      (γ (firstExitTimeLeft γ t₀ δ s ε) - s).arg := (rfl)

/-- The cap's terminal angle is its initial angle plus the branch-sensitive crossing sweep. -/
@[simp] theorem exitCapWindow_endAngle :
    (exitCapWindow γ s t₀ δ ε L_R L_L).endAngle =
      (γ (firstExitTimeLeft γ t₀ δ s ε) - s).arg +
        crossingCapSweep γ t₀ L_R L_L (γ (firstExitTimeLeft γ t₀ δ s ε) - s)
          (γ (firstExitTimeRight γ t₀ δ s ε) - s) := (rfl)

/-- **The exit-time cap window has the prescribed geometry.**  If `γ` is continuous on the
symmetric ambient window, passes through `s` at `t₀`, and both ambient endpoints lie at least
distance `ε > 0` from `s`, then the first exits lie strictly on their respective sides of `t₀`
and their chords both have norm `ε`.  Nonzero one-sided tangent limits make the cap selected by
`crossingCapSweep` join those two endpoints exactly. -/
theorem exitCapWindow_spec {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) (t₀ + δ)))
    (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖)
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    let W := exitCapWindow γ s t₀ δ ε L_R L_L
    W.lower < t₀ ∧ t₀ < W.upper ∧
      ‖γ W.lower - s‖ = ε ∧ ‖γ W.upper - s‖ = ε ∧
      W.cap s W.lower = γ W.lower ∧ W.cap s W.upper = γ W.upper := by
  let W := exitCapWindow γ s t₀ δ ε L_R L_L
  have hγL : ContinuousOn γ (Icc (t₀ - δ) t₀) :=
    hγ.mono (Icc_subset_Icc le_rfl (by linarith))
  have hγR : ContinuousOn γ (Icc t₀ (t₀ + δ)) :=
    hγ.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hlo : W.lower < t₀ := by
    simpa only [W, exitCapWindow_lower] using
      firstExitTimeLeft_lt hδ hγL h_at hε hεL
  have hhi : t₀ < W.upper := by
    simpa only [W, exitCapWindow_upper] using
      lt_firstExitTimeRight hδ hγR h_at hε hεR
  have hnormL : ‖γ W.lower - s‖ = ε := by
    simpa only [W, exitCapWindow_lower] using
      norm_at_firstExitTimeLeft_eq hδ hγL h_at hε hεL
  have hnormR : ‖γ W.upper - s‖ = ε := by
    simpa only [W, exitCapWindow_upper] using
      norm_at_firstExitTimeRight_eq hδ hγR h_at hε hεR
  have hends := circleMap_crossingCapSweep_endpoints
    (γ := γ) (s := s) (t₀ := t₀) hL_L hL_R (hnormL.trans hnormR.symm) h_R h_L
  have hradius : W.radius = ‖γ W.lower - s‖ := by
    exact (exitCapWindow_radius (γ := γ) (s := s) (t₀ := t₀) (δ := δ) (ε := ε)
      (L_R := L_R) (L_L := L_L)).trans hnormL.symm
  have hstart : W.startAngle = (γ W.lower - s).arg := by
    rfl
  have hend : W.endAngle = (γ W.lower - s).arg +
      crossingCapSweep γ t₀ L_R L_L (γ W.lower - s) (γ W.upper - s) := by
    rfl
  refine ⟨hlo, hhi, hnormL, hnormR, ?_, ?_⟩
  · rw [CircularCapWindow.cap_left, hradius, hstart, hends.1]
    ring
  · rw [CircularCapWindow.cap_right _ _ (hlo.trans hhi).ne, hradius, hend, hends.2]
    ring

/-- The exit-time window lies inside its ambient symmetric window. -/
theorem exitCapWindow_subset_Icc {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 ≤ δ) (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖) :
    (exitCapWindow γ s t₀ δ ε L_R L_L).interval ⊆ Icc (t₀ - δ) (t₀ + δ) := by
  intro t ht
  rw [CircularCapWindow.mem_interval_iff] at ht
  exact ⟨(firstExitTimeLeft_mem_Icc hδ hεL).1.trans ht.1,
    ht.2.trans (firstExitTimeRight_mem_Icc hδ hεR).2⟩

/-- If `t₀` is the only crossing in the ambient symmetric window, it is also the only crossing
in its smaller exit-time window. -/
theorem eq_crossing_of_mem_exitCapWindow {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ}
    {L_R L_L : ℂ} (hδ : 0 ≤ δ) (hεL : ε ≤ ‖γ (t₀ - δ) - s‖)
    (hεR : ε ≤ ‖γ (t₀ + δ) - s‖)
    (h_unique : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), γ t = s → t = t₀)
    {t : ℝ} (ht : t ∈ (exitCapWindow γ s t₀ δ ε L_R L_L).interval) (heq : γ t = s) :
    t = t₀ :=
  h_unique t (exitCapWindow_subset_Icc hδ hεL hεR ht) heq

/-- The finite list of equal-radius exit-time cap windows, ordered by their crossing parameters. -/
def exitCapWindows (γ : ℝ → ℂ) (s : ℂ) (T : Finset ℝ) (δ ε : ℝ)
    (L_R L_L : ℝ → ℂ) : List CircularCapWindow :=
  (T.sort (· ≤ ·)).map fun t ↦ exitCapWindow γ s t δ ε (L_R t) (L_L t)

/-- Membership in `exitCapWindows` means being the exit-time window of a listed crossing. -/
theorem mem_exitCapWindows_iff {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} :
    W ∈ exitCapWindows γ s T δ ε L_R L_L ↔
      ∃ t ∈ T, W = exitCapWindow γ s t δ ε (L_R t) (L_L t) := by
  simp only [exitCapWindows, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- **Finite exit-window geometry.**  Under common ambient-window and endpoint-radius bounds,
every listed window lies strictly inside `[a, b]`, has radius `ε`, has equal-radius endpoint
chords, and its cap joins the original curve.  Conversely, every listed crossing lies in the
interior of its corresponding window.  This is the finite family of geometric hypotheses needed
by simultaneous crossing excision. -/
theorem exitCapWindows_spec {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {a b δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ContinuousOn γ (Icc a b))
    (hinside : ∀ t ∈ T, a < t - δ ∧ t + δ < b)
    (h_at : ∀ t ∈ T, γ t = s)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hL_R : ∀ t ∈ T, L_R t ≠ 0) (hL_L : ∀ t ∈ T, L_L t ≠ 0)
    (h_R : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[>] t) (𝓝 (L_R t)))
    (h_L : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[<] t) (𝓝 (L_L t))) :
    (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L,
      W.radius = ε ∧ a < W.lower ∧ W.lower < W.upper ∧ W.upper < b ∧
        ‖γ W.lower - s‖ = ε ∧ ‖γ W.upper - s‖ = ε ∧
        W.cap s W.lower = γ W.lower ∧ W.cap s W.upper = γ W.upper) ∧
      ∀ t ∈ T, ∃ W ∈ exitCapWindows γ s T δ ε L_R L_L,
        t ∈ Ioo W.lower W.upper := by
  constructor
  · intro W hW
    obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
    have hγt : ContinuousOn γ (Icc (t - δ) (t + δ)) :=
      hγ.mono (Icc_subset_Icc (hinside t ht).1.le (hinside t ht).2.le)
    obtain ⟨hlo, hhi, hnormL, hnormR, hcapL, hcapR⟩ :=
      exitCapWindow_spec hδ hε (h_at t ht) hγt (hεL t ht) (hεR t ht)
        (hL_R t ht) (hL_L t ht) (h_R t ht) (h_L t ht)
    have hleft := (firstExitTimeLeft_mem_Icc hδ.le (hεL t ht)).1
    have hright := (firstExitTimeRight_mem_Icc hδ.le (hεR t ht)).2
    exact ⟨rfl, (hinside t ht).1.trans_le hleft, hlo.trans hhi,
      hright.trans_lt (hinside t ht).2, hnormL, hnormR, hcapL, hcapR⟩
  · intro t ht
    let W := exitCapWindow γ s t δ ε (L_R t) (L_L t)
    refine ⟨W, mem_exitCapWindows_iff.mpr ⟨t, ht, rfl⟩, ?_⟩
    have hγt : ContinuousOn γ (Icc (t - δ) (t + δ)) :=
      hγ.mono (Icc_subset_Icc (hinside t ht).1.le (hinside t ht).2.le)
    obtain ⟨hlo, hhi, -, -, -, -⟩ :=
      exitCapWindow_spec hδ hε (h_at t ht) hγt (hεL t ht) (hεR t ht)
        (hL_R t ht) (hL_L t ht) (h_R t ht) (h_L t ht)
    exact ⟨hlo, hhi⟩

/-- Exit-time cap windows inherit strict left-to-right ordering from separated symmetric windows. -/
theorem pairwise_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 ≤ δ)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 2 * δ < |t - t'|) :
    (exitCapWindows γ s T δ ε L_R L_L).Pairwise fun W V ↦ W.upper < V.lower := by
  rw [exitCapWindows, List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have ht : (T.sort (· ≤ ·))[i] ∈ T :=
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
  have ht' : (T.sort (· ≤ ·))[j] ∈ T :=
    (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hj)
  have htt' : (T.sort (· ≤ ·))[i] < (T.sort (· ≤ ·))[j] :=
    (Finset.sortedLT_sort T).getElem_lt_getElem_of_lt hij
  have hdist := hsep _ ht _ ht' htt'.ne
  rw [abs_of_neg (sub_neg.mpr htt')] at hdist
  have hu := (firstExitTimeRight_mem_Icc hδ (hεR _ ht)).2
  have hl := (firstExitTimeLeft_mem_Icc hδ (hεL _ ht')).1
  simpa only [exitCapWindow_upper, exitCapWindow_lower] using (show
    firstExitTimeRight γ (T.sort (· ≤ ·))[i] δ s ε <
      firstExitTimeLeft γ (T.sort (· ≤ ·))[j] δ s ε by linarith)

/-- **Existence of the finite equal-radius cap-window family.**  Suppose `T` lists exactly the
crossings in `[a, b]`, common symmetric time windows of half-width `δ > 0` lie inside `[a, b]`,
and distinct crossings are more than `2δ` apart.  There is then one spatial radius `ε > 0` below
the endpoint distances of every symmetric window.  The corresponding exit-time cap windows are
strictly ordered, lie inside `[a, b]`, cover all crossings, and have matching cap endpoints.

The tangent data selects each cap's branch-sensitive sweep.  The theorem does not evaluate the
principal value on the resulting asymmetric windows; that is the remaining analytic input to
`windingNumber_exitCapWindow_sub_cap`. -/
theorem exists_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {a b δ : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 < δ) (hγ : ContinuousOn γ (Icc a b))
    (hinside : ∀ t ∈ T, a < t - δ ∧ t + δ < b)
    (h_at : ∀ t ∈ T, γ t = s)
    (hcomplete : ∀ t ∈ Icc a b, γ t = s → t ∈ T)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 2 * δ < |t - t'|)
    (hL_R : ∀ t ∈ T, L_R t ≠ 0) (hL_L : ∀ t ∈ T, L_L t ≠ 0)
    (h_R : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[>] t) (𝓝 (L_R t)))
    (h_L : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[<] t) (𝓝 (L_L t))) :
    ∃ ε > 0,
      ((exitCapWindows γ s T δ ε L_R L_L).Pairwise fun W V ↦ W.upper < V.lower) ∧
      (∀ W ∈ exitCapWindows γ s T δ ε L_R L_L,
        W.radius = ε ∧ a < W.lower ∧ W.lower < W.upper ∧ W.upper < b ∧
          ‖γ W.lower - s‖ = ε ∧ ‖γ W.upper - s‖ = ε ∧
          W.cap s W.lower = γ W.lower ∧ W.cap s W.upper = γ W.upper) ∧
      ∀ t ∈ T, ∃ W ∈ exitCapWindows γ s T δ ε L_R L_L,
        t ∈ Ioo W.lower W.upper := by
  classical
  have hendpoint : ∀ t ∈ T, γ (t - δ) ≠ s ∧ γ (t + δ) ≠ s := by
    intro t ht
    constructor
    · intro heq
      have hmem : t - δ ∈ T := hcomplete _
        ⟨(hinside t ht).1.le, by linarith [(hinside t ht).2]⟩ heq
      have hne : t - δ ≠ t := by linarith
      have h := hsep t ht (t - δ) hmem hne.symm
      rw [show t - (t - δ) = δ by ring, abs_of_pos hδ] at h
      linarith
    · intro heq
      have hmem : t + δ ∈ T := hcomplete _
        ⟨by linarith [(hinside t ht).1], (hinside t ht).2.le⟩ heq
      have hne : t + δ ≠ t := by linarith
      have h := hsep t ht (t + δ) hmem hne.symm
      rw [show t - (t + δ) = -δ by ring, abs_neg, abs_of_pos hδ] at h
      linarith
  obtain ⟨ε, hε, hε_all⟩ := Pi.exists_forall_pos_add_lt
    (ι := Option {t // t ∈ T}) (x := fun _ ↦ (0 : ℝ))
    (y := fun i ↦ i.elim 1 fun t ↦ min ‖γ (t.1 - δ) - s‖ ‖γ (t.1 + δ) - s‖)
    (fun i ↦ by
      cases i with
      | none => norm_num
      | some t =>
          change 0 < min ‖γ (t.1 - δ) - s‖ ‖γ (t.1 + δ) - s‖
          exact lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr (hendpoint t.1 t.2).1))
            (norm_pos_iff.mpr (sub_ne_zero.mpr (hendpoint t.1 t.2).2)))
  have hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ := by
    intro t ht
    simpa only [zero_add] using
      (hε_all (some ⟨t, ht⟩)).le.trans (min_le_left _ _)
  have hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖ := by
    intro t ht
    simpa only [zero_add] using
      (hε_all (some ⟨t, ht⟩)).le.trans (min_le_right _ _)
  obtain ⟨hgeometry, hcover⟩ := exitCapWindows_spec hδ hε hγ hinside h_at
    hεL hεR hL_R hL_L h_R h_L
  exact ⟨ε, hε, pairwise_exitCapWindows hδ.le hεL hεR hsep, hgeometry, hcover⟩

/-- The exact local angle identity for an exit-time cap window.  Equal endpoint radii and endpoint
matching are discharged by `exitCapWindow_spec`; the remaining hypothesis is precisely the
principal-value evaluation on the asymmetric exit-time interval. -/
theorem windingNumber_exitCapWindow_sub_cap {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ}
    {L_R L_L : ℂ} (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) (t₀ + δ)))
    (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖)
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (hpv : HasCauchyPVAt γ (firstExitTimeLeft γ t₀ δ s ε)
      (firstExitTimeRight γ t₀ δ s ε) (fun z ↦ (z - s)⁻¹) s
      (((((-L_L) / (γ (firstExitTimeLeft γ t₀ δ s ε) - s)).arg +
        ((γ (firstExitTimeRight γ t₀ δ s ε) - s) / L_R).arg : ℝ) : ℂ) * Complex.I)) :
    let W := exitCapWindow γ s t₀ δ ε L_R L_L
    windingNumber γ W.lower W.upper s - windingNumber (W.cap s) W.lower W.upper s =
      (crossingAngle γ t₀ : ℂ) / (2 * (Real.pi : ℂ)) := by
  let W := exitCapWindow γ s t₀ δ ε L_R L_L
  obtain ⟨hlo, hhi, hnormL, hnormR, -, -⟩ :=
    exitCapWindow_spec hδ hε h_at hγ hεL hεR hL_R hL_L h_R h_L
  have hwL : γ W.lower - s ≠ 0 := by
    rw [← norm_pos_iff, hnormL]
    exact hε
  let cap := circleCap s ‖γ W.lower - s‖ W.lower W.upper (γ W.lower - s).arg
    ((γ W.lower - s).arg +
      crossingCapSweep γ t₀ L_R L_L (γ W.lower - s) (γ W.upper - s))
  have hlocal := windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi
    (γ := γ) (s := s) (t₀ := t₀) (L_R := L_R) (L_L := L_L)
    (w_L := γ W.lower - s) (w_R := γ W.upper - s) (l := W.lower) (u := W.upper)
    hL_L hL_R hwL (hlo.trans hhi).ne
    rfl rfl (hnormL.trans hnormR.symm) h_R h_L (by simpa only [W, exitCapWindow_lower,
      exitCapWindow_upper] using hpv)
  have hradius : W.radius = ‖γ W.lower - s‖ := by
    exact (exitCapWindow_radius (γ := γ) (s := s) (t₀ := t₀) (δ := δ) (ε := ε)
      (L_R := L_R) (L_L := L_L)).trans hnormL.symm
  have hstart : W.startAngle = (γ W.lower - s).arg := by
    rfl
  have hend : W.endAngle = (γ W.lower - s).arg +
      crossingCapSweep γ t₀ L_R L_L (γ W.lower - s) (γ W.upper - s) := by
    rfl
  have hcap : EqOn (W.cap s) cap (uIoo W.lower W.upper) := by
    intro t _
    rw [CircularCapWindow.cap_apply]
    dsimp only [cap]
    rw [circleCap_apply, hradius, hstart, hend]
  have hresult : windingNumber γ W.lower W.upper s -
      windingNumber (W.cap s) W.lower W.upper s =
        (crossingAngle γ t₀ : ℂ) / (2 * (Real.pi : ℂ)) := by
    rw [windingNumber_congr_curve hcap]
    exact hlocal.2.2
  simpa only using hresult

end TauCeti.Contour

end
