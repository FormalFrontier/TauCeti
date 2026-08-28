/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.CapAngle
public import TauCeti.Analysis.Contour.Crossing.FiniteExcision
public import TauCeti.Analysis.Contour.ExitTime
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic

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
finite crossing set; crossings separated by more than twice the ambient half-width
(`2 * δ < |t - t'|`) produce nonoverlapping, hence pairwise disjoint, cap windows.

This is the window construction and local analytic calculation in Proposition 2.2.
`exists_radius_hasCauchyPVAt_exitCapWindow` evaluates the principal value on each generally
asymmetric exit-time interval, and
`windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi` then identifies the local loop
with its crossing angle.

## Main definitions

* `TauCeti.Contour.exitCapWindow` -- the cap window determined by two first-exit times.
* `TauCeti.Contour.exitCapWindows` -- the corresponding list for a finite crossing set.

## Main results

* `TauCeti.Contour.cap_exitCapWindow_lower_eq` and
  `TauCeti.Contour.cap_exitCapWindow_upper_eq` -- the cap joins the original curve at both
  endpoints.
* `TauCeti.Contour.pairwise_disjoint_interval_exitCapWindows` -- the finite windows are pairwise
  disjoint, in the shape `Crossing.FiniteExcision` consumes.
* `TauCeti.Contour.exists_radius_hasCauchyPVAt_exitCapWindow` -- sufficiently small exit-time
  windows have the boundary-argument principal value.
* `TauCeti.Contour.windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi` -- the exact
  local angle contribution, once the principal value on the asymmetric exit-time window is
  supplied alongside the standing continuity, tangent, and radius hypotheses.

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
the two sides of a crossing `t₀`.  Those exits are searched in the ambient window
`[t₀ - δ, t₀ + δ]`, so `δ` is the ambient half-width.  The endpoint bounds
`ε ≤ ‖γ (t₀ - δ) - s‖` and `ε ≤ ‖γ (t₀ + δ) - s‖` certify that the defining sets are nonempty;
without such witnesses, an empty defining set gives the corresponding junk value `0`.  The
parameters `L_R`, `L_L` are the right- and left-hand tangent limits of `γ` at `t₀`, passed right
before left as in `crossingCapSweep`; exchanging them selects a different cap.  The cap starts in
the direction of the left endpoint chord and sweeps by `crossingCapSweep`, the tangent-selected
representative of the endpoint angle, which tends to `-crossingAngle γ t₀` as the endpoints
approach `t₀` (`tendsto_crossingCapSweep`). -/
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

/-- **The left exit time is strictly left of the crossing.**  If `γ` is continuous on the left
half of the ambient window, passes through `s` at `t₀`, and the ambient left endpoint lies at
distance at least `ε > 0` from `s`, the window's lower endpoint is strictly below `t₀`. -/
theorem exitCapWindow_lower_lt {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (exitCapWindow γ s t₀ δ ε L_R L_L).lower < t₀ := by
  rw [exitCapWindow_lower]
  exact firstExitTimeLeft_lt hδ hγ h_at hε hεL

/-- **The right exit time is strictly right of the crossing.**  The mirror image of
`exitCapWindow_lower_lt` on the right half of the ambient window. -/
theorem lt_exitCapWindow_upper {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖) :
    t₀ < (exitCapWindow γ s t₀ δ ε L_R L_L).upper := by
  rw [exitCapWindow_upper]
  exact lt_firstExitTimeRight hδ hγ h_at hε hεR

/-- **The left endpoint chord has the prescribed norm.**  At the left first-exit time the curve
sits exactly on the circle of radius `ε` about `s`. -/
theorem norm_sub_exitCapWindow_lower_eq {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) :
    ‖γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s‖ = ε := by
  rw [exitCapWindow_lower]
  exact norm_at_firstExitTimeLeft_eq hδ hγ h_at hε hεL

/-- **The right endpoint chord has the prescribed norm.**  The mirror image of
`norm_sub_exitCapWindow_lower_eq`; together they put both endpoints on one circle about `s`. -/
theorem norm_sub_exitCapWindow_upper_eq {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖) :
    ‖γ (exitCapWindow γ s t₀ δ ε L_R L_L).upper - s‖ = ε := by
  rw [exitCapWindow_upper]
  exact norm_at_firstExitTimeRight_eq hδ hγ h_at hε hεR

/-- The bundled cap of an exit-time window, spelled through the window's own endpoints: once the
left endpoint chord has norm `ε`, it is the circular cap of that chord's radius sweeping from the
chord's argument by `crossingCapSweep`. -/
theorem cap_exitCapWindow_eq_circleCap {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hnorm : ‖γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s‖ = ε) :
    (exitCapWindow γ s t₀ δ ε L_R L_L).cap s =
      circleCap s ‖γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s‖
        (exitCapWindow γ s t₀ δ ε L_R L_L).lower (exitCapWindow γ s t₀ δ ε L_R L_L).upper
        (γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s).arg
        ((γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s).arg +
          crossingCapSweep γ t₀ L_R L_L (γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s)
            (γ (exitCapWindow γ s t₀ δ ε L_R L_L).upper - s)) := by
  funext t
  rw [CircularCapWindow.cap_apply, circleCap_apply, exitCapWindow_radius, hnorm,
    exitCapWindow_startAngle, exitCapWindow_endAngle, exitCapWindow_lower, exitCapWindow_upper]

/-- **The cap meets the curve at the left endpoint.**  The cap starts in the direction of the
left first-exit chord, so its initial value is `γ` at that exit time. -/
theorem cap_exitCapWindow_lower_eq {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) t₀)) (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) :
    (exitCapWindow γ s t₀ δ ε L_R L_L).cap s (exitCapWindow γ s t₀ δ ε L_R L_L).lower =
      γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower := by
  have hnormL := norm_sub_exitCapWindow_lower_eq (L_R := L_R) (L_L := L_L)
    hδ hε h_at hγ hεL
  rw [cap_exitCapWindow_eq_circleCap hnormL, circleCap_left, circleMap,
    Complex.norm_mul_exp_arg_mul_I]
  ring

/-- **The cap meets the curve at the right endpoint.**  The companion of
`cap_exitCapWindow_lower_eq`: the same cap ends at `γ` of the right first-exit time, so the
excised curve is continuous at both ends of the window. -/
theorem cap_exitCapWindow_upper_eq {γ : ℝ → ℂ} {s : ℂ} {t₀ δ ε : ℝ} {L_R L_L : ℂ}
    (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) (t₀ + δ)))
    (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖)
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    (exitCapWindow γ s t₀ δ ε L_R L_L).cap s (exitCapWindow γ s t₀ δ ε L_R L_L).upper =
      γ (exitCapWindow γ s t₀ δ ε L_R L_L).upper := by
  have hγL : ContinuousOn γ (Icc (t₀ - δ) t₀) := hγ.mono (Icc_subset_Icc le_rfl (by linarith))
  have hγR : ContinuousOn γ (Icc t₀ (t₀ + δ)) := hγ.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hnormL := norm_sub_exitCapWindow_lower_eq (L_R := L_R) (L_L := L_L)
    hδ hε h_at hγL hεL
  have hnormR := norm_sub_exitCapWindow_upper_eq (L_R := L_R) (L_L := L_L)
    hδ hε h_at hγR hεR
  have hne : (exitCapWindow γ s t₀ δ ε L_R L_L).lower ≠
      (exitCapWindow γ s t₀ δ ε L_R L_L).upper :=
    ((exitCapWindow_lower_lt hδ hε h_at hγL hεL).trans
      (lt_exitCapWindow_upper hδ hε h_at hγR hεR)).ne
  have hends := circleMap_crossingCapSweep_endpoints
    (γ := γ) (s := s) (t₀ := t₀) hL_L hL_R (hnormL.trans hnormR.symm) h_R h_L
  rw [cap_exitCapWindow_eq_circleCap hnormL, circleCap_right _ _ hne, hends.2]
  ring

/-- The finite list of equal-radius exit-time cap windows, ordered by their crossing parameters. -/
def exitCapWindows (γ : ℝ → ℂ) (s : ℂ) (T : Finset ℝ) (δ ε : ℝ)
    (L_R L_L : ℝ → ℂ) : List CircularCapWindow :=
  (T.sort (· ≤ ·)).map fun t ↦ exitCapWindow γ s t δ ε (L_R t) (L_L t)

/-- Membership in `exitCapWindows` means being the exit-time window of a listed crossing. -/
@[simp] theorem mem_exitCapWindows_iff {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} :
    W ∈ exitCapWindows γ s T δ ε L_R L_L ↔
      ∃ t ∈ T, W = exitCapWindow γ s t δ ε (L_R t) (L_L t) := by
  simp only [exitCapWindows, List.mem_map, Finset.mem_sort]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

/-- Every listed window carries the common spatial radius.  Thus one result depending on `ε` can
be applied uniformly across the family; simultaneous excision itself only requires each radius
to be nonzero. -/
theorem radius_eq_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    W.radius = ε := by
  obtain ⟨t, -, rfl⟩ := mem_exitCapWindows_iff.mp hW
  exact exitCapWindow_radius

/-- A listed window starts strictly after `a` when every ambient window does. -/
theorem lt_lower_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {a δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 ≤ δ) (ha : ∀ t ∈ T, a < t - δ)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    a < W.lower := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  rw [exitCapWindow_lower]
  exact (ha t ht).trans_le (firstExitTimeLeft_mem_Icc hδ (hεL t ht)).1

/-- A listed window ends strictly before `b` when every ambient window does. -/
theorem upper_lt_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {b δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 ≤ δ) (hb : ∀ t ∈ T, t + δ < b)
    (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖) (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    W.upper < b := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  rw [exitCapWindow_upper]
  exact (firstExitTimeRight_mem_Icc hδ (hεR t ht)).2.trans_lt (hb t ht)

/-- Between the crossing's own two exit times a listed window is nondegenerate. -/
theorem lower_lt_upper_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ))) (h_at : ∀ t ∈ T, γ t = s)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    W.lower < W.upper := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  exact (exitCapWindow_lower_lt hδ hε (h_at t ht)
      ((hγ t ht).mono (Icc_subset_Icc le_rfl (by linarith))) (hεL t ht)).trans
    (lt_exitCapWindow_upper hδ hε (h_at t ht)
      ((hγ t ht).mono (Icc_subset_Icc (by linarith) le_rfl)) (hεR t ht))

/-- Every listed window's left endpoint chord has the common radius `ε`. -/
theorem norm_sub_lower_eq_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) t))
    (h_at : ∀ t ∈ T, γ t = s) (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖)
    (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    ‖γ W.lower - s‖ = ε := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  exact norm_sub_exitCapWindow_lower_eq hδ hε (h_at t ht) (hγ t ht) (hεL t ht)

/-- Every listed window's right endpoint chord has the common radius `ε`. -/
theorem norm_sub_upper_eq_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc t (t + δ)))
    (h_at : ∀ t ∈ T, γ t = s) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    ‖γ W.upper - s‖ = ε := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  exact norm_sub_exitCapWindow_upper_eq hδ hε (h_at t ht) (hγ t ht) (hεR t ht)

/-- The curve meets the cap's initial point at a listed window's lower endpoint, in the shape
`IsPiecewiseC1On.exciseCrossings` consumes. -/
theorem eq_circleMap_startAngle_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ}
    {δ ε : ℝ} {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) t))
    (h_at : ∀ t ∈ T, γ t = s) (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖)
    (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    γ W.lower = circleMap s W.radius W.startAngle := by
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  rw [← CircularCapWindow.cap_left]
  exact (cap_exitCapWindow_lower_eq hδ hε (h_at t ht) (hγ t ht) (hεL t ht)).symm

/-- The curve meets the cap's terminal point at a listed window's upper endpoint, in the shape
`IsPiecewiseC1On.exciseCrossings` consumes. -/
theorem eq_circleMap_endAngle_of_mem_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ}
    {δ ε : ℝ} {L_R L_L : ℝ → ℂ} {W : CircularCapWindow} (hδ : 0 < δ) (hε : 0 < ε)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ))) (h_at : ∀ t ∈ T, γ t = s)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hL_R : ∀ t ∈ T, L_R t ≠ 0) (hL_L : ∀ t ∈ T, L_L t ≠ 0)
    (h_R : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[>] t) (𝓝 (L_R t)))
    (h_L : ∀ t ∈ T, Tendsto (deriv γ) (𝓝[<] t) (𝓝 (L_L t)))
    (hW : W ∈ exitCapWindows γ s T δ ε L_R L_L) :
    γ W.upper = circleMap s W.radius W.endAngle := by
  have hne : W.lower ≠ W.upper :=
    (lower_lt_upper_of_mem_exitCapWindows hδ hε hγ h_at hεL hεR hW).ne
  obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
  rw [← CircularCapWindow.cap_right _ _ hne]
  exact (cap_exitCapWindow_upper_eq hδ hε (h_at t ht)
    (hγ t ht) (hεL t ht) (hεR t ht)
    (hL_R t ht) (hL_L t ht) (h_R t ht) (h_L t ht)).symm

/-- Exit-time cap windows inherit strict left-to-right ordering from separated symmetric
windows. -/
theorem pairwise_upper_lt_lower_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 ≤ δ)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 2 * δ < |t - t'|) :
    (exitCapWindows γ s T δ ε L_R L_L).Pairwise fun W V ↦ W.upper < V.lower := by
  rw [exitCapWindows, List.pairwise_map]
  refine (Finset.sortedLT_sort T).pairwise.imp_of_mem ?_
  intro t t' hmem hmem' htt'
  rw [Finset.mem_sort] at hmem hmem'
  have hdist := hsep _ hmem _ hmem' htt'.ne
  rw [abs_of_neg (sub_neg.mpr htt')] at hdist
  have hu := (firstExitTimeRight_mem_Icc hδ (hεR _ hmem)).2
  have hl := (firstExitTimeLeft_mem_Icc hδ (hεL _ hmem')).1
  rw [exitCapWindow_upper, exitCapWindow_lower]
  linarith


/-- Strictly ordered exit-time cap windows are pairwise disjoint, the hypothesis shape of the
simultaneous excision in `Crossing.FiniteExcision`. -/
theorem pairwise_disjoint_interval_exitCapWindows {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ ε : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 ≤ δ)
    (hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖) (hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → 2 * δ < |t - t'|) :
    (exitCapWindows γ s T δ ε L_R L_L).Pairwise fun W V ↦ Disjoint W.interval V.interval := by
  exact pairwise_disjoint_interval_of_pairwise_upper_lt_lower
    (pairwise_upper_lt_lower_exitCapWindows hδ hεL hεR hsep)

/-- **A common spatial exit radius for a finite crossing family.**  If both ambient endpoints
stay away from the crossed point, one positive radius works on both sides of every crossing.
For this radius, continuity places every crossing strictly inside its generated exit-time window.
The empty family is included. -/
theorem exists_common_exitCapWindows_radius {γ : ℝ → ℂ} {s : ℂ} {T : Finset ℝ} {δ : ℝ}
    {L_R L_L : ℝ → ℂ} (hδ : 0 < δ)
    (hγ : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ)))
    (h_at : ∀ t ∈ T, γ t = s)
    (hendpoint : ∀ t ∈ T, γ (t - δ) ≠ s ∧ γ (t + δ) ≠ s) :
    ∃ ε > 0,
      (∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ ∧ ε ≤ ‖γ (t + δ) - s‖) ∧
      ∀ t ∈ T, t ∈ Ioo (exitCapWindow γ s t δ ε (L_R t) (L_L t)).lower
        (exitCapWindow γ s t δ ε (L_R t) (L_L t)).upper := by
  classical
  let R : ℝ → ℝ := fun t ↦ min ‖γ (t - δ) - s‖ ‖γ (t + δ) - s‖
  by_cases hT : T.Nonempty
  · obtain ⟨t₀, ht₀, hmin⟩ := T.exists_min_image R hT
    have hRpos : 0 < R t₀ := by
      dsimp [R]
      exact lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr (hendpoint t₀ ht₀).1))
        (norm_pos_iff.mpr (sub_ne_zero.mpr (hendpoint t₀ ht₀).2))
    refine ⟨R t₀, hRpos, ?_, ?_⟩
    · intro t ht
      have hεmin : R t₀ ≤ min ‖γ (t - δ) - s‖ ‖γ (t + δ) - s‖ := hmin t ht
      exact ⟨hεmin.trans (min_le_left _ _), hεmin.trans (min_le_right _ _)⟩
    · intro t ht
      have hεmin : R t₀ ≤ min ‖γ (t - δ) - s‖ ‖γ (t + δ) - s‖ := hmin t ht
      have hεL := hεmin.trans (min_le_left _ _)
      have hεR := hεmin.trans (min_le_right _ _)
      exact ⟨exitCapWindow_lower_lt hδ hRpos (h_at t ht)
          ((hγ t ht).mono (Icc_subset_Icc le_rfl (by linarith))) hεL,
        lt_exitCapWindow_upper hδ hRpos (h_at t ht)
          ((hγ t ht).mono (Icc_subset_Icc (by linarith) le_rfl)) hεR⟩
  · refine ⟨1, one_pos, ?_, ?_⟩
    · intro t ht
      exact (hT ⟨t, ht⟩).elim
    · intro t ht
      exact (hT ⟨t, ht⟩).elim

/-- **The Cauchy principal value on an exit-time window.**  Around an interior crossing of a
piecewise-`C¹` immersion, there is an ambient radius `R` and nonzero one-sided tangent limits such
that every smaller ambient window containing no other crossing has the following property.  For
each positive spatial exit radius reached on both sides, the Cauchy-kernel principal value on the
generally asymmetric interval between the two first exits is

`i * (arg (-L_L / (γ(lower) - s)) + arg ((γ(upper) - s) / L_R))`.

The real logarithmic term vanishes because both exit chords have the same norm.  This is the
analytic input that `windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi` consumes in
Hungerbühler--Wasem Proposition 2.2. -/
theorem exists_radius_hasCauchyPVAt_exitCapWindow {γ : ℝ → ℂ} {s : ℂ} {a b t₀ : ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b) (ht₀ : t₀ ∈ Ioo a b)
    (h_at : γ t₀ = s) :
    ∃ R > 0, ∃ L_R L_L : ℂ, L_R ≠ 0 ∧ L_L ≠ 0 ∧
      Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R) ∧ Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ R → a < t₀ - δ → t₀ + δ ≤ b →
      (∀ t ∈ Icc (t₀ - δ) (t₀ + δ), γ t = s → t = t₀) →
      ∀ ε : ℝ, 0 < ε → ε ≤ ‖γ (t₀ - δ) - s‖ → ε ≤ ‖γ (t₀ + δ) - s‖ →
      HasCauchyPVAt γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower
        (exitCapWindow γ s t₀ δ ε L_R L_L).upper (fun z ↦ (z - s)⁻¹) s
        (((((-L_L) / (γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s)).arg +
          ((γ (exitCapWindow γ s t₀ δ ε L_R L_L).upper - s) / L_R).arg : ℝ) : ℂ) *
            Complex.I) := by
  obtain ⟨R, hR, L_R, L_L, hL_R, hL_L, h_R, h_L, hspec⟩ :=
    exists_radius_perWindow_tendsto_log_norm_add_arg h_imm hab ht₀ h_at
  refine ⟨R, hR, L_R, L_L, hL_R, hL_L, h_R, h_L, ?_⟩
  intro δ hδ hδR ha hb h_unique ε hε hεL hεR
  let W := exitCapWindow γ s t₀ δ ε L_R L_L
  have hγ : ContinuousOn γ (Icc (t₀ - δ) (t₀ + δ)) :=
    h_imm.continuousOn.mono (by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc ha.le hb)
  have hγL : ContinuousOn γ (Icc (t₀ - δ) t₀) :=
    hγ.mono (Icc_subset_Icc le_rfl (by linarith))
  have hγR : ContinuousOn γ (Icc t₀ (t₀ + δ)) :=
    hγ.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hlt : W.lower < t₀ := exitCapWindow_lower_lt hδ hε h_at hγL hεL
  have htu : t₀ < W.upper := lt_exitCapWindow_upper hδ hε h_at hγR hεR
  have hlower_mem := firstExitTimeLeft_mem_Icc hδ.le hεL
  have hupper_mem := firstExitTimeRight_mem_Icc hδ.le hεR
  have hnormL : ‖γ W.lower - s‖ = ε :=
    norm_sub_exitCapWindow_lower_eq hδ hε h_at hγL hεL
  have hnormR : ‖γ W.upper - s‖ = ε :=
    norm_sub_exitCapWindow_upper_eq hδ hε h_at hγR hεR
  have hW_lower : t₀ - δ ≤ W.lower := by
    dsimp [W]
    rw [exitCapWindow_lower]
    exact hlower_mem.1
  have hW_upper : W.upper ≤ t₀ + δ := by
    dsimp [W]
    rw [exitCapWindow_upper]
    exact hupper_mem.2
  have htend := hspec W.lower W.upper
    (by linarith) hlt htu (by linarith) (ha.trans_le hW_lower) (hW_upper.trans hb)
    (fun t ht heq => h_unique t
      ⟨hW_lower.trans ht.1, ht.2.trans hW_upper⟩ heq)
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact intervalIntegrable_inv_sub_truncated
      (h_imm.continuousOn.mono (by
        rw [uIcc_of_le hab.le, uIcc_of_le (hlt.le.trans htu.le)]
        exact Icc_subset_Icc (by linarith [ha, hlower_mem.1])
          (hupper_mem.2.trans hb)))
      (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
        rw [uIcc_of_le (hlt.le.trans htu.le), uIcc_of_le hab.le]
        exact Icc_subset_Icc (by linarith [ha, hlower_mem.1]) (hupper_mem.2.trans hb))) hη
  · rw [hnormR, hnormL] at htend
    simpa only [W, sub_self, Complex.ofReal_zero, zero_add] using htend

/-- **The exact local angle contribution of one exit-time cap window.**  The winding number of
the curve over the window minus that of its cap is `crossingAngle γ t₀ / 2π`.  Beyond the
standing continuity, tangent, and radius hypotheses -- which already give equal endpoint radii
and endpoint matching -- the only extra input is the principal value of `(z - s)⁻¹` along the
generally asymmetric exit-time interval. -/
theorem windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi {γ : ℝ → ℂ} {s : ℂ}
    {t₀ δ ε : ℝ} {L_R L_L : ℂ} (hδ : 0 < δ) (hε : 0 < ε) (h_at : γ t₀ = s)
    (hγ : ContinuousOn γ (Icc (t₀ - δ) (t₀ + δ)))
    (hεL : ε ≤ ‖γ (t₀ - δ) - s‖) (hεR : ε ≤ ‖γ (t₀ + δ) - s‖)
    (hL_R : L_R ≠ 0) (hL_L : L_L ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L))
    (hpv : HasCauchyPVAt γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower
      (exitCapWindow γ s t₀ δ ε L_R L_L).upper (fun z ↦ (z - s)⁻¹) s
      (((((-L_L) / (γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s)).arg +
        ((γ (exitCapWindow γ s t₀ δ ε L_R L_L).upper - s) / L_R).arg : ℝ) : ℂ) * Complex.I)) :
    windingNumber γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower
        (exitCapWindow γ s t₀ δ ε L_R L_L).upper s -
      windingNumber ((exitCapWindow γ s t₀ δ ε L_R L_L).cap s)
        (exitCapWindow γ s t₀ δ ε L_R L_L).lower
        (exitCapWindow γ s t₀ δ ε L_R L_L).upper s =
      (crossingAngle γ t₀ : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hγL : ContinuousOn γ (Icc (t₀ - δ) t₀) := hγ.mono (Icc_subset_Icc le_rfl (by linarith))
  have hγR : ContinuousOn γ (Icc t₀ (t₀ + δ)) := hγ.mono (Icc_subset_Icc (by linarith) le_rfl)
  have hnormL := norm_sub_exitCapWindow_lower_eq (L_R := L_R) (L_L := L_L)
    hδ hε h_at hγL hεL
  have hnormR := norm_sub_exitCapWindow_upper_eq (L_R := L_R) (L_L := L_L)
    hδ hε h_at hγR hεR
  have hne : (exitCapWindow γ s t₀ δ ε L_R L_L).lower ≠
      (exitCapWindow γ s t₀ δ ε L_R L_L).upper :=
    ((exitCapWindow_lower_lt hδ hε h_at hγL hεL).trans
      (lt_exitCapWindow_upper hδ hε h_at hγR hεR)).ne
  have hwL : γ (exitCapWindow γ s t₀ δ ε L_R L_L).lower - s ≠ 0 := by
    rw [← norm_pos_iff, hnormL]
    exact hε
  rw [cap_exitCapWindow_eq_circleCap hnormL]
  exact (windingNumber_sub_circleCap_eq_crossingAngle_div_two_pi (γ := γ) (s := s) (t₀ := t₀)
    (L_R := L_R) (L_L := L_L) hL_L hL_R hwL hne rfl rfl (hnormL.trans hnormR.symm) h_R h_L
    hpv).2.2

end TauCeti.Contour

end
