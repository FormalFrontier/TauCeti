/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-!
# Uniform distance from an avoided point to a continuous curve

For a curve `γ : ℝ → ℂ` continuous on a compact interval `[a, b]` and avoiding a point `w`, the
image `γ '' [a, b]` is compact and misses `w`, so `w` stays a positive distance from it; this gives
a uniform positive lower bound `ρ` on `‖γ t - w‖` over `[a, b]`.

## Main results

* `TauCeti.Contour.exists_curve_dist_lower_bound` — the uniform positive distance lower bound.
* `TauCeti.Contour.exists_ball_dist_curve_lower_bound` — the same lower bound made uniform over a
  whole ball of points around the avoided point.
* `TauCeti.Contour.exists_mem_off_curve` — an open set containing a curve contains a point off the
  curve: the compact image cannot exhaust a nonempty open subset of the noncompact connected `ℂ`.

These small support lemmas are shared by the argument-lift partition
(`exists_uniform_modulus_avoiding`, feeding the integer-valuedness of the winding number), by the
continuity of the winding number in the point (`continuousAt_windingNumber_of_avoidance`), and by
the homology form of Cauchy's theorem (`homologyCauchyTheorem`), whose Dixon-style proof picks its
base point off the curve via `exists_mem_off_curve`.
-/

public section

open Set

namespace TauCeti.Contour

/-- **Uniform positive distance from an avoided point to a curve.** If `γ` is continuous on the
interval with endpoints `a`, `b` and avoids `w` there, then there is `ρ > 0` with `ρ ≤ ‖γ t - w‖`
for every `t ∈ Set.uIcc a b` (one may take `ρ = Metric.infDist w (γ '' Set.uIcc a b)`). Stated on
the oriented interval `Set.uIcc a b`, matching the winding-number API. -/
theorem exists_curve_dist_lower_bound {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ ρ > 0, ∀ t ∈ uIcc a b, ρ ≤ ‖γ t - w‖ := by
  have h_image_compact : IsCompact (γ '' uIcc a b) := isCompact_uIcc.image_of_continuousOn hγ
  have h_image_nonempty : (γ '' uIcc a b).Nonempty := ⟨γ a, mem_image_of_mem _ left_mem_uIcc⟩
  have h_w_not_mem : w ∉ γ '' uIcc a b := fun ⟨t, ht, heq⟩ ↦ h_avoid t ht heq
  refine ⟨Metric.infDist w (γ '' uIcc a b),
    (h_image_compact.isClosed.notMem_iff_infDist_pos h_image_nonempty).mp h_w_not_mem,
    fun t ht ↦ ?_⟩
  have h1 := Metric.infDist_le_dist_of_mem (x := w) (mem_image_of_mem γ ht)
  rwa [Complex.dist_eq, norm_sub_rev] at h1

/-- **Uniform distance to the curve on a neighbourhood of an avoided point.** If `γ` is continuous
on the interval with endpoints `a`, `b` and avoids `w₀` there, then there is a radius `ε > 0` such
that every `w` within `ε` of `w₀` stays at distance at least `ε` from the whole curve: for all
`t ∈ Set.uIcc a b`, `ε ≤ ‖γ t - w‖`. Stated on the oriented interval `Set.uIcc a b`. -/
theorem exists_ball_dist_curve_lower_bound {γ : ℝ → ℂ} {w₀ : ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ uIcc a b, ε ≤ ‖γ t - w‖ := by
  obtain ⟨ρ, hρ_pos, h_dist_lb⟩ := exists_curve_dist_lower_bound hγ h_avoid
  refine ⟨ρ / 2, half_pos hρ_pos, fun w hw t ht ↦ ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq] at hw
  have htri : ‖γ t - w₀‖ - ‖w - w₀‖ ≤ ‖γ t - w‖ := by
    have h := norm_sub_norm_le (γ t - w₀) (w - w₀)
    rwa [sub_sub_sub_cancel_right] at h
  linarith [h_dist_lb t ht]

/-- **An open set containing a curve contains a point off the curve.** If `γ` is continuous on the
interval with endpoints `a`, `b` and maps it into an open set `Ω ⊆ ℂ`, then some `w₀ ∈ Ω` is not
on the curve. The image is compact, so if it exhausted `Ω` then `Ω` would be a nonempty clopen
subset of the connected `ℂ`, hence all of `ℂ` — which is not compact. This supplies the base point
off the curve that Dixon's proof of the homology Cauchy theorem requires. -/
theorem exists_mem_off_curve {γ : ℝ → ℂ} {Ω : Set ℂ} {a b : ℝ} (hΩ : IsOpen Ω)
    (hγ : ContinuousOn γ (uIcc a b)) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    ∃ w₀ ∈ Ω, ∀ t ∈ uIcc a b, γ t ≠ w₀ := by
  by_contra hcon
  push Not at hcon
  have himg : γ '' uIcc a b = Ω :=
    (image_subset_iff.mpr hγΩ).antisymm fun w hw => by
      obtain ⟨t, ht, hts⟩ := hcon w hw
      exact ⟨t, ht, hts⟩
  have hcompact : IsCompact Ω := himg ▸ isCompact_uIcc.image_of_continuousOn hγ
  have : PreconnectedSpace ℂ := ⟨(convex_univ : Convex ℝ (univ : Set ℂ)).isPreconnected⟩
  have huniv : Ω = univ :=
    IsClopen.eq_univ ⟨hcompact.isClosed, hΩ⟩ ⟨γ a, hγΩ a left_mem_uIcc⟩
  exact noncompact_univ ℂ (huniv ▸ hcompact)

end TauCeti.Contour
