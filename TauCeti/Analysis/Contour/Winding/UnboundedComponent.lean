/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Analysis.Contour.Winding.LocallyConstant
public import TauCeti.Analysis.Contour.Winding.Vanishing

/-!
# The winding number on the unbounded component

For a closed curve `γ`, the winding number is constant on every connected component of the
complement of the curve. If such a component is unbounded, it contains a point outside the compact
set on which the far-field vanishing theorem gives no information. At that point the winding
number is zero, and componentwise constancy transports the value back to every point of the
component.

This proves the final part of the classical off-curve winding package in Layer 0 of the contour
integration roadmap: the winding number is zero on the unbounded component.

## Main results

* `TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` — the winding number vanishes on
  every unbounded component of the curve complement.
* `TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component` — the direct
  piecewise-`C¹` form.

## References

* N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Section 2.
-/

public section

open Bornology Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour

/-- **The winding number vanishes on every unbounded component of the curve complement.**
For a closed curve with the usual off-curve regularity, if the connected component of `w` in
`ℂ \ γ '' [[a, b]]` is unbounded, then the winding number about `w` is zero. Unboundedness also
ensures that `w` lies outside the curve.

Indeed, far-field vanishing holds outside some compact set. An unbounded component cannot be
contained in that compact set, so it contains a far-field point with winding number zero; the
winding number is constant on the component. -/
theorem windingNumber_eq_zero_of_unbounded_component {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    {w : ℂ} (hcomp : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) w)) :
    windingNumber γ a b w = 0 := by
  obtain ⟨K, hK_compact, hK_good⟩ :=
    Filter.mem_cocompact.mp
      (windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int)
  have hnot_subset : ¬connectedComponentIn ((γ '' uIcc a b)ᶜ) w ⊆ K :=
    fun hsubset ↦ hcomp (hK_compact.isBounded.subset hsubset)
  obtain ⟨w', hw'_comp, hw'_notK⟩ := Set.not_subset.mp hnot_subset
  have hw'_zero : windingNumber γ a b w' = 0 := (hK_good hw'_notK).2
  exact
    (windingNumber_eq_of_mem_connectedComponentIn hclosed hP hγ_cont hγ_diff hderiv_int
      hw'_comp).symm.trans hw'_zero

/-- **Piecewise-`C¹` form of vanishing on the unbounded component.** If the component of `w` in the
complement of a closed piecewise-`C¹` curve is unbounded, its winding number about `w` is zero. The
finite breakpoint set supplies all raw regularity hypotheses of
`windingNumber_eq_zero_of_unbounded_component`. -/
theorem IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    {w : ℂ} (hcomp : ¬IsBounded (connectedComponentIn ((γ '' uIcc a b)ᶜ) w)) :
    windingNumber γ a b w = 0 := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component hclosed hP
    hγ.continuousOn hγ_diff hγ.intervalIntegrable_deriv hcomp

/-- **The winding number vanishes at a point joined to infinity by a ray off the curve.** If the
ray `c ↦ w + c · v` (`0 ≤ c`, `v ≠ 0`) misses the closed curve, then `w` lies in an unbounded
component of the complement and the winding number about `w` is zero.

This is the form callers can actually discharge: exhibiting one escape ray is elementary, whereas
`IsPiecewiseC1On.windingNumber_eq_zero_of_unbounded_component` asks for the component itself. Any
point outside a bounded region the curve encloses -- outside a disc containing the curve, or on the
far side of a line the curve does not cross -- has such a ray. -/
theorem IsPiecewiseC1On.windingNumber_eq_zero_of_ray {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) {w v : ℂ} (hv : v ≠ 0)
    (hray : ∀ c : ℝ, 0 ≤ c → w + (c : ℂ) * v ∉ γ '' uIcc a b) :
    windingNumber γ a b w = 0 := by
  have hAconn : IsPreconnected ((fun c : ℝ => w + (c : ℂ) * v) '' Ici 0) :=
    isPreconnected_Ici.image (fun c : ℝ => w + (c : ℂ) * v)
      (Continuous.continuousOn (by fun_prop))
  have hzero : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have hAmem : w ∈ (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 := ⟨0, hzero, by simp⟩
  have hAsub : (fun c : ℝ => w + (c : ℂ) * v) '' Ici 0 ⊆ (γ '' uIcc a b)ᶜ := by
    rintro _ ⟨c, hc, rfl⟩
    exact hray c hc
  refine hγ.windingNumber_eq_zero_of_unbounded_component hclosed fun hbdd => ?_
  have hsub := hAconn.subset_connectedComponentIn hAmem hAsub
  obtain ⟨r, hr⟩ := (hbdd.subset hsub).subset_closedBall 0
  have hwr : ‖w‖ ≤ r := by simpa using Metric.mem_closedBall.mp (hr ⟨0, hzero, by simp⟩)
  have hrnn : (0 : ℝ) ≤ r := le_trans (norm_nonneg w) hwr
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- Far enough along the ray the norm exceeds `r`, so the ray escapes the ball.
  set c : ℝ := (r + ‖w‖ + 1) / ‖v‖ with hc_def
  have hcnn : 0 ≤ c := by positivity
  have hnorm : ‖(c : ℂ) * v‖ = r + ‖w‖ + 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcnn, hc_def,
      div_mul_cancel₀ _ hvpos.ne']
  have hle : ‖w + (c : ℂ) * v‖ ≤ r := by
    simpa using Metric.mem_closedBall.mp (hr ⟨c, hcnn, rfl⟩)
  have hge : ‖(c : ℂ) * v‖ ≤ ‖w + (c : ℂ) * v‖ + ‖w‖ := by
    simpa using norm_sub_le (w + (c : ℂ) * v) w
  rw [hnorm] at hge
  linarith

end TauCeti.Contour
