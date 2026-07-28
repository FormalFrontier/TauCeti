/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
  have hw : w ∈ (γ '' uIcc a b)ᶜ := by
    by_contra hw
    apply hcomp
    rw [connectedComponentIn_eq_empty hw]
    exact isBounded_empty
  obtain ⟨K, hK_compact, hK_good⟩ :=
    Filter.mem_cocompact.mp
      (windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int)
  have hnot_subset : ¬connectedComponentIn ((γ '' uIcc a b)ᶜ) w ⊆ K :=
    fun hsubset ↦ hcomp (hK_compact.isBounded.subset hsubset)
  obtain ⟨w', hw'_comp, hw'_notK⟩ := Set.not_subset.mp hnot_subset
  have hw'_zero : windingNumber γ a b w' = 0 := (hK_good hw'_notK).2
  exact
    (windingNumber_eq_of_mem_connectedComponentIn hclosed hP hγ_cont hγ_diff hderiv_int
      hw hw'_comp).symm.trans hw'_zero

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

end TauCeti.Contour
