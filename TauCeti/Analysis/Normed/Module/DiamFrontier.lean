/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import TauCeti.Topology.Frontier

/-!
# A bounded set is exactly as wide as its frontier

In a real normed space a bounded set `V` and its frontier have the same diameter:
`TauCeti.diam_frontier`. One inequality is trivial, `frontier V` being contained in `closure V`.
The other says that the frontier already realises every distance realised inside `V`, and it is
the geometric content: a set cannot be wide and have a narrow boundary.

The mechanism is that a ray leaving a bounded set has to cross the frontier, and crossing it only
*later* than it passes through a given point of the set. Precisely
(`TauCeti.exists_mem_frontier_dist_le`), for `x ∈ V` and any base point `y ≠ x` the ray
`t ↦ y + t • (x - y)`, followed from `t = 1` outwards, eventually leaves the bounded set `V`, and
the segment it traces is connected, so `TauCeti.IsPreconnected.inter_frontier_nonempty` produces a
frontier point `p = y + t • (x - y)` with `t ≥ 1`, whence `dist y p = t * dist y x ≥ dist y x`.

Applying this twice turns a pair of points of `V` into a pair of frontier points at least as far
apart: first push `x` away from `y` to a frontier point `p`, then push `y` away from `p` to a
frontier point `q`, and `dist x y ≤ dist y p ≤ dist p q`. Boundedness is essential and not merely
a convenience of `Metric.diam`, which vanishes on unbounded sets: in `ℝ` the unbounded set
`Metric.ball 0 1 ∪ Set.Ici 2` has frontier `{-1, 1, 2}` of diameter `3`.

Nothing here needs `V` to be open, connected, or measurable, and the ambient space is an arbitrary
real normed space: only the segment and the norm are used.

The intended consumer is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, Carathéodory's
boundary correspondence. There the piece of a domain that a crosscut cuts off has to be shown small,
and what is small is its boundary — the crosscut itself together with the arc of the domain boundary
it separates; `TauCeti.diam_frontier` is what converts that into a bound on the piece.
`TauCeti/Analysis/Complex/Conformal/CutDiameter.lean` carries out that conversion.

## Main results

* `TauCeti.exists_mem_frontier_dist_le` — from a point of a bounded set, the ray away from any other
  base point reaches the frontier no sooner than it reaches that point.
* `TauCeti.diam_le_diam_frontier` and `TauCeti.diam_frontier` — a bounded set is exactly as wide as
  its frontier.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {x y : E}

/-- **A ray leaving a bounded set crosses its frontier, and does so no sooner than it passes
through a given point of the set.** For `x` in a bounded set `V` and any base point `y ≠ x`, the
ray from `y` through `x` meets `frontier V` at a point `p` with `dist y x ≤ dist y p`.

The ray is followed from `x` outwards. It leaves `V` because `V` is bounded, the segment traced is
connected, and `TauCeti.IsPreconnected.inter_frontier_nonempty` therefore hands back a frontier
point on it; being beyond `x` on the ray, that point is at least as far from `y` as `x` is. -/
theorem exists_mem_frontier_dist_le (hV : IsBounded V) (hx : x ∈ V) (hne : y ≠ x) :
    ∃ p ∈ frontier V, dist y x ≤ dist y p := by
  obtain ⟨R, hR⟩ := hV.subset_closedBall y
  set d : E := x - y with hd
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  set γ : ℝ → E := fun t => y + t • d with hγ
  have hγdist : ∀ t : ℝ, 0 ≤ t → dist y (γ t) = t * ‖d‖ := by
    intro t ht
    rw [hγ, dist_eq_norm]
    simp [norm_smul, abs_of_nonneg ht]
  have hγ1 : γ 1 = x := by simp [hγ, hd]
  set T : ℝ := max 1 ((R + 1) / ‖d‖) with hT
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hTd : R + 1 ≤ T * ‖d‖ := by
    have := le_max_right 1 ((R + 1) / ‖d‖)
    calc R + 1 = (R + 1) / ‖d‖ * ‖d‖ := by field_simp
      _ ≤ T * ‖d‖ := by gcongr
  have hTV : γ T ∉ V := by
    intro hmem
    have := mem_closedBall.mp (hR hmem)
    rw [dist_comm] at this
    rw [hγdist T (by linarith)] at this
    linarith
  have hcont : Continuous γ := by fun_prop
  have hSconn : IsPreconnected (γ '' Icc 1 T) :=
    isPreconnected_Icc.image γ hcont.continuousOn
  obtain ⟨p, hpS, hpf⟩ := IsPreconnected.inter_frontier_nonempty hSconn
    ⟨x, ⟨1, ⟨le_rfl, hT1⟩, hγ1⟩, hx⟩ ⟨γ T, ⟨T, ⟨hT1, le_rfl⟩, rfl⟩, hTV⟩
  obtain ⟨t, ht, rfl⟩ := hpS
  refine ⟨γ t, hpf, ?_⟩
  rw [← hγ1, hγdist 1 zero_le_one, hγdist t (by linarith [ht.1])]
  nlinarith [ht.1]

/-- **A bounded set is no wider than its frontier.** Every distance realised between two points of
a bounded set `V` is already realised between two points of `frontier V`: push the first point away
from the second to the frontier, then the second away from the resulting frontier point. -/
theorem diam_le_diam_frontier (hV : IsBounded V) : diam V ≤ diam (frontier V) := by
  have hfb : IsBounded (frontier V) := hV.closure.subset frontier_subset_closure
  refine diam_le_of_forall_dist_le diam_nonneg fun a ha b hb => ?_
  rcases eq_or_ne a b with rfl | hab
  · simpa using diam_nonneg
  obtain ⟨p, hp, hple⟩ := exists_mem_frontier_dist_le hV ha hab.symm
  have hpb : p ≠ b := by
    rintro rfl
    exact hab (dist_le_zero.mp (le_trans hple (by simp))).symm
  obtain ⟨q, hq, hqle⟩ := exists_mem_frontier_dist_le hV hb hpb
  calc dist a b = dist b a := dist_comm a b
    _ ≤ dist b p := hple
    _ = dist p b := dist_comm b p
    _ ≤ dist p q := hqle
    _ ≤ diam (frontier V) := dist_le_diam_of_mem hfb hp hq

/-- **The diameter of a bounded set is the diameter of its frontier.** The frontier is contained in
the closure, which gives one inequality, and `TauCeti.diam_le_diam_frontier` gives the other.

Boundedness cannot be dropped: `Metric.diam` is `0` on an unbounded set, while the frontier of
`Metric.ball 0 1 ∪ Set.Ici 2` in `ℝ` is `{-1, 1, 2}`. -/
theorem diam_frontier (hV : IsBounded V) : diam (frontier V) = diam V := by
  refine le_antisymm ?_ (diam_le_diam_frontier hV)
  calc diam (frontier V) ≤ diam (closure V) := diam_mono frontier_subset_closure hV.closure
    _ = diam V := diam_closure V

end TauCeti
