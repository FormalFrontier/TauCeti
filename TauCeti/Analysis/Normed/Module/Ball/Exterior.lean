/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Topology.FilledHull

/-!
# The exterior of a ball is connected, and the unbounded component is unique

In a real normed space of dimension at least two the complement of a closed ball is preconnected:
it is the union, over the radii `M` exceeding the ball's, of the spheres of radius `M`, strung
together along a single ray from the centre. Consequently the complement of a *bounded* set has at
most one unbounded connected component, and two points of the complement that lie in different
components cannot both be outside `TauCeti.filledHull K`.

## Main results

* `TauCeti.isPreconnected_compl_closedBall` — the exterior of a closed ball is preconnected in a
  real normed space of dimension at least two.
* `TauCeti.connectedComponentIn_compl_eq_of_unbounded_component` — the unbounded connected
  component of the complement of a bounded set is unique (dimension at least two).
* `TauCeti.mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn` — of two points in
  different components, at least one lies in the filled hull (dimension at least two).

This is a prerequisite of the planar-separation step of the `ConformalMapping` roadmap (L5).
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {x y : E}

/-- **The exterior of a closed ball is preconnected** in a real normed space of dimension at least
two. -/
theorem isPreconnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (closedBall x r)ᶜ := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [closedBall_eq_empty.mpr hr, compl_empty]
    exact isPreconnected_univ
  have : Nontrivial E := rank_pos_iff_nontrivial.mp (zero_lt_one.trans h)
  obtain ⟨u, hu⟩ := exists_norm_eq E zero_le_one
  set L : Set E := (fun t : ℝ => x + t • u) '' Ioi r
  have hLc : IsPreconnected L :=
    isPreconnected_Ioi.image _ (by fun_prop : Continuous fun t : ℝ => x + t • u).continuousOn
  have hLmem : ∀ t, r < t → x + t • u ∈ L := fun t ht => ⟨t, ht, rfl⟩
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖x + t • u - x‖ = t := by
    intro t ht
    rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_nonneg ht]
  have hLsub : L ⊆ (closedBall x r)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_compl_iff, mem_closedBall, dist_eq_norm, hnorm t (hr.trans ht.le), not_le]
    exact ht
  have key : (closedBall x r)ᶜ = ⋃ M : Ioi r, (sphere x M ∪ L) := by
    ext w
    constructor
    · intro hw
      have hwM : r < ‖w - x‖ := by
        rwa [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hw
      exact mem_iUnion.mpr ⟨⟨‖w - x‖, hwM⟩, Or.inl (by rw [mem_sphere, dist_eq_norm])⟩
    · intro hw
      obtain ⟨⟨M, hM⟩, hwM⟩ := mem_iUnion.mp hw
      rcases hwM with hwM | hwM
      · rw [mem_sphere, dist_eq_norm] at hwM
        rw [mem_compl_iff, mem_closedBall, dist_eq_norm, hwM, not_le]
        exact hM
      · exact hLsub hwM
  rw [key]
  refine isPreconnected_iUnion ⟨x + (r + 1) • u, ?_⟩ fun ⟨M, hM⟩ => ?_
  · simp only [mem_iInter]
    exact fun _ => Or.inr (hLmem _ (by linarith))
  · refine IsPreconnected.union (x + M • u) ?_ (hLmem M hM) (isPreconnected_sphere h x M) hLc
    rw [mem_sphere, dist_eq_norm, hnorm M (hr.trans hM.le)]

/-- **The unbounded component of the complement of a bounded set is unique** in a real normed space
of dimension at least two. -/
theorem connectedComponentIn_compl_eq_of_unbounded_component (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hx : ¬ IsBounded (connectedComponentIn Kᶜ x))
    (hy : ¬ IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall (0 : E)
  have hext : (closedBall (0 : E) R)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hR
  have hesc : ∀ z : E, ¬ IsBounded (connectedComponentIn Kᶜ z) →
      ∃ z' ∈ connectedComponentIn Kᶜ z, z' ∈ (closedBall (0 : E) R)ᶜ := fun z hz => by
    by_contra hcon
    push Not at hcon
    exact hz ((isBounded_closedBall (x := (0 : E)) (r := R)).subset fun w hw =>
      notMem_compl_iff.mp (hcon w hw))
  obtain ⟨x', hx'c, hx'R⟩ := hesc x hx
  obtain ⟨y', hy'c, hy'R⟩ := hesc y hy
  have h1 : y' ∈ connectedComponentIn Kᶜ x' :=
    (isPreconnected_compl_closedBall h 0 R).subset_connectedComponentIn hx'R hext hy'R
  rw [connectedComponentIn_eq hx'c, connectedComponentIn_eq h1, ← connectedComponentIn_eq hy'c]

/-- **Two points in different components of the complement of a bounded set cannot both lie outside
the filled hull** in a real normed space of dimension at least two. -/
theorem mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn (h : 1 < Module.rank ℝ E)
    (hK : IsBounded K) (hxy : y ∉ connectedComponentIn Kᶜ x) :
    x ∈ filledHull K ∨ y ∈ filledHull K := by
  by_cases hy : y ∈ K
  · exact Or.inr (subset_filledHull hy)
  · by_contra hcon
    push Not at hcon
    simp only [mem_filledHull_iff] at hcon
    exact hxy ((connectedComponentIn_compl_eq_of_unbounded_component h hK hcon.1 hcon.2).symm ▸
      mem_connectedComponentIn (mem_compl hy))

end TauCeti
