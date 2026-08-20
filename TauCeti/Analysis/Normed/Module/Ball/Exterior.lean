/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The exterior of a closed ball is preconnected

In a real normed space of dimension at least two the complement of a closed ball is preconnected:
it is the union, over the radii `M` exceeding the ball's, of the spheres of radius `M`, strung
together along a single ray from the centre.

The consequences for bounded sets — uniqueness of the unbounded component and the filled-hull
alternative — are in `TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.isPreconnected_compl_closedBall` — the exterior of a closed ball is preconnected in a
  real normed space of dimension at least two.

This is a prerequisite of the planar-separation step of the `ConformalMapping` roadmap (L5).

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
  have hdist : ∀ t : ℝ, 0 ≤ t → dist (x + t • u) x = t := by
    intro t ht
    simp [dist_eq_norm, norm_smul, hu, abs_of_nonneg ht]
  have hmem : ∀ w, w ∈ (closedBall x r)ᶜ ↔ r < dist w x := by
    simp [mem_closedBall, not_le]
  have hLsub : L ⊆ (closedBall x r)ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hmem, hdist t (hr.trans ht.le)]
    exact ht
  have key : (closedBall x r)ᶜ = ⋃ M : Ioi r, (sphere x M ∪ L) := by
    ext w
    constructor
    · intro hw
      exact mem_iUnion.mpr ⟨⟨dist w x, (hmem w).mp hw⟩, Or.inl (mem_sphere.mpr rfl)⟩
    · intro hw
      obtain ⟨⟨M, hM⟩, hwM⟩ := mem_iUnion.mp hw
      rcases hwM with hwM | hwM
      · rw [hmem]; rw [mem_sphere, dist_comm] at hwM; rw [dist_comm, hwM]; exact hM
      · exact hLsub hwM
  rw [key]
  refine isPreconnected_iUnion ⟨x + (r + 1) • u, ?_⟩ fun ⟨M, hM⟩ => ?_
  · simp only [mem_iInter]
    exact fun _ => Or.inr (hLmem _ (by linarith))
  · refine IsPreconnected.union (x + M • u) ?_ (hLmem M hM) (isPreconnected_sphere h x M) hLc
    rw [mem_sphere, hdist M (hr.trans hM.le)]

end TauCeti
