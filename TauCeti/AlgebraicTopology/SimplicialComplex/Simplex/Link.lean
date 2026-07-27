/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Links and stars in abstract simplices

This file computes the closed star, link, and deletion constructions on the standard abstract
simplex and its boundary.  These formulas are the standard-model calculations used by the
recursive link condition for combinatorial manifolds in layer 11 of the geometric-topology
roadmap.  In particular, the link of a subset in a simplex is the simplex on the complementary
vertices, while the link in the boundary is the boundary of that complementary simplex.

The constructions use `PreAbstractSimplicialComplex`, since taking a link changes the vertices
that occur.  The formulas follow Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2.

## Main results

* `closedStar_simplex`: the closed star of a subset is the whole simplex.
* `link_simplex`: the link of a subset is the simplex on its complementary vertices.
* `deletion_simplex_self`: deleting the full vertex set leaves the simplex boundary.
* `link_simplexBoundary`: the link of a subset is the boundary on its complementary
  vertices.
-/

public section

namespace TauCeti

open Finset

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]
variable {V σ : Finset ι}

/-- The closed star of any subset `σ ⊆ V` in the simplex on `V` is the entire simplex. -/
@[simp]
theorem closedStar_simplex (hσ : σ ⊆ V) : closedStar (simplex V) σ = simplex V := by
  apply SetLike.ext
  intro ρ
  rw [mem_closedStar, mem_simplex, mem_simplex]
  constructor
  · exact fun h => ⟨h.1, subset_union_left.trans h.2.2⟩
  · exact fun h => ⟨h.1, h.1.mono subset_union_left, union_subset h.2 hσ⟩

/-- The link of any subset `σ ⊆ V` in the simplex on `V` is the simplex on the vertices of `V`
not in `σ`. -/
@[simp]
theorem link_simplex (hσ : σ ⊆ V) : link (simplex V) σ = simplex (V \ σ) := by
  apply SetLike.ext
  intro ρ
  rw [mem_link, mem_simplex, mem_simplex]
  constructor
  · rintro ⟨hρ, hdis, -, hρσ⟩
    refine ⟨hρ, subset_sdiff.mpr ⟨subset_union_left.trans hρσ, ?_⟩⟩
    exact hdis
  · rintro ⟨hρ, hρV⟩
    have hρV' : ρ ⊆ V := hρV.trans sdiff_subset
    have hdis : Disjoint ρ σ := disjoint_sdiff_self_left.mono_left hρV
    exact ⟨hρ, hdis, (hρ.mono subset_union_left), union_subset hρV' hσ⟩

omit [DecidableEq ι] in
/-- Deleting the full vertex set from a simplex leaves exactly its boundary. -/
@[simp]
theorem deletion_simplex_self : deletion (simplex V) V = simplexBoundary V := by
  apply SetLike.ext
  intro ρ
  rw [mem_deletion, mem_simplexBoundary_iff_mem_simplex_ne]
  constructor
  · rintro ⟨hρ, hVρ⟩
    exact ⟨hρ, fun hρV => hVρ hρV.symm.subset⟩
  · rintro ⟨hρ, hρV⟩
    exact ⟨hρ, fun hVρ => hρV (Subset.antisymm (mem_simplex.mp hρ).2 hVρ)⟩

/-- A set `ρ` lies in the closed star of `σ` in the boundary of the simplex on `V` exactly when
`ρ` is nonempty and `ρ ∪ σ` is a proper subset of `V`. -/
theorem mem_closedStar_simplexBoundary {ρ : Finset ι} :
    ρ ∈ closedStar (simplexBoundary V) σ ↔ ρ.Nonempty ∧ ρ ∪ σ ⊂ V := by
  rw [mem_closedStar, mem_simplexBoundary]
  constructor
  · exact fun h => ⟨h.1, h.2.2⟩
  · exact fun h => ⟨h.1, h.1.mono subset_union_left, h.2⟩

/-- The link of any subset `σ ⊆ V` in the boundary of the simplex on `V` is the boundary of the
simplex on the complementary vertices. -/
@[simp]
theorem link_simplexBoundary (hσ : σ ⊆ V) :
    link (simplexBoundary V) σ = simplexBoundary (V \ σ) := by
  apply SetLike.ext
  intro ρ
  rw [mem_link, mem_simplexBoundary, mem_simplexBoundary]
  constructor
  · rintro ⟨hρ, hdis, -, hρσ⟩
    refine ⟨hρ, Finset.ssubset_iff_subset_ne.mpr ⟨subset_sdiff.mpr
      ⟨subset_union_left.trans hρσ.subset, hdis⟩, ?_⟩⟩
    intro hρeq
    apply hρσ.ne
    rw [hρeq, sdiff_union_of_subset hσ]
  · rintro ⟨hρ, hρdiff⟩
    have hρV : ρ ⊆ V := hρdiff.subset.trans sdiff_subset
    have hdis : Disjoint ρ σ := disjoint_sdiff_self_left.mono_left hρdiff.subset
    refine ⟨hρ, hdis, hρ.mono subset_union_left, ?_⟩
    refine Finset.ssubset_iff_subset_ne.mpr ⟨union_subset hρV hσ, ?_⟩
    intro hρσeq
    apply hρdiff.ne
    rw [← hρσeq, union_sdiff_cancel_right hdis]

/-- The link of the full vertex set in its simplex is empty.  (`simp` also proves this via
`link_simplex`; the named form is kept for convenience.) -/
theorem link_simplex_self : link (simplex V) V = ⊥ := by
  rw [link_simplex Subset.rfl, sdiff_self, bot_eq_empty]
  exact simplex_empty

/-- The link of the full vertex set `V` in the boundary of the simplex on `V` is empty (note `V`
itself is not a face of that boundary).  The statement also covers the empty spanning set.
(`simp` also proves this via `link_simplexBoundary`; the named form is kept for convenience.) -/
theorem link_simplexBoundary_self : link (simplexBoundary V) V = ⊥ := by
  rw [link_simplexBoundary Subset.rfl, sdiff_self, bot_eq_empty]
  exact simplexBoundary_empty

end PreAbstractSimplicialComplex

end TauCeti
