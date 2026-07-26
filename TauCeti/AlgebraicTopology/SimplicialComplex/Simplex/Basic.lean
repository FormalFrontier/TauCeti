/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Abstract simplices and their boundaries

This file defines the abstract simplex spanned by a finite set of vertices and its boundary.
Both are `PreAbstractSimplicialComplex`es on the original ambient vertex type: this lets the
construction remember exactly which vertices occur, unlike `AbstractSimplicialComplex`, which
must contain every singleton of its ambient type.

The boundary consists of the nonempty proper subsets of the spanning vertex set. These
constructions provide the standard models needed for the recursive definitions of combinatorial
spheres and balls in layer 11 of the geometric-topology roadmap.

The definitions follow Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.

## Main definitions

* `PreAbstractSimplicialComplex.simplex`: the complex of nonempty subsets of a finite vertex set.
* `PreAbstractSimplicialComplex.simplexBoundary`: its proper faces.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- The abstract simplex spanned by `V`: its faces are the nonempty subsets of `V`. -/
def simplex (V : Finset ι) : _root_.PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ σ ⊆ V}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hσV⟩
    exact ⟨hσ, fun _ hτσ hτ => ⟨hτ, hτσ.trans hσV⟩⟩

/-- The boundary of the abstract simplex spanned by `V`: its faces are the nonempty proper
subsets of `V`. -/
def simplexBoundary (V : Finset ι) : _root_.PreAbstractSimplicialComplex ι where
  faces := {σ | σ.Nonempty ∧ σ ⊂ V}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hσV⟩
    refine ⟨hσ, fun _ hτσ hτ => ⟨hτ, hτσ.trans_ssubset hσV⟩⟩

variable {K : _root_.PreAbstractSimplicialComplex ι} {V W σ : Finset ι}

/-- A finite set is a face of a simplex exactly when it is nonempty and contained in the
spanning vertex set. -/
@[simp]
theorem mem_simplex : σ ∈ simplex V ↔ σ.Nonempty ∧ σ ⊆ V :=
  Iff.rfl

/-- A finite set is a face of a simplex boundary exactly when it is a nonempty proper subset of
the spanning vertex set. -/
@[simp]
theorem mem_simplexBoundary : σ ∈ simplexBoundary V ↔ σ.Nonempty ∧ σ ⊂ V :=
  Iff.rfl

/-- The spanning vertex set is a face of its simplex exactly when it is nonempty. -/
theorem self_mem_simplex : V ∈ simplex V ↔ V.Nonempty := by
  simp

/-- The spanning vertex set is not a face of its own boundary. -/
theorem self_notMem_simplexBoundary : V ∉ simplexBoundary V := by
  simp

/-- A vertex belongs to the spanning set exactly when its singleton is a face of the simplex. -/
theorem singleton_mem_simplex {v : ι} : {v} ∈ simplex V ↔ v ∈ V := by
  simp

/-- A singleton is a boundary face exactly when its vertex belongs to a spanning set containing
at least one other vertex. -/
theorem singleton_mem_simplexBoundary {v : ι} :
    {v} ∈ simplexBoundary V ↔ v ∈ V ∧ V ≠ {v} := by
  simp only [mem_simplexBoundary, Finset.singleton_nonempty, true_and]
  rw [Finset.ssubset_iff_subset_ne, Finset.singleton_subset_iff]
  constructor
  · exact fun ⟨hv, hne⟩ => ⟨hv, hne.symm⟩
  · exact fun ⟨hv, hne⟩ => ⟨hv, hne.symm⟩

/-- The boundary is a subcomplex of the simplex. -/
theorem simplexBoundary_le_simplex : simplexBoundary V ≤ simplex V :=
  fun _ hσ => ⟨hσ.1, hσ.2.subset⟩

/-- The boundary of a simplex with nonempty spanning set is a strict subcomplex of the simplex. -/
theorem simplexBoundary_lt_simplex (hV : V.Nonempty) : simplexBoundary V < simplex V := by
  refine lt_of_le_of_ne simplexBoundary_le_simplex ?_
  intro h
  have : V ∈ simplexBoundary V := h ▸ (self_mem_simplex.mpr hV : V ∈ simplex V)
  exact self_notMem_simplexBoundary this

/-- The simplex on the empty spanning set has no faces. -/
@[simp]
theorem simplex_empty : simplex (∅ : Finset ι) = ⊥ := by
  ext σ
  constructor
  · intro hσ
    exact hσ.1.ne_empty (Finset.subset_empty.mp hσ.2)
  · exact False.elim

/-- The boundary of the empty simplex has no faces. -/
@[simp]
theorem simplexBoundary_empty : simplexBoundary (∅ : Finset ι) = ⊥ := by
  ext σ
  constructor
  · intro hσ
    exact hσ.1.ne_empty (Finset.subset_empty.mp hσ.2.subset)
  · exact False.elim

/-- The boundary of a one-vertex simplex is empty. -/
@[simp]
theorem simplexBoundary_singleton (v : ι) : simplexBoundary {v} = ⊥ := by
  ext σ
  constructor
  · intro hσ
    exact hσ.1.ne_empty (Finset.ssubset_singleton_iff.mp hσ.2)
  · exact False.elim

/-- The simplex on `V` is contained in a complex exactly when `V` is a face of the complex
whenever `V` is nonempty.  For `V = ∅` the simplex is `⊥`, so it is contained in every complex. -/
theorem simplex_le_iff : simplex V ≤ K ↔ (V.Nonempty → V ∈ K) := by
  constructor
  · exact fun h hV => h (self_mem_simplex.mpr hV)
  · intro h σ hσ
    obtain ⟨x, hx⟩ := hσ.1
    exact (K.isRelLowerSet_faces (h ⟨x, hσ.2 hx⟩)).2 hσ.2 hσ.1

/-- Simplices are ordered exactly when their spanning vertex sets are ordered. -/
theorem simplex_le_simplex_iff : simplex V ≤ simplex W ↔ V ⊆ W := by
  rw [simplex_le_iff]
  constructor
  · intro h
    rcases V.eq_empty_or_nonempty with rfl | hV
    · exact Finset.empty_subset W
    · exact (mem_simplex.mp (h hV)).2
  · exact fun h hV => mem_simplex.mpr ⟨hV, h⟩

/-- Enlarging the spanning vertex set enlarges the simplex. -/
theorem simplex_mono (h : V ⊆ W) : simplex V ≤ simplex W :=
  fun _ hσ => ⟨hσ.1, hσ.2.trans h⟩

/-- Enlarging the spanning vertex set enlarges the boundary. -/
theorem simplexBoundary_mono (h : V ⊆ W) : simplexBoundary V ≤ simplexBoundary W := by
  intro σ hσ
  refine ⟨hσ.1, ?_⟩
  exact hσ.2.trans_le h

/-- A face of a simplex lies in its boundary exactly when it is not the whole spanning set. -/
theorem mem_simplexBoundary_iff_mem_simplex_ne :
    σ ∈ simplexBoundary V ↔ σ ∈ simplex V ∧ σ ≠ V := by
  simp only [mem_simplexBoundary, mem_simplex, Finset.ssubset_iff_subset_ne]
  tauto

/-- The faces of a simplex are its boundary faces together with the spanning set itself, the
latter only when the spanning set is nonempty. -/
theorem mem_simplex_iff_mem_simplexBoundary_or_eq :
    σ ∈ simplex V ↔ σ ∈ simplexBoundary V ∨ V.Nonempty ∧ σ = V := by
  rw [mem_simplexBoundary_iff_mem_simplex_ne]
  constructor
  · intro hσ
    rcases eq_or_ne σ V with rfl | hne
    · exact Or.inr ⟨hσ.1, rfl⟩
    · exact Or.inl ⟨hσ, hne⟩
  · rintro (⟨hσ, -⟩ | ⟨hV, rfl⟩)
    · exact hσ
    · exact self_mem_simplex.mpr hV

end PreAbstractSimplicialComplex

end TauCeti
