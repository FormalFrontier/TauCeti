/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join

/-!
# Cones of simplicial complexes

The cone on a simplicial complex `K` is its join with a single vertex.  Its vertex type is
`α ⊕ PUnit`: the left summand contains the original vertices and `Sum.inr PUnit.unit` is the
apex.  A face is therefore either an original face, tagged into the left summand, or an original
face together with the apex; the apex by itself is also a face.

Cones are elementary infrastructure for layer 11 of the geometric-topology roadmap.  Recursive
combinatorial balls are obtained by coning combinatorial spheres, and suspensions are formed by
iterated coning/gluing.  This file supplies the combinatorial operation and its face API, building
entirely on the join construction already available in Tau Ceti.

The construction follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter
2.  No result from that source is used beyond the standard definition of a cone as a join with a
point.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.cone`: the cone on a pre-abstract simplicial complex.
* `TauCeti.AbstractSimplicialComplex.cone`: the cone on an abstract simplicial complex.

## Main results

* `mem_cone_iff`: a face of the cone is nonempty and has either an empty base projection or a
  face of the original complex as its base projection.
* `map_inl_mem_cone`: every original face is a face of the cone.
* `apex_mem_cone`: the apex is a face.
* `disjSum_singleton_mem_cone`: adjoining the apex to an original face gives a face.
* `cone_mono`: coning is monotone.
-/

public section

namespace TauCeti

open Finset Function Sum

namespace PreAbstractSimplicialComplex

variable {α : Type*}

/-- The cone on a pre-abstract simplicial complex, defined as its join with the full complex on
the one-point type `PUnit`. -/
public def cone (K : PreAbstractSimplicialComplex α) :
    PreAbstractSimplicialComplex (α ⊕ PUnit) :=
  join K ⊤

variable {K L : PreAbstractSimplicialComplex α}

/-- A finite set is a face of the cone exactly when it is nonempty and its left projection is
either empty or a face of the base complex.  There is no further condition on the right
projection because the apex type has one element. -/
@[simp]
theorem mem_cone_iff {σ : Finset (α ⊕ PUnit)} :
    σ ∈ cone K ↔ σ.Nonempty ∧ (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) := by
  rw [cone, mem_join_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hσ, hleft⟩
    refine ⟨hσ, hleft, ?_⟩
    by_cases hright : σ.toRight = ∅
    · exact Or.inl hright
    · exact Or.inr (Finset.nonempty_iff_ne_empty.mpr hright)

/-- A finite set tagged into the left summand is a face of the cone exactly when it is a face of
the base complex. -/
@[simp]
theorem map_inl_mem_cone_iff {s : Finset α} :
    s.map (Embedding.inl : α ↪ α ⊕ PUnit) ∈ cone K ↔ s ∈ K := by
  rw [← disjSum_empty, cone, disjSum_mem_join_iff]
  constructor
  · rintro ⟨_, hs | hs, _⟩
    · simp_all
    · exact hs
  · exact fun hs => ⟨Or.inl (K.isRelLowerSet_faces hs).1, Or.inr hs, Or.inl rfl⟩

/-- Every face of the base complex, tagged into the left summand, is a face of its cone. -/
theorem map_inl_mem_cone {s : Finset α} (hs : s ∈ K) :
    s.map (Embedding.inl : α ↪ α ⊕ PUnit) ∈ cone K :=
  map_inl_mem_cone_iff.mpr hs

/-- The cone apex is a face. -/
theorem apex_mem_cone : ({Sum.inr PUnit.unit} : Finset (α ⊕ PUnit)) ∈ cone K := by
  simpa [cone] using
    (map_inr_mem_join (K := K) (L := (⊤ : PreAbstractSimplicialComplex PUnit))
      (Finset.singleton_nonempty PUnit.unit))

/-- Adjoining the apex gives a face of the cone exactly when the base is empty or a face of the
base complex. -/
@[simp]
theorem disjSum_singleton_mem_cone_iff {s : Finset α} :
    s.disjSum {PUnit.unit} ∈ cone K ↔ s = ∅ ∨ s ∈ K := by
  rw [cone, disjSum_mem_join_iff]
  constructor
  · exact fun h => h.2.1
  · exact fun hs => ⟨Or.inr (Finset.singleton_nonempty PUnit.unit), hs,
      Or.inr (Finset.singleton_nonempty PUnit.unit)⟩

/-- Adjoining the apex to a face of the base produces a face of the cone. -/
theorem disjSum_singleton_mem_cone {s : Finset α} (hs : s ∈ K) :
    s.disjSum {PUnit.unit} ∈ cone K :=
  disjSum_singleton_mem_cone_iff.mpr (Or.inr hs)

/-- Coning is monotone in the base complex. -/
theorem cone_mono (h : K ≤ L) : cone K ≤ cone L :=
  join_mono h le_rfl

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {α : Type*}

/-- The cone on an abstract simplicial complex, defined as its join with the full complex on the
one-point type `PUnit`. -/
public def cone (K : AbstractSimplicialComplex α) :
    AbstractSimplicialComplex (α ⊕ PUnit) :=
  join K ⊤

variable {K L : AbstractSimplicialComplex α}

/-- Forgetting the singleton-face witness from an abstract cone recovers the cone of the
underlying pre-abstract simplicial complex. -/
@[simp]
theorem cone_toPreAbstractSimplicialComplex :
    (cone K).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.cone K.toPreAbstractSimplicialComplex := by
  rw [cone, join_toPreAbstractSimplicialComplex, PreAbstractSimplicialComplex.cone]
  congr 1

/-- A finite set is a face of the cone exactly when it is nonempty and its left projection is
either empty or a face of the base complex. -/
@[simp]
theorem mem_cone_iff {σ : Finset (α ⊕ PUnit)} :
    σ ∈ cone K ↔ σ.Nonempty ∧ (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) := by
  simp only [← mem_toPreAbstractSimplicialComplex, cone_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_cone_iff

/-- A finite set tagged into the left summand is a face of the cone exactly when it is a face of
the base complex. -/
@[simp]
theorem map_inl_mem_cone_iff {s : Finset α} :
    s.map (Embedding.inl : α ↪ α ⊕ PUnit) ∈ cone K ↔ s ∈ K := by
  simp only [← mem_toPreAbstractSimplicialComplex, cone_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.map_inl_mem_cone_iff

/-- Every face of the base complex, tagged into the left summand, is a face of its cone. -/
theorem map_inl_mem_cone {s : Finset α} (hs : s ∈ K) :
    s.map (Embedding.inl : α ↪ α ⊕ PUnit) ∈ cone K :=
  map_inl_mem_cone_iff.mpr hs

/-- The cone apex is a face. -/
theorem apex_mem_cone : ({Sum.inr PUnit.unit} : Finset (α ⊕ PUnit)) ∈ cone K := by
  exact (cone K).singleton_mem (Sum.inr PUnit.unit)

/-- Adjoining the apex gives a face of the cone exactly when the base is empty or a face of the
base complex. -/
@[simp]
theorem disjSum_singleton_mem_cone_iff {s : Finset α} :
    s.disjSum {PUnit.unit} ∈ cone K ↔ s = ∅ ∨ s ∈ K := by
  simp only [← mem_toPreAbstractSimplicialComplex, cone_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.disjSum_singleton_mem_cone_iff

/-- Adjoining the apex to a face of the base produces a face of the cone. -/
theorem disjSum_singleton_mem_cone {s : Finset α} (hs : s ∈ K) :
    s.disjSum {PUnit.unit} ∈ cone K :=
  disjSum_singleton_mem_cone_iff.mpr (Or.inr hs)

/-- Coning is monotone in the base complex. -/
theorem cone_mono (h : K ≤ L) : cone K ≤ cone L :=
  join_mono h le_rfl

end AbstractSimplicialComplex

end TauCeti
