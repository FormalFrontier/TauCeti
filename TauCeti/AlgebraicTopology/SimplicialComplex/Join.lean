/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Sum
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Joins of abstract simplicial complexes

The join of complexes `K` and `L` has the disjoint sum of their vertex types as vertices. Its
faces are the nonempty disjoint unions of a face of `K` and a face of `L`, allowing either side to
be empty. This file constructs the join first for `PreAbstractSimplicialComplex` and then for
`AbstractSimplicialComplex`.

Joins are standard infrastructure for the combinatorial-manifold part of the geometric-topology
roadmap (`TauCetiRoadmap/GeometricTopology/README.md`, layer 11). In particular, combinatorial
spheres are generated from the boundary of a simplex using subdivision and joins, links interact
with joins, and the simplicial cylinder appearing in collapse arguments is built from closely
related product constructions.

The construction follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter
2. The use of the sum type makes the two vertex sets disjoint by construction.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.join`: the join of two precomplexes.
* `TauCeti.AbstractSimplicialComplex.join`: the join of two abstract complexes.

## Main results

* `mem_join_iff`: membership is characterized by the two projected faces.
* `disjSum_mem_join_iff`: a disjoint union is a face exactly when each nonempty component is.
* `join_mono`: join is monotone in both arguments.
-/

public section

namespace TauCeti

open Finset Function Sum

namespace PreAbstractSimplicialComplex

variable {α β : Type*}

/-- The join of two pre-abstract simplicial complexes, on the disjoint sum of their vertex types.
A nonempty finite set is a face when each of its nonempty left and right projections is a face of
the corresponding complex. -/
public def join (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) :
    PreAbstractSimplicialComplex (α ⊕ β) where
  faces := {σ | σ.Nonempty ∧
    (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) ∧ (σ.toRight = ∅ ∨ σ.toRight ∈ L)}
  isRelLowerSet_faces := by
    rintro σ ⟨hσ, hK, hL⟩
    refine ⟨hσ, fun {τ} hτσ hτ => ⟨hτ, ?_, ?_⟩⟩
    · rcases hK with hK | hK
      · left
        exact subset_empty.mp ((toLeft_subset_toLeft hτσ).trans (subset_of_eq hK))
      · by_cases hτl : τ.toLeft = ∅
        · exact Or.inl hτl
        · exact Or.inr <| (K.isRelLowerSet_faces hK).2 (toLeft_subset_toLeft hτσ)
            (Finset.nonempty_iff_ne_empty.mpr hτl)
    · rcases hL with hL | hL
      · left
        exact subset_empty.mp ((toRight_subset_toRight hτσ).trans (subset_of_eq hL))
      · by_cases hτr : τ.toRight = ∅
        · exact Or.inl hτr
        · exact Or.inr <| (L.isRelLowerSet_faces hL).2 (toRight_subset_toRight hτσ)
            (Finset.nonempty_iff_ne_empty.mpr hτr)

variable {K K' : PreAbstractSimplicialComplex α} {L L' : PreAbstractSimplicialComplex β}

/-- Membership in a precomplex join is equivalent to nonemptiness together with the left and
right projection face conditions. -/
@[simp]
theorem mem_join_iff {σ : Finset (α ⊕ β)} :
    σ ∈ join K L ↔ σ.Nonempty ∧
      (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) ∧ (σ.toRight = ∅ ∨ σ.toRight ∈ L) :=
  Iff.rfl

/-- A disjoint union is a face of the join exactly when it is nonempty and each nonempty
component is a face of its original complex. -/
theorem disjSum_mem_join_iff {s : Finset α} {t : Finset β} :
    s.disjSum t ∈ join K L ↔
      (s.Nonempty ∨ t.Nonempty) ∧ (s = ∅ ∨ s ∈ K) ∧ (t = ∅ ∨ t ∈ L) := by
  simp only [mem_join_iff, toLeft_disjSum, toRight_disjSum]
  simp only [Finset.nonempty_iff_ne_empty, ne_eq, Finset.disjSum_eq_empty, not_and_or]

/-- A left face, tagged into the sum type, is a face of the join. -/
theorem map_inl_mem_join {s : Finset α} (hs : s ∈ K) :
    s.map (Embedding.inl : α ↪ α ⊕ β) ∈ join K L := by
  rw [← disjSum_empty, disjSum_mem_join_iff]
  exact ⟨Or.inl (K.isRelLowerSet_faces hs).1, Or.inr hs, Or.inl rfl⟩

/-- A right face, tagged into the sum type, is a face of the join. -/
theorem map_inr_mem_join {t : Finset β} (ht : t ∈ L) :
    t.map (Embedding.inr : β ↪ α ⊕ β) ∈ join K L := by
  rw [← empty_disjSum, disjSum_mem_join_iff]
  exact ⟨Or.inr (L.isRelLowerSet_faces ht).1, Or.inl rfl, Or.inr ht⟩

/-- The disjoint union of a left face and a right face is a face of the join. -/
theorem disjSum_mem_join {s : Finset α} {t : Finset β} (hs : s ∈ K) (ht : t ∈ L) :
    s.disjSum t ∈ join K L := by
  rw [disjSum_mem_join_iff]
  exact ⟨Or.inl (K.isRelLowerSet_faces hs).1, Or.inr hs, Or.inr ht⟩

/-- Join is monotone in both complexes. -/
theorem join_mono (hK : K ≤ K') (hL : L ≤ L') : join K L ≤ join K' L' := by
  rintro σ ⟨hσ, hs, ht⟩
  exact ⟨hσ, hs.imp_right (fun h => hK h), ht.imp_right (fun h => hL h)⟩

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {α β : Type*}

/-- The join of two abstract simplicial complexes, with vertices in the disjoint sum. -/
public def join (K : AbstractSimplicialComplex α) (L : AbstractSimplicialComplex β) :
    AbstractSimplicialComplex (α ⊕ β) :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex
    (α ⊕ β)
    (PreAbstractSimplicialComplex.join K.toPreAbstractSimplicialComplex
      L.toPreAbstractSimplicialComplex) fun v => by
      cases v with
      | inl a => exact PreAbstractSimplicialComplex.map_inl_mem_join (K.singleton_mem a)
      | inr b => exact PreAbstractSimplicialComplex.map_inr_mem_join (L.singleton_mem b)

variable {K K' : AbstractSimplicialComplex α} {L L' : AbstractSimplicialComplex β}

/-- Forgetting that the join contains every singleton recovers the underlying precomplex join. -/
@[simp]
theorem join_toPreAbstractSimplicialComplex :
    (join K L).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.join K.toPreAbstractSimplicialComplex
        L.toPreAbstractSimplicialComplex := by
  ext σ
  rfl

/-- Membership in an abstract join is equivalent to nonemptiness together with the left and
right projection face conditions. -/
@[simp]
theorem mem_join_iff {σ : Finset (α ⊕ β)} :
    σ ∈ join K L ↔ σ.Nonempty ∧
      (σ.toLeft = ∅ ∨ σ.toLeft ∈ K) ∧ (σ.toRight = ∅ ∨ σ.toRight ∈ L) := by
  simp only [← mem_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_join_iff

/-- A disjoint union is a face of the abstract join exactly when it is nonempty and each
nonempty component is a face of its original complex. -/
theorem disjSum_mem_join_iff {s : Finset α} {t : Finset β} :
    s.disjSum t ∈ join K L ↔
      (s.Nonempty ∨ t.Nonempty) ∧ (s = ∅ ∨ s ∈ K) ∧ (t = ∅ ∨ t ∈ L) := by
  simp only [← mem_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.disjSum_mem_join_iff

/-- A left face, tagged into the sum type, is a face of the join. -/
theorem map_inl_mem_join {s : Finset α} (hs : s ∈ K) :
    s.map (Embedding.inl : α ↪ α ⊕ β) ∈ join K L := by
  rw [← mem_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.map_inl_mem_join hs

/-- A right face, tagged into the sum type, is a face of the join. -/
theorem map_inr_mem_join {t : Finset β} (ht : t ∈ L) :
    t.map (Embedding.inr : β ↪ α ⊕ β) ∈ join K L := by
  rw [← mem_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.map_inr_mem_join ht

/-- The disjoint union of faces is a face of the join. -/
theorem disjSum_mem_join {s : Finset α} {t : Finset β} (hs : s ∈ K) (ht : t ∈ L) :
    s.disjSum t ∈ join K L := by
  rw [← mem_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.disjSum_mem_join hs ht

/-- Join is monotone in both abstract simplicial complexes. -/
theorem join_mono (hK : K ≤ K') (hL : L ≤ L') :
    join K L ≤ join K' L' := by
  rw [← AbstractSimplicialComplex.toPreAbstractSimplicialComplex_le_iff]
  rw [join_toPreAbstractSimplicialComplex, join_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.join_mono hK hL

end AbstractSimplicialComplex

end TauCeti
