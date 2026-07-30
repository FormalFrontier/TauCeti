/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Join
public import TauCeti.AlgebraicTopology.SimplicialComplex.LinkStar
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic

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

The file also carries the predicate `IsCone K v`, which says that `K` is a cone with apex a
vertex `v` of its *own* vertex type, so that a complex can be recognised as a cone without
changing that type.  This internal form applies to complexes that merely happen to be cones —
abstract simplices and closed stars — while `isCone_cone` records that the `cone` construction
satisfies it at its apex, identifying the two accounts.

The construction follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter
2.  No result from that source is used beyond the standard definition of a cone as a join with a
point.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.cone`: the cone on a pre-abstract simplicial complex.
* `TauCeti.AbstractSimplicialComplex.cone`: the cone on an abstract simplicial complex.
* `TauCeti.PreAbstractSimplicialComplex.IsCone`: a complex is a cone with a given apex.

## Main results

* `mem_cone_iff`: a face of the cone is nonempty and has either an empty base projection or a
  face of the original complex as its base projection.
* `map_inl_mem_cone`: every original face is a face of the cone.
* `apex_mem_cone`: the apex is a face.
* `disjSum_singleton_mem_cone`: adjoining the apex to an original face gives a face.
* `cone_mono`: coning is monotone.
* `finite_faces_cone`: the cone on a finite complex is finite.
* `isCone_deletion`: deleting a face missing the apex leaves a cone with the same apex.
* `isCone_simplex`, `isCone_closedStar`, `isCone_cone`: the standard cones.
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
projection because the apex type has one element.

This is a low-priority `simp` lemma: it normalizes membership of an arbitrary finite set, while
the specialized characterizations below still fire first on their own shapes. -/
@[simp low]
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

/-- The cone on a finite complex is finite: a face of the cone is determined by its two
projections (`Finset.sumEquiv`), the left one is empty or a face of the base, and the apex type
is finite. -/
theorem finite_faces_cone (hfin : K.faces.Finite) : (cone K).faces.Finite := by
  refine Set.Finite.of_finite_image (f := Finset.sumEquiv)
    (Set.Finite.subset ((hfin.insert ∅).prod (Set.finite_univ (α := Finset PUnit))) ?_)
    Finset.sumEquiv.injective.injOn
  rintro _ ⟨σ, hσ, rfl⟩
  exact Set.mem_prod.mpr ⟨Set.mem_insert_iff.mpr (mem_cone_iff.mp hσ).2, Set.mem_univ _⟩

section IsCone

variable {ι : Type*} [DecidableEq ι] {v : ι} {σ : Finset ι}

/-- `K` is a **cone with apex `v`** when `v` is a vertex of `K` and adjoining `v` to a face of
`K` again gives a face of `K`.

This is the internal form of the cone condition: the apex is a vertex of the ambient type of
`K` itself, so a complex can be recognised as a cone without changing its vertex type.  The
`cone` construction above satisfies it at its apex (`isCone_cone`). -/
structure IsCone (K : PreAbstractSimplicialComplex ι) (v : ι) : Prop where
  /-- The apex is a vertex of the complex. -/
  apex_mem : ({v} : Finset ι) ∈ K
  /-- Adjoining the apex to a face gives a face. -/
  insert_mem : ∀ ⦃σ : Finset ι⦄, σ ∈ K → insert v σ ∈ K

/-- A cone with apex `v` is nonempty. -/
theorem IsCone.ne_bot {K : PreAbstractSimplicialComplex ι} (h : IsCone K v) : K ≠ ⊥ := fun hK =>
  (hK ▸ h.apex_mem : ({v} : Finset ι) ∈ (⊥ : PreAbstractSimplicialComplex ι)).elim

/-- Deleting a nonempty face that misses the apex leaves a cone with the same apex.  Note that
the deletion of a face *containing* the apex need not be a cone: deleting `{v}` itself destroys
the apex. -/
theorem isCone_deletion {K : PreAbstractSimplicialComplex ι} (h : IsCone K v) (hσ : σ.Nonempty)
    (hv : v ∉ σ) : IsCone (deletion K σ) v where
  apex_mem := by
    refine mem_deletion.mpr ⟨h.apex_mem, fun hsub => ?_⟩
    rcases Finset.subset_singleton_iff.mp hsub with rfl | rfl
    · exact hσ.ne_empty rfl
    · exact hv (Finset.mem_singleton_self v)
  insert_mem ω hω := by
    rw [mem_deletion] at hω ⊢
    exact ⟨h.insert_mem hω.1, fun hsub =>
      hω.2 ((Finset.subset_insert_iff_of_notMem hv).mp hsub)⟩

/-- An abstract simplex is a cone with apex any of its vertices. -/
theorem isCone_simplex {V : Finset ι} (hv : v ∈ V) : IsCone (simplex V) v where
  apex_mem := mem_simplex.mpr ⟨Finset.singleton_nonempty v, Finset.singleton_subset_iff.mpr hv⟩
  insert_mem σ hσ :=
    mem_simplex.mpr ⟨Finset.insert_nonempty v σ, Finset.insert_subset hv (mem_simplex.mp hσ).2⟩

/-- The closed star of a face is a cone with apex any vertex of that face: adjoining `v ∈ σ` to
a face `ρ` of the closed star leaves the defining union `ρ ∪ σ` unchanged. -/
theorem isCone_closedStar {K : PreAbstractSimplicialComplex ι} (hσ : σ ∈ K) (hv : v ∈ σ) :
    IsCone (closedStar K σ) v where
  apex_mem :=
    mem_closedStar.mpr ⟨Finset.singleton_nonempty v, by
      rwa [Finset.singleton_union, Finset.insert_eq_self.mpr hv]⟩
  insert_mem ρ hρ :=
    mem_closedStar.mpr ⟨Finset.insert_nonempty v ρ, by
      rw [Finset.insert_union, Finset.insert_eq_self.mpr (Finset.mem_union_right _ hv)]
      exact (mem_closedStar.mp hρ).2⟩

/-- The cone construction produces a cone in the internal sense, with apex the adjoined
vertex.  This is what identifies the two accounts of a cone. -/
theorem isCone_cone [DecidableEq α] (K : PreAbstractSimplicialComplex α) :
    IsCone (cone K) (Sum.inr PUnit.unit) where
  apex_mem := apex_mem_cone
  insert_mem σ hσ := by
    rw [mem_cone_iff] at hσ ⊢
    exact ⟨Finset.insert_nonempty _ _, by rw [Finset.toLeft_insert_inr]; exact hσ.2⟩

end IsCone

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
either empty or a face of the base complex.

This is a low-priority `simp` lemma: it normalizes membership of an arbitrary finite set, while
the specialized characterizations below still fire first on their own shapes. -/
@[simp low]
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
