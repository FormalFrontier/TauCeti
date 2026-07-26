/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.ElementaryCollapse
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Basic

/-!
# Simplicial collapse

This file passes from the local elementary-collapse move to finite simplicial collapses.  A
complex `K` collapses to `L` when there is a finite, possibly empty, sequence of elementary
collapses from `K` to `L`; it is collapsible when the endpoint can be a one-vertex complex.
These are the collapse notions used in layer 11 of the geometric-topology roadmap and in the
statement of Zeeman's conjecture.

As in `ElementaryCollapse`, the definitions use `PreAbstractSimplicialComplex`: collapsing a
free vertex changes the set of vertices actually used by a complex.  The definitions follow
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 3.

## Main definitions

* `PreAbstractSimplicialComplex.point`: the complex whose only face is a given vertex.
* `PreAbstractSimplicialComplex.CollapsesTo`: the reflexive transitive closure of elementary
  collapse.
* `PreAbstractSimplicialComplex.Collapsible`: collapse to a one-vertex complex.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- The one-vertex complex at `v`.  Its unique face is `{v}`. -/
def point (v : ι) : _root_.PreAbstractSimplicialComplex ι where
  faces := {{v}}
  isRelLowerSet_faces := by
    rintro σ rfl
    refine ⟨Finset.singleton_nonempty v, fun τ hτσ hτ => ?_⟩
    obtain ⟨w, hw⟩ := hτ
    have hwv : w = v := Finset.mem_singleton.mp (hτσ hw)
    subst w
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hw, fun w hw =>
      Finset.mem_singleton.mp (hτσ hw)⟩

@[simp]
theorem mem_point {v : ι} {σ : Finset ι} : σ ∈ point v ↔ σ = {v} := Iff.rfl

/-- A singleton is a face of `point v` exactly when it is the singleton at `v`. -/
theorem singleton_mem_point {v w : ι} : {w} ∈ point v ↔ w = v := by
  rw [mem_point, Finset.singleton_inj]

/-- The one-vertex complex at `v` is a subcomplex of `K` exactly when `{v}` is a face of `K`. -/
theorem point_le_iff {v : ι} {K : _root_.PreAbstractSimplicialComplex ι} :
    point v ≤ K ↔ ({v} : Finset ι) ∈ K :=
  Set.singleton_subset_iff

/-- The one-vertex complex at `v` is nonempty. -/
theorem point_ne_bot (v : ι) : point v ≠ ⊥ := by
  intro h
  have : ({v} : Finset ι) ∈ (⊥ : _root_.PreAbstractSimplicialComplex ι) :=
    h ▸ (mem_point.mpr rfl : ({v} : Finset ι) ∈ point v)
  exact this.elim

/-- Two one-vertex complexes are equal exactly when their vertices are equal. -/
@[simp]
theorem point_inj {v w : ι} : point v = point w ↔ v = w := by
  constructor
  · intro h
    have : ({v} : Finset ι) ∈ point w := h ▸ (mem_point.mpr rfl : ({v} : Finset ι) ∈ point v)
    exact singleton_mem_point.mp this
  · exact fun h => h ▸ rfl

/-- The abstract simplex spanned by a single vertex is the one-vertex complex at that vertex. -/
@[simp]
theorem simplex_singleton (v : ι) : simplex {v} = point v := by
  refine SetLike.ext fun σ => ?_
  rw [mem_simplex, mem_point, Finset.subset_singleton_iff]
  constructor
  · rintro ⟨hne, rfl | rfl⟩
    · exact absurd rfl hne.ne_empty
    · rfl
  · rintro rfl
    exact ⟨Finset.singleton_nonempty v, Or.inr rfl⟩

/-- `K` collapses to `L` when a finite, possibly empty, sequence of elementary collapses takes
`K` to `L`. -/
def CollapsesTo (K L : _root_.PreAbstractSimplicialComplex ι) : Prop :=
  Relation.ReflTransGen ElementaryCollapsesTo K L

namespace CollapsesTo

variable {K L P : _root_.PreAbstractSimplicialComplex ι}

/-- Every complex collapses to itself by the empty sequence. -/
@[refl]
theorem refl (K : _root_.PreAbstractSimplicialComplex ι) : CollapsesTo K K :=
  Relation.ReflTransGen.refl

/-- An elementary collapse is a collapse of length one. -/
theorem single (h : ElementaryCollapsesTo K L) : CollapsesTo K L :=
  Relation.ReflTransGen.single h

/-- Collapse is transitive by concatenating finite collapse sequences. -/
@[trans]
theorem trans (hKL : CollapsesTo K L) (hLP : CollapsesTo L P) : CollapsesTo K P :=
  Relation.ReflTransGen.trans hKL hLP

/-- Prepending an elementary collapse to a collapse sequence gives a collapse. -/
theorem head (hKL : ElementaryCollapsesTo K L) (hLP : CollapsesTo L P) : CollapsesTo K P :=
  Relation.ReflTransGen.head hKL hLP

/-- Appending an elementary collapse to a collapse sequence gives a collapse. -/
theorem tail (hKL : CollapsesTo K L) (hLP : ElementaryCollapsesTo L P) : CollapsesTo K P :=
  Relation.ReflTransGen.tail hKL hLP

/-- The endpoint of a collapse is a subcomplex of its starting complex. -/
theorem le (h : CollapsesTo K L) : L ≤ K := by
  induction h with
  | refl => exact le_rfl
  | tail hKL hLP ih => exact hLP.le.trans ih

/-- If `K` collapses to a complex `L` that contains `K`, then `K` and `L` are equal. -/
theorem eq_of_le (h : CollapsesTo K L) (hKL : K ≤ L) : K = L :=
  le_antisymm hKL h.le

/-- A collapse between comparable complexes is equality when the order points both ways. -/
theorem antisymm (hKL : CollapsesTo K L) (hLK : CollapsesTo L K) : K = L :=
  le_antisymm hLK.le hKL.le

/-- A nontrivial collapse sequence contains a first elementary collapse. -/
theorem eq_or_exists_head (h : CollapsesTo K L) :
    K = L ∨ ∃ P, ElementaryCollapsesTo K P ∧ CollapsesTo P L :=
  Relation.ReflTransGen.cases_head h

/-- A nontrivial collapse strictly decreases the complex. -/
theorem lt (h : CollapsesTo K L) (hne : K ≠ L) : L < K :=
  lt_of_le_of_ne h.le hne.symm

/-- A collapse preserves any property that is inherited by subcomplexes. -/
theorem property_of_antitone {p : _root_.PreAbstractSimplicialComplex ι → Prop}
    (hp : ∀ ⦃A B⦄, A ≤ B → p B → p A) (h : CollapsesTo K L) (hK : p K) : p L :=
  hp h.le hK

/-- A property preserved by each elementary collapse is preserved by a collapse sequence. -/
theorem property_of_elementaryCollapsesTo
    {p : _root_.PreAbstractSimplicialComplex ι → Prop}
    (hp : ∀ ⦃A B⦄, ElementaryCollapsesTo A B → p A → p B)
    (h : CollapsesTo K L) (hK : p K) : p L := by
  induction h with
  | refl => exact hK
  | tail hAB hBC ih => exact hp hBC ih

end CollapsesTo

/-- A simplicial complex is collapsible when it collapses to a one-vertex complex. -/
def Collapsible (K : _root_.PreAbstractSimplicialComplex ι) : Prop :=
  ∃ v : ι, CollapsesTo K (point v)

namespace Collapsible

variable {K L : _root_.PreAbstractSimplicialComplex ι}

/-- A one-vertex complex is collapsible, using the empty collapse sequence. -/
theorem point (v : ι) : Collapsible (point v) :=
  ⟨v, CollapsesTo.refl _⟩

/-- If `K` collapses to a collapsible complex, then `K` is collapsible. -/
theorem of_collapsesTo (hKL : CollapsesTo K L) (hL : Collapsible L) : Collapsible K := by
  obtain ⟨v, hLv⟩ := hL
  exact ⟨v, hKL.trans hLv⟩

/-- If `K` elementarily collapses to a collapsible complex, then `K` is collapsible. -/
theorem of_elementaryCollapsesTo (hKL : ElementaryCollapsesTo K L) (hL : Collapsible L) :
    Collapsible K :=
  of_collapsesTo (CollapsesTo.single hKL) hL

/-- A collapsible complex is nonempty. -/
theorem ne_bot (h : Collapsible K) : K ≠ ⊥ := by
  obtain ⟨v, hv⟩ := h
  intro hK
  have : ({v} : Finset ι) ∈ (⊥ : _root_.PreAbstractSimplicialComplex ι) :=
    point_le_iff.mp (hK ▸ hv.le)
  exact this.elim

/-- A collapsible complex contains its terminal vertex as a face. -/
theorem exists_vertex (h : Collapsible K) : ∃ v : ι, ({v} : Finset ι) ∈ K := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, point_le_iff.mp hv.le⟩

end Collapsible

end PreAbstractSimplicialComplex

end TauCeti
