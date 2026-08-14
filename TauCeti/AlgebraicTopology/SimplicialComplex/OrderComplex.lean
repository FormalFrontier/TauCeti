/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Preorder.Chain
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Order complexes

The order complex of a partially ordered type has the elements of the type as vertices and the
nonempty finite chains as faces. This is the general construction underlying barycentric
subdivision: applying it to the face poset of a simplicial complex gives its first barycentric
subdivision.

This file also records functoriality. A monotone map sends a chain to a chain, and hence induces a
simplicial map of order complexes. The construction and its functoriality follow the description
of derived subdivisions in Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*,
Chapter 2.

## Main definitions

* `TauCeti.AbstractSimplicialComplex.orderComplex`: the simplicial complex of nonempty finite
  chains.
* `TauCeti.AbstractSimplicialComplex.orderComplexMap`: the simplicial map induced by a monotone
  map.

## Main results

* `TauCeti.AbstractSimplicialComplex.mem_orderComplex_iff`: faces are exactly the nonempty finite
  chains.
* `TauCeti.AbstractSimplicialComplex.pair_mem_orderComplex_iff`: two vertices span an edge exactly
  when they are comparable.
* `TauCeti.AbstractSimplicialComplex.orderComplex_eq_top`: the order complex of a linear order is
  the full simplicial complex.
* `TauCeti.AbstractSimplicialComplex.orderComplexMap_id` and
  `TauCeti.AbstractSimplicialComplex.orderComplexMap_comp`: functoriality laws.
-/

public section

open Finset Set

namespace TauCeti

namespace AbstractSimplicialComplex

variable {P Q R : Type*} [PartialOrder P] [PartialOrder Q] [PartialOrder R]

/-- The **order complex** of a partially ordered type `P`. Its vertices are the elements of `P`,
and a nonempty finite set of vertices is a face exactly when its elements are pairwise comparable.
-/
noncomputable def orderComplex (P : Type*) [PartialOrder P] : AbstractSimplicialComplex P where
  faces := {σ | σ.Nonempty ∧ IsChain (· ≤ ·) (↑σ : Set P)}
  isRelLowerSet_faces := fun {_} hσ =>
    ⟨hσ.1, fun _ hsub hne =>
      ⟨hne, hσ.2.mono (by exact_mod_cast hsub)⟩⟩
  singleton_mem p := by
    classical
    exact ⟨singleton_nonempty p, by simp⟩

/-- A finite set is a face of the order complex exactly when it is nonempty and is a chain. -/
@[simp]
theorem mem_orderComplex_iff {σ : Finset P} :
    σ ∈ orderComplex P ↔ σ.Nonempty ∧ IsChain (· ≤ ·) (↑σ : Set P) :=
  by
    -- `SetLike` membership hides the defining predicate behind the structure's `faces` projection.
    change σ ∈ (orderComplex P).faces ↔ _
    rw [orderComplex]
    rfl

/-- Two elements span an edge of the order complex exactly when they are comparable. This also
covers the degenerate case `p = q`, when the pair is a singleton face. -/
@[simp]
theorem pair_mem_orderComplex_iff [DecidableEq P] (p q : P) :
    {p, q} ∈ orderComplex P ↔ p ≤ q ∨ q ≤ p := by
  rw [mem_orderComplex_iff]
  constructor
  · intro h
    by_cases hpq : p = q
    · exact Or.inl hpq.le
    · exact h.2 (by simp) (by simp) hpq
  · intro hpq
    refine ⟨⟨p, by simp⟩, ?_⟩
    rcases hpq with hpq | hqp
    · simpa only [Finset.coe_insert, Finset.coe_singleton] using IsChain.pair hpq
    · simpa only [Finset.pair_comm, Finset.coe_insert, Finset.coe_singleton] using
        IsChain.pair hqp

/-- In a face of an order complex, every two vertices are comparable. -/
theorem comparable_of_mem_orderComplex {σ : Finset P} (hσ : σ ∈ orderComplex P)
    {p q : P} (hp : p ∈ σ) (hq : q ∈ σ) : p ≤ q ∨ q ≤ p := by
  by_cases hpq : p = q
  · exact Or.inl hpq.le
  · exact (mem_orderComplex_iff.mp hσ).2 (by exact_mod_cast hp) (by exact_mod_cast hq) hpq

/-- If the order on `P` is linear, every nonempty finite set is a chain, so its order complex is
the full abstract simplicial complex. -/
@[simp]
theorem orderComplex_eq_top (P : Type*) [LinearOrder P] :
    orderComplex P = (⊤ : AbstractSimplicialComplex P) := by
  apply le_antisymm le_top
  intro σ hσ
  -- Expose the two `faces` projections before unfolding the order complex and the lattice top.
  change σ ∈ (orderComplex P).faces
  rw [orderComplex]
  change σ.Nonempty at hσ
  exact ⟨hσ, isChain_of_trichotomous _⟩

/-- A monotone map induces a simplicial map between order complexes. -/
def orderComplexMap [DecidableEq Q] (f : P →o Q) :
    PreAbstractSimplicialComplex.SimplicialMap
      (orderComplex P).toPreAbstractSimplicialComplex
      (orderComplex Q).toPreAbstractSimplicialComplex where
  toFun := f
  map_face' := by
    intro σ hσ
    rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      mem_orderComplex_iff]
    rw [_root_.AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
      mem_orderComplex_iff] at hσ
    refine ⟨image_nonempty.mpr hσ.1, ?_⟩
    simpa only [coe_image] using f.monotone.isChain_image hσ.2

@[simp]
theorem coe_orderComplexMap [DecidableEq Q] (f : P →o Q) :
    ⇑(orderComplexMap f) = f :=
  (rfl)

@[simp]
theorem orderComplexMap_apply [DecidableEq Q] (f : P →o Q) (p : P) :
    orderComplexMap f p = f p :=
  (rfl)

/-- The simplicial map of order complexes induced by the identity is the identity simplicial map.
-/
@[simp]
theorem orderComplexMap_id [DecidableEq P] :
  orderComplexMap OrderHom.id =
      PreAbstractSimplicialComplex.SimplicialMap.id
        (orderComplex P).toPreAbstractSimplicialComplex := by
  ext p
  -- `SimplicialMap.ext` leaves `toFun` projections; recover applications to use the public API.
  change orderComplexMap OrderHom.id p =
    PreAbstractSimplicialComplex.SimplicialMap.id
      (orderComplex P).toPreAbstractSimplicialComplex p
  rw [orderComplexMap_apply, PreAbstractSimplicialComplex.SimplicialMap.id_apply]
  rfl

/-- The simplicial map of order complexes induced by a composite is the composite of the induced
simplicial maps. -/
@[simp]
theorem orderComplexMap_comp [DecidableEq Q] [DecidableEq R] (g : Q →o R) (f : P →o Q) :
    orderComplexMap (g.comp f) =
      (orderComplexMap g).comp (orderComplexMap f) := by
  ext p
  -- `SimplicialMap.ext` leaves `toFun` projections; recover applications to use the public API.
  change orderComplexMap (g.comp f) p = (orderComplexMap g).comp (orderComplexMap f) p
  rw [orderComplexMap_apply, PreAbstractSimplicialComplex.SimplicialMap.comp_apply,
    orderComplexMap_apply, orderComplexMap_apply]
  rfl

end AbstractSimplicialComplex

end TauCeti
