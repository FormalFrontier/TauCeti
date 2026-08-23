/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Chain
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Order complexes

The order complex of a preordered type has the elements of the type as vertices and the
nonempty finite chains as faces. This is the general construction underlying barycentric
subdivision: applying it to the face poset of a simplicial complex gives its first barycentric
subdivision.

This file also records functoriality. A monotone map sends a chain to a chain, and hence induces a
simplicial map of order complexes. The barycentric-subdivision specialization in the next module
models the derived subdivision described by Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 2; the generic order-complex formulation and its functoriality are not taken
from that source.

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
* `TauCeti.AbstractSimplicialComplex.orderComplex_eq_top`: the order complex of a total preorder is
  the full simplicial complex.
* `TauCeti.AbstractSimplicialComplex.orderComplexMap_id` and
  `TauCeti.AbstractSimplicialComplex.orderComplexMap_comp`: functoriality laws.
-/

public section

open Finset Set

namespace TauCeti

namespace AbstractSimplicialComplex

variable {P Q R : Type*} [Preorder P] [Preorder Q] [Preorder R]

/-- The **order complex** of a preordered type `P`. Its vertices are the elements of `P`,
and a nonempty finite set of vertices is a face exactly when its elements are pairwise comparable.
-/
noncomputable def orderComplex (P : Type*) [Preorder P] : AbstractSimplicialComplex P where
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
  Iff.rfl

/-- A finite set is a face of the order complex exactly when it is nonempty and every two of its
elements are comparable. -/
theorem mem_orderComplex_iff' {σ : Finset P} :
    σ ∈ orderComplex P ↔
      σ.Nonempty ∧ ∀ p ∈ σ, ∀ q ∈ σ, p ≤ q ∨ q ≤ p := by
  rw [mem_orderComplex_iff]
  refine and_congr_right fun _ => ⟨fun h p hp q hq => ?_, fun h => ?_⟩
  · exact h.total (by exact_mod_cast hp) (by exact_mod_cast hq)
  · intro p hp q hq _
    exact h p (by exact_mod_cast hp) q (by exact_mod_cast hq)

/-- In a face of an order complex, every two vertices are comparable. -/
theorem le_or_le_of_mem_orderComplex {σ : Finset P} (hσ : σ ∈ orderComplex P)
    {p q : P} (hp : p ∈ σ) (hq : q ∈ σ) : p ≤ q ∨ q ≤ p :=
  (mem_orderComplex_iff.mp hσ).2.total (by exact_mod_cast hp) (by exact_mod_cast hq)

/-- Two elements span an edge of the order complex exactly when they are comparable. This also
covers the degenerate case `p = q`, when the pair is a singleton face.

This is not a `simp` lemma: `mem_orderComplex_iff` already rewrites the left-hand side. -/
theorem pair_mem_orderComplex_iff [DecidableEq P] (p q : P) :
    {p, q} ∈ orderComplex P ↔ p ≤ q ∨ q ≤ p := by
  constructor
  · intro h
    exact le_or_le_of_mem_orderComplex h (by simp) (by simp)
  · intro hpq
    rw [mem_orderComplex_iff]
    refine ⟨⟨p, by simp⟩, ?_⟩
    rcases hpq with hpq | hqp
    · simpa only [Finset.coe_pair] using IsChain.pair hpq
    · simpa only [Finset.pair_comm, Finset.coe_pair] using IsChain.pair hqp

/-- If the preorder on `P` is total, every nonempty finite set is a chain, so its order complex is
the full abstract simplicial complex. -/
@[simp]
theorem orderComplex_eq_top (P : Type*) [Preorder P]
    [Std.Total ((· ≤ ·) : P → P → Prop)] :
    orderComplex P = (⊤ : AbstractSimplicialComplex P) := by
  apply le_antisymm le_top
  intro σ hσ
  exact mem_orderComplex_iff.mpr
    ⟨mem_top_iff.mp hσ, fun p _ q _ _ => total_of (· ≤ ·) p q⟩

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
  apply DFunLike.coe_injective
  rw [coe_orderComplexMap, PreAbstractSimplicialComplex.SimplicialMap.coe_id]
  rfl

/-- The simplicial map of order complexes induced by a composite is the composite of the induced
simplicial maps. -/
@[simp]
theorem orderComplexMap_comp [DecidableEq Q] [DecidableEq R] (g : Q →o R) (f : P →o Q) :
    orderComplexMap (g.comp f) =
      (orderComplexMap g).comp (orderComplexMap f) := by
  apply DFunLike.coe_injective
  rw [coe_orderComplexMap, PreAbstractSimplicialComplex.SimplicialMap.coe_comp,
    coe_orderComplexMap, coe_orderComplexMap]
  rfl

end AbstractSimplicialComplex

end TauCeti
