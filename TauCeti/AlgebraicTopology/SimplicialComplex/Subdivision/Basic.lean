/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex

/-!
# Barycentric subdivision of abstract simplicial complexes

The vertices of the first barycentric subdivision of a simplicial complex `K` are its faces, which
are always nonempty: `PreAbstractSimplicialComplex` requires its face collection to be a lower set
relative to `Finset.Nonempty`, so the empty face never occurs. A collection of these new vertices
spans a face exactly when the corresponding faces of `K` form a chain under inclusion.
Equivalently, the barycentric subdivision is the order complex of the face poset.

The construction is made for `PreAbstractSimplicialComplex`, since links, deletions, and collapse
subcomplexes need not contain every ambient singleton. Its result is an
`AbstractSimplicialComplex`: every face of the original complex is genuinely a vertex of the
subdivision. Simplicial maps act on face posets by taking vertexwise images, yielding the
functorial map `barycentricSubdivisionMap`.

This supplies the subdivision primitive required by Layer 11 of the GeometricTopology roadmap
before combinatorial spheres and balls can be defined up to subdivision. The definition follows
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2, "Derived
Subdivisions". Identifying the realizations of a complex and its subdivision is separate geometric
realization work. The functoriality here is only at the level of abstract complexes: the canonical
identification of a subdivision's realization with the original realization is not natural in
arbitrary simplicial maps.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision`: the order complex of the face
  poset.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom`: the monotone map on face
  posets induced by a simplicial map.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap`: the induced
  simplicial map between barycentric subdivisions.

## Main results

* `TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff`: the characteristic face
  criterion.
* `TauCeti.PreAbstractSimplicialComplex.pair_mem_barycentricSubdivision_iff`: two original faces
  span an edge exactly when one contains the other.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap_id` and
  `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricSubdivisionMap_comp`:
  functoriality laws.
-/

public section

open Finset Set

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {α β γ : Type*}

/-- The first **barycentric subdivision** of `K`: its vertices are the faces of `K`, and its faces
are the nonempty finite chains of faces under inclusion. -/
@[expose] noncomputable def barycentricSubdivision (K : PreAbstractSimplicialComplex α) :
    AbstractSimplicialComplex (SetLike.Face K) :=
  AbstractSimplicialComplex.orderComplex (SetLike.Face K)

/-- Barycentric subdivision is the order complex of the face poset. -/
theorem barycentricSubdivision_eq_orderComplex (K : PreAbstractSimplicialComplex α) :
    barycentricSubdivision K =
      AbstractSimplicialComplex.orderComplex (SetLike.Face K) :=
  rfl

variable {K : PreAbstractSimplicialComplex α}

/-- A collection of faces of `K` is a face of its barycentric subdivision exactly when it is
nonempty and totally ordered by inclusion. -/
@[simp]
theorem mem_barycentricSubdivision_iff {τ : Finset (SetLike.Face K)} :
    τ ∈ barycentricSubdivision K ↔
      τ.Nonempty ∧
        IsChain (· ≤ ·) (↑τ : Set (SetLike.Face K)) := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.mem_orderComplex_iff]

/-- A collection is a face of the barycentric subdivision exactly when it is nonempty and every
two original faces in the collection are nested. -/
theorem mem_barycentricSubdivision_iff' {ρ : Finset (SetLike.Face K)} :
    ρ ∈ barycentricSubdivision K ↔
      ρ.Nonempty ∧ ∀ σ ∈ ρ, ∀ τ ∈ ρ,
        (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.mem_orderComplex_iff']
  simp only [SetLike.face_le_iff]

/-- Two faces of `K` span an edge in its barycentric subdivision exactly when one is contained in
the other.

This is not a `simp` lemma: `mem_barycentricSubdivision_iff` already rewrites the left-hand
side. -/
theorem pair_mem_barycentricSubdivision_iff [DecidableEq α] (σ τ : SetLike.Face K) :
    {σ, τ} ∈ barycentricSubdivision K ↔
      (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex,
    AbstractSimplicialComplex.pair_mem_orderComplex_iff]
  simp only [SetLike.face_le_iff]

/-- Every two original faces occurring in one face of the barycentric subdivision are nested. -/
theorem subset_or_subset_of_mem_barycentricSubdivision
    {ρ : Finset (SetLike.Face K)}
    (hρ : ρ ∈ barycentricSubdivision K)
    {σ τ : SetLike.Face K}
    (hσ : σ ∈ ρ) (hτ : τ ∈ ρ) :
    (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ := by
  rw [barycentricSubdivision_eq_orderComplex] at hρ
  simpa only [SetLike.face_le_iff] using
    AbstractSimplicialComplex.le_or_le_of_mem_orderComplex hρ hσ hτ

namespace SimplicialMap

variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}
  {M : PreAbstractSimplicialComplex γ}

/-- A simplicial map induces a simplicial map between barycentric subdivisions by mapping every
face-vertex to its vertexwise image. -/
def barycentricSubdivisionMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    _root_.PreAbstractSimplicialComplex.SimplicialMap
      (barycentricSubdivision K).toPreAbstractSimplicialComplex
      (barycentricSubdivision L).toPreAbstractSimplicialComplex :=
  AbstractSimplicialComplex.orderComplexMap (faceOrderHom f)

/-- The subdivision map is the order-complex map induced by the map on face posets. -/
theorem barycentricSubdivisionMap_eq_orderComplexMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    barycentricSubdivisionMap f = AbstractSimplicialComplex.orderComplexMap (faceOrderHom f) :=
  (rfl)

theorem coe_barycentricSubdivisionMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    ⇑(barycentricSubdivisionMap f) = faceOrderHom f := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap]
  exact AbstractSimplicialComplex.coe_orderComplexMap (faceOrderHom f)

@[simp]
theorem coe_barycentricSubdivisionMap_apply [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L)
    (σ : SetLike.Face K) :
    (barycentricSubdivisionMap f σ : Finset β) = σ.1.image f := by
  rw [← coe_faceOrderHom_apply, ← coe_barycentricSubdivisionMap]

/-- Barycentric subdivision sends the identity simplicial map to the identity simplicial map. -/
@[simp]
theorem barycentricSubdivisionMap_id [DecidableEq α] :
    barycentricSubdivisionMap (_root_.PreAbstractSimplicialComplex.SimplicialMap.id K) =
      _root_.PreAbstractSimplicialComplex.SimplicialMap.id
        (barycentricSubdivision K).toPreAbstractSimplicialComplex := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap, faceOrderHom_id,
    AbstractSimplicialComplex.orderComplexMap_id]
  rfl

/-- Barycentric subdivision sends a composite of simplicial maps to the composite of their
induced maps. -/
@[simp]
theorem barycentricSubdivisionMap_comp [DecidableEq β] [DecidableEq γ]
    (g : _root_.PreAbstractSimplicialComplex.SimplicialMap L M)
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    barycentricSubdivisionMap (g.comp f) =
      (barycentricSubdivisionMap g).comp (barycentricSubdivisionMap f) := by
  rw [barycentricSubdivisionMap_eq_orderComplexMap, faceOrderHom_comp,
    AbstractSimplicialComplex.orderComplexMap_comp,
    barycentricSubdivisionMap_eq_orderComplexMap, barycentricSubdivisionMap_eq_orderComplexMap]
  rfl

end SimplicialMap

end PreAbstractSimplicialComplex

end TauCeti
