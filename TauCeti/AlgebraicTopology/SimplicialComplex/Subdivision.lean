/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.OrderComplex

/-!
# Barycentric subdivision of abstract simplicial complexes

The vertices of the first barycentric subdivision of a simplicial complex `K` are the nonempty
faces of `K`. A collection of these new vertices spans a face exactly when the corresponding faces
of `K` form a chain under inclusion. Equivalently, the barycentric subdivision is the order
complex of the face poset.

The construction is made for `PreAbstractSimplicialComplex`, since links, deletions, and collapse
subcomplexes need not contain every ambient singleton. Its result is an
`AbstractSimplicialComplex`: every face of the original complex is genuinely a vertex of the
subdivision. Simplicial maps act on face posets by taking vertexwise images, yielding the
functorial map `barycentricMap`.

This supplies the subdivision primitive required by Layer 11 of the GeometricTopology roadmap
before combinatorial spheres and balls can be defined up to subdivision. The definition follows
Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2, "Derived
Subdivisions". Identifying the realizations of a complex and its subdivision is separate geometric
realization work.

## Main definitions

* `TauCeti.PreAbstractSimplicialComplex.BarycentricVertex`: a nonempty face of the original
  complex, regarded as a vertex of its subdivision.
* `TauCeti.PreAbstractSimplicialComplex.barycentricSubdivision`: the order complex of the face
  poset.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.faceOrderHom`: the monotone map on face
  posets induced by a simplicial map.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricMap`: the induced simplicial map
  between barycentric subdivisions.

## Main results

* `TauCeti.PreAbstractSimplicialComplex.mem_barycentricSubdivision_iff`: the characteristic face
  criterion.
* `TauCeti.PreAbstractSimplicialComplex.pair_mem_barycentricSubdivision_iff`: two original faces
  span an edge exactly when one contains the other.
* `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricMap_id` and
  `TauCeti.PreAbstractSimplicialComplex.SimplicialMap.barycentricMap_comp`: functoriality laws.
-/

public section

open Finset Set

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {α β γ : Type*}

/-- A vertex of the barycentric subdivision of `K` is a face of `K`. Faces of a pre-abstract
simplicial complex are nonempty by definition. -/
abbrev BarycentricVertex (K : PreAbstractSimplicialComplex α) := {σ : Finset α // σ ∈ K}

/-- The first **barycentric subdivision** of `K`: its vertices are the faces of `K`, and its faces
are the nonempty finite chains of faces under inclusion. -/
noncomputable def barycentricSubdivision (K : PreAbstractSimplicialComplex α) :
    AbstractSimplicialComplex (BarycentricVertex K) :=
  AbstractSimplicialComplex.orderComplex (BarycentricVertex K)

variable {K : PreAbstractSimplicialComplex α}

/-- A collection of faces of `K` is a face of its barycentric subdivision exactly when it is
nonempty and totally ordered by inclusion. -/
@[simp]
theorem mem_barycentricSubdivision_iff {τ : Finset (BarycentricVertex K)} :
    τ ∈ barycentricSubdivision K ↔
      τ.Nonempty ∧ IsChain (· ≤ ·) (↑τ : Set (BarycentricVertex K)) :=
  AbstractSimplicialComplex.mem_orderComplex_iff

/-- Two faces of `K` span an edge in its barycentric subdivision exactly when one is contained in
the other.

This is not a `simp` lemma: `mem_barycentricSubdivision_iff` already rewrites the left-hand
side. -/
theorem pair_mem_barycentricSubdivision_iff [DecidableEq α] (σ τ : BarycentricVertex K) :
    {σ, τ} ∈ barycentricSubdivision K ↔ (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ :=
  AbstractSimplicialComplex.pair_mem_orderComplex_iff σ τ

/-- Every two original faces occurring in one face of the barycentric subdivision are nested. -/
theorem comparable_of_mem_barycentricSubdivision {ρ : Finset (BarycentricVertex K)}
    (hρ : ρ ∈ barycentricSubdivision K) {σ τ : BarycentricVertex K}
    (hσ : σ ∈ ρ) (hτ : τ ∈ ρ) : (σ : Finset α) ⊆ τ ∨ (τ : Finset α) ⊆ σ :=
  AbstractSimplicialComplex.comparable_of_mem_orderComplex hρ hσ hτ

namespace SimplicialMap

variable {K : PreAbstractSimplicialComplex α} {L : PreAbstractSimplicialComplex β}
  {M : PreAbstractSimplicialComplex γ}

/-- A simplicial map induces a monotone map between face posets by taking the image of every face.
-/
def faceOrderHom [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    BarycentricVertex K →o BarycentricVertex L where
  toFun σ := ⟨σ.1.image f, f.map_face σ.2⟩
  monotone' _ _ h := Finset.image_mono f h

-- Not a `simp` lemma: its right-hand side is a lambda building a subtype, so
-- `faceOrderHom_apply_coe` is the pointwise `simp`-normal form.
theorem coe_faceOrderHom [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    ⇑(faceOrderHom f) = fun σ => ⟨σ.1.image f, f.map_face σ.2⟩ :=
  (rfl)

@[simp]
theorem faceOrderHom_apply_coe [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L)
    (σ : BarycentricVertex K) :
    (faceOrderHom f σ : Finset β) = σ.1.image f :=
  (rfl)

/-- A simplicial map induces a simplicial map between barycentric subdivisions by mapping every
face-vertex to its vertexwise image. -/
def barycentricMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    _root_.PreAbstractSimplicialComplex.SimplicialMap
      (barycentricSubdivision K).toPreAbstractSimplicialComplex
      (barycentricSubdivision L).toPreAbstractSimplicialComplex :=
  AbstractSimplicialComplex.orderComplexMap (faceOrderHom f)

-- Not a `simp` lemma: it would reduce `barycentricMap_apply_coe`, the pointwise
-- `simp`-normal form, to a duplicate.
theorem coe_barycentricMap [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    ⇑(barycentricMap f) = faceOrderHom f :=
  by
    rw [barycentricMap]
    exact AbstractSimplicialComplex.coe_orderComplexMap (faceOrderHom f)

@[simp]
theorem barycentricMap_apply_coe [DecidableEq β]
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L)
    (σ : BarycentricVertex K) :
    (barycentricMap f σ : Finset β) = σ.1.image f :=
  by
    rw [← faceOrderHom_apply_coe, ← coe_barycentricMap]

/-- Mapping face posets along a composite agrees pointwise with composing the face-poset maps. -/
theorem faceOrderHom_comp_apply [DecidableEq β] [DecidableEq γ]
    (g : _root_.PreAbstractSimplicialComplex.SimplicialMap L M)
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L)
    (σ : BarycentricVertex K) :
    faceOrderHom (g.comp f) σ = faceOrderHom g (faceOrderHom f σ) := by
  apply Subtype.ext
  rw [faceOrderHom_apply_coe, faceOrderHom_apply_coe, faceOrderHom_apply_coe]
  rw [← Finset.image_comp]
  exact congrArg (fun h : α → γ => σ.1.image h)
    (_root_.PreAbstractSimplicialComplex.SimplicialMap.coe_comp g f)

/-- Barycentric subdivision sends the identity simplicial map to the identity simplicial map. -/
@[simp]
theorem barycentricMap_id [DecidableEq α] :
    barycentricMap (_root_.PreAbstractSimplicialComplex.SimplicialMap.id K) =
      _root_.PreAbstractSimplicialComplex.SimplicialMap.id
        (barycentricSubdivision K).toPreAbstractSimplicialComplex := by
  apply DFunLike.coe_injective
  funext σ
  apply Subtype.ext
  rw [barycentricMap_apply_coe]
  simp

/-- Barycentric subdivision sends a composite of simplicial maps to the composite of their
induced maps. -/
@[simp]
theorem barycentricMap_comp [DecidableEq β] [DecidableEq γ]
    (g : _root_.PreAbstractSimplicialComplex.SimplicialMap L M)
    (f : _root_.PreAbstractSimplicialComplex.SimplicialMap K L) :
    barycentricMap (g.comp f) = (barycentricMap g).comp (barycentricMap f) := by
  apply DFunLike.coe_injective
  funext σ
  rw [coe_barycentricMap,
    _root_.PreAbstractSimplicialComplex.SimplicialMap.coe_comp,
    coe_barycentricMap, coe_barycentricMap]
  exact faceOrderHom_comp_apply g f σ

end SimplicialMap

end PreAbstractSimplicialComplex

end TauCeti
