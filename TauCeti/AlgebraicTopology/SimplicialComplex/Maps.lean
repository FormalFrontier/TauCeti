/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.SimplicialComplex.Basic

/-!
# Maps of abstract simplicial complexes

This file bundles simplicial maps between pre-abstract simplicial complexes. A simplicial map is
a map of ambient vertex types which sends every face to a face. The file supplies the identity,
composition, restriction to subcomplexes, and extension to a larger complex, together with the
connection to Mathlib's image complex `PreAbstractSimplicialComplex.map`.

These maps are basic infrastructure for subdivision and geometric realization in the geometric
topology roadmap. We work with `PreAbstractSimplicialComplex`, since constructions such as links
and elementary collapses naturally change the set of vertices represented by singleton faces.
-/

public section

namespace TauCeti

namespace PreAbstractSimplicialComplex

variable {α β γ δ : Type*} [DecidableEq β] [DecidableEq γ]
variable {K K' : PreAbstractSimplicialComplex α}
variable {L L' : PreAbstractSimplicialComplex β}
variable {P : PreAbstractSimplicialComplex γ}
variable {P' : PreAbstractSimplicialComplex δ}

/-- A simplicial map between pre-abstract simplicial complexes is a map of their ambient vertex
types which sends faces to faces. -/
@[ext]
structure SimplicialMap (K : PreAbstractSimplicialComplex α)
    (L : PreAbstractSimplicialComplex β) where
  /-- The map on the ambient vertex types. -/
  toFun : α → β
  /-- The image of every face is a face. -/
  map_face' : ∀ ⦃σ : Finset α⦄, σ ∈ K → σ.image toFun ∈ L

namespace SimplicialMap

instance : FunLike (SimplicialMap K L) α β where
  coe := toFun
  coe_injective f g h := by
    cases f
    cases g
    simp_all

@[simp]
theorem coe_mk (f : α → β) (hf) : ⇑(SimplicialMap.mk f hf : SimplicialMap K L) = f :=
  (rfl)

/-- A simplicial map sends a face to a face. -/
@[grind =>]
theorem map_face (f : SimplicialMap K L) {σ : Finset α} (hσ : σ ∈ K) :
    σ.image f ∈ L :=
  f.map_face' hσ

/-- A vertex map is simplicial exactly when its image complex is a subcomplex of the codomain. -/
theorem map_le_iff (f : α → β) :
    K.map f ≤ L ↔ ∀ ⦃σ : Finset α⦄, σ ∈ K → σ.image f ∈ L :=
  Set.image_subset_iff

/-- Construct a simplicial map from containment of the image complex in the codomain. -/
def ofMapLE (f : α → β) (h : K.map f ≤ L) : SimplicialMap K L where
  toFun := f
  map_face' := map_le_iff f |>.mp h

@[simp]
theorem coe_ofMapLE (f : α → β) (h : K.map f ≤ L) : ⇑(ofMapLE f h) = f :=
  (rfl)

/-- The image complex of a simplicial map is contained in its codomain. -/
theorem map_le (f : SimplicialMap K L) : K.map f ≤ L :=
  map_le_iff f |>.mpr fun _ hσ ↦ f.map_face hσ

/-- The identity simplicial map. -/
def id [DecidableEq α] (K : PreAbstractSimplicialComplex α) : SimplicialMap K K where
  toFun := _root_.id
  map_face' := by simp

@[simp]
theorem coe_id [DecidableEq α] : ⇑(id K) = _root_.id :=
  (rfl)

@[simp]
theorem id_apply [DecidableEq α] (x : α) : id K x = x :=
  (rfl)

/-- Composition of simplicial maps. -/
def comp (g : SimplicialMap L P) (f : SimplicialMap K L) : SimplicialMap K P where
  toFun := g ∘ f
  map_face' := by
    intro σ hσ
    rw [Finset.image_comp]
    exact g.map_face (f.map_face hσ)

@[simp]
theorem coe_comp (g : SimplicialMap L P) (f : SimplicialMap K L) :
    ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem comp_apply (g : SimplicialMap L P) (f : SimplicialMap K L) (x : α) :
    g.comp f x = g (f x) :=
  (rfl)

/-- Composing a simplicial map on the right with the identity leaves it unchanged. -/
@[simp]
theorem comp_id [DecidableEq α] (f : SimplicialMap K L) : f.comp (id K) = f := by
  apply DFunLike.coe_injective
  rw [coe_comp, coe_id, Function.comp_id]

/-- Composing a simplicial map on the left with the identity leaves it unchanged. -/
@[simp]
theorem id_comp (f : SimplicialMap K L) : (id L).comp f = f := by
  apply DFunLike.coe_injective
  rw [coe_comp, coe_id, Function.id_comp]

/-- Composition of simplicial maps is associative. -/
@[simp]
theorem comp_assoc [DecidableEq δ] (h : SimplicialMap P P') (g : SimplicialMap L P)
    (f : SimplicialMap K L) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply DFunLike.coe_injective
  simp only [coe_comp, Function.comp_def]

/-- Restrict the domain of a simplicial map to a subcomplex. -/
def domainRestrict (f : SimplicialMap K L) (h : K' ≤ K) : SimplicialMap K' L where
  toFun := f
  map_face' := fun _ hσ ↦ f.map_face (h hσ)

@[simp]
theorem coe_domainRestrict (f : SimplicialMap K L) (h : K' ≤ K) :
    ⇑(f.domainRestrict h) = f :=
  (rfl)

/-- Regard a simplicial map as landing in a larger complex. -/
def codomainExtend (f : SimplicialMap K L) (h : L ≤ L') : SimplicialMap K L' where
  toFun := f
  map_face' := fun _ hσ ↦ h (f.map_face hσ)

@[simp]
theorem coe_codomainExtend (f : SimplicialMap K L) (h : L ≤ L') :
    ⇑(f.codomainExtend h) = f :=
  (rfl)

/-- Every vertex map is simplicial into its image complex. -/
def toImage (K : PreAbstractSimplicialComplex α) (f : α → β) : SimplicialMap K (K.map f) :=
  ofMapLE f le_rfl

@[simp]
theorem coe_toImage (K : PreAbstractSimplicialComplex α) (f : α → β) : ⇑(toImage K f) = f :=
  (rfl)

/-- The inclusion of a subcomplex, acting as the identity on the ambient vertex type. -/
def inclusion [DecidableEq α] (h : K ≤ K') : SimplicialMap K K' :=
  (id K).codomainExtend h

@[simp]
theorem coe_inclusion [DecidableEq α] (h : K ≤ K') : ⇑(inclusion h) = _root_.id :=
  (rfl)

@[simp]
theorem inclusion_apply [DecidableEq α] (h : K ≤ K') (x : α) : inclusion h x = x :=
  (rfl)

end SimplicialMap

end PreAbstractSimplicialComplex

end TauCeti
