/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Linear
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Additivity and linearity of continuous cohomology

This file proves that the compatible-pair map on continuous cohomology is additive in its
coefficient morphism. Over a commutative coefficient ring it also commutes with scalar
multiplication. Consequently `Hⁿ(G, -)`, packaged as
`TauCeti.ContinuousCohomology.continuousCohomologyFunctor`, is an additive and linear functor.

The proof follows the construction through Mathlib's coinduced resolution: `resolutionMap`,
`cochainsMap`, `cocyclesMap`, and finally the induced map on homology. The cochain- and
cocycle-level statements are public because later constructions, in particular connecting maps
and cup products, need linearity before passing to cohomology.

## Main results

* `TauCeti.ContinuousCohomology.map_add` and `TauCeti.ContinuousCohomology.map_smul` give
  additivity and linearity of the map associated to a compatible pair.
* `TauCeti.ContinuousCohomology.mapAddHom` and
  `TauCeti.ContinuousCohomology.mapLinearMap` bundle that dependence as an additive homomorphism
  and a linear map.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctor_additive` and
  `TauCeti.ContinuousCohomology.continuousCohomologyFunctor_linear` install the corresponding
  functor instances.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology _root_.TopRep _root_.ContRepresentation

universe u v

variable {R : Type u} {G H : Type v} [Ring R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep R G} {Y : TopRep R H}

@[simp]
private theorem resolutionMap_zero_coeff (φ : H →ₜ* G) (i : ℕ) :
    resolutionMap φ (0 : TopRep.res φ X ⟶ Y) i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, ih]
    ext F x
    rfl

@[simp]
private theorem resolutionMap_add (φ : H →ₜ* G) (f g : TopRep.res φ X ⟶ Y) (i : ℕ) :
    resolutionMap φ (f + g) i = resolutionMap φ f i + resolutionMap φ g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- The compatible-pair cochain map induced by the zero coefficient morphism is zero. -/
@[simp]
theorem cochainsMap_zero (φ : H →ₜ* G) :
    cochainsMap φ (0 : TopRep.res φ X ⟶ Y) = 0 := by
  ext i v
  simp only [cochainsMap_f, resolutionMap_zero_coeff]
  rfl

/-- Compatible-pair cochain maps are additive in the coefficient morphism. -/
@[simp]
theorem cochainsMap_add (φ : H →ₜ* G) (f g : TopRep.res φ X ⟶ Y) :
    cochainsMap φ (f + g) = cochainsMap φ f + cochainsMap φ g := by
  ext i v
  simp only [cochainsMap_f, resolutionMap_add]
  rfl

/-- The map on continuous cocycles induced by the zero coefficient morphism is zero. -/
@[simp]
theorem cocyclesMap_zero (φ : H →ₜ* G) (n : ℕ) :
    cocyclesMap φ (0 : TopRep.res φ X ⟶ Y) n = 0 := by
  simp only [cocyclesMap, cochainsMap_zero]
  exact HomologicalComplex.cyclesMap_zero _ _ n

/-- Maps on continuous cocycles are additive in the coefficient morphism. -/
@[simp]
theorem cocyclesMap_add (φ : H →ₜ* G) (f g : TopRep.res φ X ⟶ Y) (n : ℕ) :
    cocyclesMap φ (f + g) n = cocyclesMap φ f n + cocyclesMap φ g n := by
  rw [← cancel_mono ((homogeneousCochains Y).iCycles n)]
  rw [HomologicalComplex.cyclesMap_i, Preadditive.add_comp,
    HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i, cochainsMap_add,
    HomologicalComplex.add_f_apply, Preadditive.comp_add]

/-- The map on continuous cohomology induced by the zero coefficient morphism is zero. -/
@[simp]
theorem map_zero (φ : H →ₜ* G) (n : ℕ) :
    map φ (0 : TopRep.res φ X ⟶ Y) n = 0 := by
  simp only [map, cochainsMap_zero]
  exact HomologicalComplex.homologyMap_zero _ _ n

/-- Maps on continuous cohomology are additive in the coefficient morphism. -/
@[simp]
theorem map_add (φ : H →ₜ* G) (f g : TopRep.res φ X ⟶ Y) (n : ℕ) :
    map φ (f + g) n = map φ f n + map φ g n := by
  simp only [map, cochainsMap_add]
  exact HomologicalComplex.homologyMap_add _ _ n

/-- The map on continuous cohomology induced by a fixed group homomorphism, bundled as an
additive homomorphism in the coefficient morphism. -/
noncomputable def mapAddHom (φ : H →ₜ* G) (X : TopRep R G) (Y : TopRep R H) (n : ℕ) :
    (TopRep.res φ X ⟶ Y) →+ (continuousCohomology n X ⟶ continuousCohomology n Y) where
  toFun f := map φ f n
  map_zero' := map_zero φ n
  map_add' f g := map_add φ f g n

@[simp]
theorem mapAddHom_apply (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    mapAddHom φ X Y n f = map φ f n :=
  (rfl)

section Linear

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {X : TopRep R G} {Y : TopRep R H}

@[simp]
private theorem resolutionMap_smul (φ : H →ₜ* G) (r : R) (f : TopRep.res φ X ⟶ Y)
    (i : ℕ) :
    resolutionMap φ (r • f) i = r • resolutionMap φ f i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [resolutionMap_succ, resolutionMap_succ, ih]
    ext F x
    rfl

/-- Compatible-pair cochain maps commute with scalar multiplication of the coefficient morphism. -/
@[simp]
theorem cochainsMap_smul (φ : H →ₜ* G) (r : R) (f : TopRep.res φ X ⟶ Y) :
    cochainsMap φ (r • f) = r • cochainsMap φ f := by
  ext i v
  simp only [cochainsMap_f, resolutionMap_smul]
  rfl

/-- Maps on continuous cocycles commute with scalar multiplication of the coefficient morphism. -/
@[simp]
theorem cocyclesMap_smul (φ : H →ₜ* G) (r : R) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    cocyclesMap φ (r • f) n = r • cocyclesMap φ f n := by
  rw [← cancel_mono ((homogeneousCochains Y).iCycles n)]
  rw [HomologicalComplex.cyclesMap_i, Linear.smul_comp, HomologicalComplex.cyclesMap_i,
    cochainsMap_smul, HomologicalComplex.smul_f_apply, Linear.comp_smul]

/-- Maps on continuous cohomology commute with scalar multiplication of the coefficient morphism. -/
@[simp]
theorem map_smul (φ : H →ₜ* G) (r : R) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    map φ (r • f) n = r • map φ f n := by
  rw [← cancel_epi (π X n), π_map, cocyclesMap_smul, Linear.smul_comp, Linear.comp_smul,
    π_map]

/-- The map on continuous cohomology induced by a fixed group homomorphism, bundled as a linear
map in the coefficient morphism. -/
noncomputable def mapLinearMap (φ : H →ₜ* G) (X : TopRep R G) (Y : TopRep R H) (n : ℕ) :
    (TopRep.res φ X ⟶ Y) →ₗ[R]
      (continuousCohomology n X ⟶ continuousCohomology n Y) where
  __ := mapAddHom φ X Y n
  map_smul' r f := map_smul φ r f n

@[simp]
theorem mapLinearMap_apply (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    mapLinearMap φ X Y n f = map φ f n :=
  (rfl)

end Linear

section Additive

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
private theorem res_id_eq (X : TopRep R G) :
    TopRep.res (ContinuousMonoidHom.id G : G →* G) X = X := by
  rfl

private def resIdHom (X : TopRep R G) :
    TopRep.res (ContinuousMonoidHom.id G : G →* G) X ⟶ X :=
  eqToHom (res_id_eq R G X)

private theorem coeffMap_eq_map_id {X Y : TopRep R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap f n = map (ContinuousMonoidHom.id G) (resIdHom R G X ≫ f) n := by
  rw [coeffMap_def]
  exact map_congr rfl (eqToHom_comp_heq f (res_id_eq R G X)).symm n

private theorem coeffMap_add {X Y : TopRep R G} (f g : X ⟶ Y) (n : ℕ) :
    coeffMap (f + g) n = coeffMap f n + coeffMap g n := by
  rw [coeffMap_eq_map_id, coeffMap_eq_map_id, coeffMap_eq_map_id,
    Preadditive.comp_add, map_add]

/-- Continuous cohomology in a fixed degree is additive in the coefficient representation. -/
noncomputable instance continuousCohomologyFunctor_additive (n : ℕ) :
    (continuousCohomologyFunctor R G n).Additive where
  map_add {_X _Y} {f g} := coeffMap_add R G f g n

end Additive

section Linear

variable (R : Type u) [CommRing R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem coeffMap_smul {X Y : TopRep R G} (r : R) (f : X ⟶ Y) (n : ℕ) :
    coeffMap (r • f) n = r • coeffMap f n := by
  rw [coeffMap_eq_map_id, coeffMap_eq_map_id, Linear.comp_smul, map_smul]

/-- Continuous cohomology in a fixed degree is linear in the coefficient representation. -/
noncomputable instance continuousCohomologyFunctor_linear (n : ℕ) :
    (continuousCohomologyFunctor R G n).Linear R where
  map_smul f r := coeffMap_smul R G r f n

end Linear

end TauCeti.ContinuousCohomology

end
