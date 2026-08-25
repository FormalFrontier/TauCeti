/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme

/-!
# Relabelling the coordinates of a split torus

A permutation `τ` of the index set of the rank-`sigma` split torus permutes its coordinates, hence
acts on its character lattice `sigma →₀ ℤ`, on its coordinate Hopf algebra, and on the group scheme
itself. This file records that action at all three levels, together with its two structural
identities: it is multiplicative in `τ` and trivial at the identity permutation.

The character-lattice map sends a character `χ` to `χ ∘ τ⁻¹`, so that the induced automorphism of
the group scheme permutes coordinates by `τ` on points. A consumer that has to check a finite-order
relation for a relabelling — the graph automorphism of a Chevalley group is the case this file was
written for — gets it from the two identities below and the order of `τ` in `Equiv.Perm sigma`,
with no further computation.

## Main declarations

* `TauCeti.SplitTorus.characterRelabel`: the induced automorphism of the character lattice.
* `TauCeti.SplitTorus.relabelHom`: the same map, read in `FGCommGrpCat`.
* `TauCeti.SplitTorus.relabelCoordinateMap`: the induced automorphism of the coordinate
  Hopf algebra.
* `TauCeti.SplitTorus.relabel`: the induced automorphism of the split-torus group scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12.
-/

public section

open CategoryTheory

namespace TauCeti.SplitTorus

universe u

variable {sigma : Type u}

/-- **Relabelling the characters of the rank-`sigma` split torus along a permutation of `sigma`.**
It sends the character `χ` to `χ ∘ τ⁻¹`. -/
noncomputable def characterRelabel (τ : Equiv.Perm sigma) :
    Multiplicative (sigma →₀ ℤ) →* Multiplicative (sigma →₀ ℤ) :=
  AddMonoidHom.toMultiplicative (Finsupp.domCongr τ).toAddMonoidHom

/-- Relabelling a character reindexes its coordinate function. -/
theorem characterRelabel_apply (τ : Equiv.Perm sigma) (x : Multiplicative (sigma →₀ ℤ)) :
    characterRelabel τ x =
      Multiplicative.ofAdd (Finsupp.equivMapDomain τ (Multiplicative.toAdd x)) := (rfl)

/-- Relabelling an additively written character. -/
theorem characterRelabel_ofAdd (τ : Equiv.Perm sigma) (f : sigma →₀ ℤ) :
    characterRelabel τ (Multiplicative.ofAdd f) =
      Multiplicative.ofAdd (Finsupp.equivMapDomain τ f) := (rfl)

/-- Relabelling is multiplicative in the permutation. -/
theorem characterRelabel_comp (τ ν : Equiv.Perm sigma) :
    (characterRelabel τ).comp (characterRelabel ν) = characterRelabel (τ * ν) := by
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, characterRelabel_apply, Equiv.Perm.mul_def,
    Finsupp.equivMapDomain_trans]
  rfl

/-- Relabelling by the identity permutation is the identity. -/
theorem characterRelabel_one : characterRelabel (sigma := sigma) 1 = MonoidHom.id _ := by
  refine MonoidHom.ext fun x => ?_
  simp only [characterRelabel_apply, MonoidHom.id_apply, Equiv.Perm.one_def,
    Finsupp.equivMapDomain_refl]
  rfl

variable [Finite sigma]

/-- The relabelling of the character group, read as a morphism of finitely generated commutative
groups. -/
noncomputable def relabelHom (τ : Equiv.Perm sigma) :
    characterGroup sigma ⟶ characterGroup sigma :=
  FGCommGrpCat.ofHom (characterRelabel τ)

/-- The underlying monoid homomorphism of `relabelHom`. -/
@[simp]
theorem toMonoidHom_relabelHom (τ : Equiv.Perm sigma) :
    FGCommGrpCat.toMonoidHom (relabelHom τ) = characterRelabel τ :=
  (rfl)

/-- Relabelling of character groups is multiplicative in the permutation. -/
theorem relabelHom_comp (τ ν : Equiv.Perm sigma) :
    relabelHom ν ≫ relabelHom τ = relabelHom (sigma := sigma) (τ * ν) := by
  apply FGCommGrpCat.hom_ext
  rw [FGCommGrpCat.toMonoidHom_comp, toMonoidHom_relabelHom, toMonoidHom_relabelHom,
    toMonoidHom_relabelHom, characterRelabel_comp]

/-- Relabelling of character groups by the identity permutation is the identity. -/
theorem relabelHom_one : relabelHom (sigma := sigma) 1 = CategoryStruct.id _ := by
  apply FGCommGrpCat.hom_ext
  rw [toMonoidHom_relabelHom, characterRelabel_one, FGCommGrpCat.toMonoidHom_id]

variable (R : Type u) [CommRing R]

/-- **The relabelling automorphism of the coordinate Hopf algebra of the split torus.** -/
noncomputable def relabelCoordinateMap (τ : Equiv.Perm sigma) :
    (DiagonalizableGroup.coordinateRing R (characterGroup sigma)).obj ⟶
      (DiagonalizableGroup.coordinateRing R (characterGroup sigma)).obj :=
  (DiagonalizableGroup.coordinateMap R (relabelHom τ)).hom

/-- The bialgebra morphism underlying the coordinate relabelling. -/
theorem hom_relabelCoordinateMap (τ : Equiv.Perm sigma) :
    (relabelCoordinateMap R τ).hom =
      MonoidAlgebra.mapDomainBialgHom R (characterRelabel τ) :=
  (rfl)

/-- Coordinate relabelling is multiplicative in the permutation. -/
theorem relabelCoordinateMap_comp (τ ν : Equiv.Perm sigma) :
    relabelCoordinateMap R τ ≫ relabelCoordinateMap R ν =
      relabelCoordinateMap (sigma := sigma) R (ν * τ) := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [_root_.CommHopfAlgCat.hom_comp, hom_relabelCoordinateMap, hom_relabelCoordinateMap,
    hom_relabelCoordinateMap, ← characterRelabel_comp, MonoidAlgebra.mapDomainBialgHom_comp]

/-- Coordinate relabelling by the identity permutation is the identity. -/
theorem relabelCoordinateMap_one :
    relabelCoordinateMap (sigma := sigma) R 1 = CategoryStruct.id _ := by
  apply _root_.CommHopfAlgCat.hom_ext
  rw [hom_relabelCoordinateMap, characterRelabel_one, MonoidAlgebra.mapDomainBialgHom_id]
  rfl

/-- Coordinate relabelling is injective, being an isomorphism. -/
theorem relabelCoordinateMap_injective (τ : Equiv.Perm sigma) :
    Function.Injective (relabelCoordinateMap (sigma := sigma) R τ).hom := by
  intro x y hxy
  rw [hom_relabelCoordinateMap] at hxy
  have h := congrArg
    (MonoidAlgebra.mapDomainBialgHom R (characterRelabel (sigma := sigma) τ⁻¹)) hxy
  rwa [MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom,
    MonoidAlgebra.mapDomainBialgHom_mapDomainBialgHom, characterRelabel_comp,
    inv_mul_cancel, characterRelabel_one, MonoidAlgebra.mapDomainBialgHom_id] at h

/-- **The relabelling automorphism of the split-torus group scheme.** On points it permutes the
coordinates by `τ`. -/
noncomputable def relabel (τ : Equiv.Perm sigma) :
    groupScheme R sigma ⟶ groupScheme R sigma :=
  DiagonalizableGroup.groupSchemeMap R (relabelHom τ)

/-- Relabelling of group schemes is multiplicative in the permutation. -/
theorem relabel_comp (τ ν : Equiv.Perm sigma) :
    relabel R τ ≫ relabel R ν = relabel (sigma := sigma) R (τ * ν) := by
  rw [relabel, relabel, relabel, ← DiagonalizableGroup.groupSchemeMap_comp,
    relabelHom_comp]

/-- Relabelling by the identity permutation is the identity. -/
theorem relabel_one : relabel (sigma := sigma) R 1 = CategoryStruct.id _ := by
  rw [relabel, relabelHom_one, DiagonalizableGroup.groupSchemeMap_id]

/-- The group-scheme relabelling is the spectrum of the coordinate relabelling, read across the
canonical presentation of the split torus. -/
theorem relabel_def (τ : Equiv.Perm sigma) :
    relabel R τ =
      eqToHom (DiagonalizableGroup.groupScheme_def R (characterGroup sigma)) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map (relabelCoordinateMap R τ).op ≫
        eqToHom (DiagonalizableGroup.groupScheme_def R (characterGroup sigma)).symm :=
  DiagonalizableGroup.groupSchemeMap_def R (relabelHom τ)

end TauCeti.SplitTorus
