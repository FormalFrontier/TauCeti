/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Frobenius.GeneralLinear
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# Functorial points of the Geck group scheme

For a valid Dynkin type `t`, `TauCeti.DynkinType.geckPoints t ht A` is the group of `A`-valued
points of the explicit integral Geck carrier, written as a subgroup of `GLₙ(A)`. This file makes
the dependence on the value ring functorial. A morphism of commutative rings acts
entrywise on matrices and restricts to a homomorphism of Geck point groups; these maps assemble
into `TauCeti.DynkinType.geckPointsFunctor`.

The `p ^ k`-power Frobenius is then a named endomorphism of the Geck point group over every ring of
exponential characteristic `p`. Its matrix entries are raised to `p ^ k`, the zeroth iterate is
the identity, and addition of exponents is composition. Over an algebraic closure of `ZMod p`,
this is the untwisted field part of the Steinberg endomorphism required by the finite-groups-of-Lie-
type consumer.

## Main declarations

* `TauCeti.DynkinType.mapGeckPoints`: the map on Geck points induced by a value-algebra morphism.
* `TauCeti.DynkinType.geckPointsFunctor`: the group-valued functor of points of the Geck carrier,
  in its explicit matrix realization.
* `TauCeti.DynkinType.iterateFrobeniusGeckPoints`: the `p ^ k`-power Frobenius endomorphism on
  Geck points.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §1.15 and §2.1.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

This completes the functoriality and Frobenius part of "Points over an algebraically closed field"
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. The pinned graph automorphisms and the
identification of the carrier with the required simply connected form remain separate targets.
-/

public section

open CategoryTheory

namespace TauCeti.DynkinType

universe v

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-! ## Functoriality in the value algebra -/

/-- A morphism of commutative rings induces a homomorphism between the corresponding
groups of Geck points by applying it entrywise to the ambient invertible matrices. -/
noncomputable def mapGeckPoints {A B : CommRingCat.{v}} (f : A ⟶ B) :
    t.geckPoints ht A →* t.geckPoints ht B :=
  (((Matrix.GeneralLinearGroup.map f.hom.toIntAlgHom.toRingHom).domRestrict
    (t.geckPoints ht A)).codRestrict (t.geckPoints ht B) fun g => by
      have hg : (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) ∈
          GeneralLinear.hopfIdealPointsSubgroup
            (t.geckDim ht) (t.geckDefiningIdeal ht) A := by
        rw [← t.geckPoints_def ht A]
        exact g.property
      rw [t.geckPoints_def ht B]
      exact GeneralLinear.map_mem_hopfIdealPointsSubgroup
        (t.geckDim ht) (t.geckDefiningIdeal ht) f.hom.toIntAlgHom hg)

/-- The map on Geck points induced by a value-algebra morphism is entrywise application on the
ambient invertible matrix. -/
@[simp]
theorem coe_mapGeckPoints {A B : CommRingCat.{v}} (f : A ⟶ B)
    (g : t.geckPoints ht A) :
    (t.mapGeckPoints ht f g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) =
      Matrix.GeneralLinearGroup.map f.hom g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

/-- The identity value-algebra morphism induces the identity on Geck points. -/
@[simp]
theorem mapGeckPoints_id (A : CommRingCat.{v}) :
    t.mapGeckPoints ht (𝟙 A) = MonoidHom.id (t.geckPoints ht A) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_mapGeckPoints, Matrix.GeneralLinearGroup.map_apply, MonoidHom.id_apply]
  rfl

/-- Maps on Geck points preserve composition of value-algebra morphisms. -/
@[simp]
theorem mapGeckPoints_comp {A B C : CommRingCat.{v}} (f : A ⟶ B) (g : B ⟶ C) :
    t.mapGeckPoints ht (f ≫ g) =
      (t.mapGeckPoints ht g).comp (t.mapGeckPoints ht f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [coe_mapGeckPoints, Matrix.GeneralLinearGroup.map_apply,
    CategoryTheory.ConcreteCategory.comp_apply, MonoidHom.comp_apply]

/-- An injective value-algebra morphism induces an injective map on Geck points. -/
theorem mapGeckPoints_injective {A B : CommRingCat.{v}} {f : A ⟶ B}
    (hf : Function.Injective f) : Function.Injective (t.mapGeckPoints ht f) := by
  have hmap : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin (t.geckDim ht)) f.hom) :=
    Units.map_injective (Matrix.map_injective hf)
  intro g g' h
  apply Subtype.ext
  apply hmap
  rw [← coe_mapGeckPoints, ← coe_mapGeckPoints, h]

/-- The group-valued functor sending a commutative ring to the explicit matrix group of
points of the Geck carrier. -/
noncomputable def geckPointsFunctor :
    CategoryTheory.Functor CommRingCat.{v} GrpCat.{v} where
  obj A := GrpCat.of (t.geckPoints ht A)
  map f := GrpCat.ofHom (t.mapGeckPoints ht f)
  map_id A := congrArg GrpCat.ofHom (t.mapGeckPoints_id ht A)
  map_comp f g := congrArg GrpCat.ofHom (t.mapGeckPoints_comp ht f g)

/-- The object part of the Geck points functor is the explicit matrix point group. -/
@[simp]
theorem geckPointsFunctor_obj (A : CommRingCat.{v}) :
    (t.geckPointsFunctor ht).obj A = GrpCat.of (t.geckPoints ht A) :=
  (rfl)

/-- The morphism part of the Geck points functor is the restricted entrywise matrix map. -/
@[simp]
theorem geckPointsFunctor_map {A B : CommRingCat.{v}} (f : A ⟶ B) :
    (t.geckPointsFunctor ht).map f =
      eqToHom (t.geckPointsFunctor_obj ht A) ≫
        GrpCat.ofHom (t.mapGeckPoints ht f) ≫
      eqToHom (t.geckPointsFunctor_obj ht B).symm :=
  (rfl)

/-! ## Frobenius on the explicit carrier -/

/-- The `p ^ k`-power Frobenius endomorphism of the explicit Geck point group over `A`. -/
noncomputable def iterateFrobeniusGeckPoints (p k : ℕ) (A : Type v)
    [CommRing A] [ExpChar A p] :
    t.geckPoints ht A →* t.geckPoints ht A :=
  t.mapGeckPoints ht (CommRingCat.ofHom (iterateFrobenius A p k))

variable (p k : ℕ)
variable {A : Type v} [CommRing A] [ExpChar A p]

/-- The Frobenius endomorphism of Geck points is the entrywise Frobenius on the ambient matrix. -/
@[simp]
theorem coe_iterateFrobeniusGeckPoints (g : t.geckPoints ht A) :
    (t.iterateFrobeniusGeckPoints ht p k A g :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      Matrix.GeneralLinearGroup.map (iterateFrobenius A p k) g := by
  exact t.coe_mapGeckPoints ht (CommRingCat.ofHom (iterateFrobenius A p k)) g

/-- A Geck point is fixed by Frobenius exactly when each matrix entry belongs to the Frobenius-
fixed subring. -/
@[simp]
theorem iterateFrobeniusGeckPoints_eq_self_iff (g : t.geckPoints ht A) :
    t.iterateFrobeniusGeckPoints ht p k A g = g ↔
      ∀ i j, (((g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) i j) ∈
          frobeniusFixedSubring A p k := by
  rw [← SetLike.coe_eq_coe, coe_iterateFrobeniusGeckPoints,
    Matrix.GeneralLinearGroup.map_iterateFrobenius_eq_self_iff]

/-- The zeroth Frobenius iterate is the identity on Geck points. -/
@[simp]
theorem iterateFrobeniusGeckPoints_zero :
    t.iterateFrobeniusGeckPoints ht p 0 A = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [coe_iterateFrobeniusGeckPoints, MonoidHom.id_apply, iterateFrobenius_zero,
    Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]

/-- Frobenius iterates add under composition on Geck points. -/
theorem iterateFrobeniusGeckPoints_add (m : ℕ) :
    t.iterateFrobeniusGeckPoints ht p (k + m) A =
      (t.iterateFrobeniusGeckPoints ht p k A).comp
        (t.iterateFrobeniusGeckPoints ht p m A) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [coe_iterateFrobeniusGeckPoints, MonoidHom.comp_apply,
    coe_iterateFrobeniusGeckPoints, coe_iterateFrobeniusGeckPoints,
    iterateFrobenius_add, Matrix.GeneralLinearGroup.map_comp, MonoidHom.comp_apply]

end

end TauCeti.DynkinType
