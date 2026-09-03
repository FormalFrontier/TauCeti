/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic

/-!
# Functorial points of the full-weight type-D spin carrier

`TauCeti.TypeDSpinCarrier.points n hn A` realizes the `A`-valued points of the full-weight
type-`Dₙ` spin carrier as a subgroup of `GL_(2^n)(A)`. This file supplies the group homomorphism
induced by a homomorphism of value rings, together with its identity, composition, and
injectivity laws.

## Main declarations

* `TauCeti.TypeDSpinCarrier.pointsMap`: the map on carrier points induced by a ring homomorphism.
* `TauCeti.TypeDSpinCarrier.pointsMap_id` and
  `TauCeti.TypeDSpinCarrier.pointsMap_comp`: functoriality of the induced maps.
* `TauCeti.TypeDSpinCarrier.pointsMap_injective`: injectivity when the ring homomorphism is
  injective.
* `TauCeti.TypeDSpinCarrier.pointsMap_rootSubgroupPoints` and
  `TauCeti.TypeDSpinCarrier.pointsMap_weightTorusPoints`: naturality of the distinguished
  root-subgroup and weight-torus families.
* `TauCeti.TypeDSpinCarrier.pointsFunctor`: the bundled group-valued points functor.
* `TauCeti.TypeDSpinCarrier.pointsMulEquiv` and
  `TauCeti.TypeDSpinCarrier.pointsFunctorNatIso`: the pointwise and natural representing
  isomorphisms.

The interface follows the analogous full-weight type-`A`, type-`C`, and type-`E₆` carrier
interfaces. It advances the functorial-points target in Layer 9 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe v w

noncomputable section

variable (n : ℕ) (hn : 4 ≤ n)

section Map

variable {A : Type v} {B : Type w} [CommRing A] [CommRing B]

/-- The map on type-`Dₙ` spin-carrier points induced by a homomorphism of value rings. It is the
entrywise map on the ambient general linear group, restricted to the carrier subgroup. -/
def pointsMap (f : A →+* B) : points n hn A →* points n hn B :=
  ((MulEquiv.subgroupCongr (points_def n hn B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup (dimension n) (definingIdeal n hn)
          f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (points_def n hn A)).toMonoidHom)

/-- The induced map on type-`Dₙ` spin-carrier points is the entrywise matrix map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points n hn A) :
    (pointsMap n hn f g : Matrix.GeneralLinearGroup (Fin (dimension n)) B) =
      Matrix.GeneralLinearGroup.map f g := by
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [pointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_symm_apply, GeneralLinear.coe_mapHopfIdealPointsSubgroup,
    MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points n hn A)
    (i j : Fin (dimension n)) :
    ((pointsMap n hn f g : Matrix.GeneralLinearGroup (Fin (dimension n)) B) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism induces the identity on type-`Dₙ` spin-carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap n hn (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A := AlgHom.ext fun _ ↦ rfl
  rw [pointsMap, hid, GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr (points_def n hn A)).symm_apply_apply g

/-- The induced maps on type-`Dₙ` spin-carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap n hn (g.comp f) = (pointsMap n hn g).comp (pointsMap n hn f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective homomorphism of value rings induces an injective map on type-`Dₙ` spin-carrier
points. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap n hn f) := by
  rw [pointsMap]
  exact (MulEquiv.subgroupCongr (points_def n hn B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective
      (dimension n) (definingIdeal n hn) hf).comp
        (MulEquiv.subgroupCongr (points_def n hn A)).injective)

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B) (k : Fin n ⊕ Fin n)
    (u : Multiplicative A) :
    pointsMap n hn f (rootSubgroupPoints n hn k A u) =
      rootSubgroupPoints n hn k B
        (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the split spin weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin n → Aˣ) :
    pointsMap n hn f (weightTorusPoints n hn A s) =
      weightTorusPoints n hn B fun i ↦ Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice n).toAddSubgroup) (b := latticeBasis n) (wt := basisWeight n) f s

end Map

/-! ## The functor of points -/

section Functor

/-- The group-valued functor of points of the full-weight type-`Dₙ` spin carrier. -/
def pointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (points n hn A)
  map f := GrpCat.ofHom (pointsMap n hn f.hom.toRingHom)
  map_id _A := congrArg GrpCat.ofHom (pointsMap_id n hn)
  map_comp f g := congrArg GrpCat.ofHom
    (pointsMap_comp n hn f.hom.toRingHom g.hom.toRingHom)

/-- The object part of the type-`Dₙ` spin carrier's points functor is its named point group. -/
@[simp]
theorem pointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    (pointsFunctor n hn).obj A = GrpCat.of (points n hn A) :=
  (rfl)

/-- The morphism part of the type-`Dₙ` spin carrier's points functor is the induced entrywise
map. -/
@[simp]
theorem pointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    (pointsFunctor n hn).map f =
      eqToHom (pointsFunctor_obj n hn A) ≫
        GrpCat.ofHom (pointsMap n hn f.hom.toRingHom) ≫
        eqToHom (pointsFunctor_obj n hn B).symm :=
  (rfl)

/-- At a bundled `ℤ`-algebra, the named carrier points are the ambient general-linear subgroup
cut out by the defining ideal. -/
private theorem points_eq_hopfIdealPointsSubgroup (A : CommAlgCat.{v} ℤ) :
    points n hn A =
      GeneralLinear.hopfIdealPointsSubgroup (dimension n) (definingIdeal n hn) A := by
  rw [points_def n hn A]
  congr 1
  exact Subsingleton.elim _ _

/-- The points of the quotient coordinate Hopf algebra are the named type-`Dₙ` spin-carrier
points. -/
def pointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) A ≃*
      points n hn A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv (dimension n)
      (definingIdeal n hn) A).trans
    (MulEquiv.subgroupCongr (points_eq_hopfIdealPointsSubgroup n hn A)).symm

/-- A quotient point, read through `pointsMulEquiv`, is its ambient point viewed as an invertible
matrix. -/
@[simp]
theorem coe_pointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) A) :
    (pointsMulEquiv n hn A q : Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      GeneralLinear.pointsMulEquiv (dimension n)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)
          A q) := by
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply
    (dimension n) (definingIdeal n hn) A q

/-- Including the ambient Hopf-algebra point underlying the inverse of `pointsMulEquiv` recovers
the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (A : CommAlgCat.{v} ℤ)
    (g : points n hn A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) A
        ((pointsMulEquiv n hn A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm
        (g : Matrix.GeneralLinearGroup (Fin (dimension n)) A) := by
  simp only [pointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [GeneralLinear.quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm,
    MulEquiv.subgroupCongr_apply]

/-- The pointwise identification with quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem pointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) A) :
    pointsMulEquiv n hn B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn))
          f q) =
      pointsMap n hn f.hom.toRingHom (pointsMulEquiv n hn A q) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints
        (dimension n) (definingIdeal n hn) f q)).trans
    (GeneralLinear.coe_mapHopfIdealPointsSubgroup
      (dimension n) (definingIdeal n hn) f.hom _)

/-- The quotient coordinate Hopf algebra represents the points functor of the full-weight
type-`Dₙ` spin carrier. -/
def pointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) ≅
      pointsFunctor n hn :=
  NatIso.ofComponents (fun A ↦ (pointsMulEquiv n hn A).toGrpIso)
    (by
      intro A B f
      ext q
      exact pointsMulEquiv_mapPoints n hn f q)

/-- The forward component of the representing natural isomorphism is the pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) A) :
    eqToHom (pointsFunctor_obj n hn A) ((pointsFunctorNatIso n hn).hom.app A q) =
      pointsMulEquiv n hn A q :=
  (rfl)

/-- The inverse component of the representing natural isomorphism is the inverse pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : points n hn A) :
    (pointsFunctorNatIso n hn).inv.app A (eqToHom (pointsFunctor_obj n hn A).symm g) =
      (pointsMulEquiv n hn A).symm g :=
  (rfl)

end Functor

end

end TauCeti.TypeDSpinCarrier
