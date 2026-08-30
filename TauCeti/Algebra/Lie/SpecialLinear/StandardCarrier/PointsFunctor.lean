/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic

/-!
# The points of the full-weight type-A carrier, functorially in the value ring

`TauCeti.SlStd.groupScheme r` is the explicit full-weight Chevalley carrier of type `A_r` over `ℤ`,
and `TauCeti.SlStd.points r A` reads its `A`-valued points as a subgroup of `GL_{r+1}(A)`. Those
point groups have so far been available one value ring at a time. This file supplies the group
homomorphism induced by an arbitrary homomorphism of value rings and assembles the point groups
into a functor on commutative `ℤ`-algebras.

The induced map is entrywise, so on the pinned generating families it acts by

```text
f (x_k(u)) = x_k(f u),        f (t(s)) = t(f ∘ s),
```

with `k` ranging over the numbered raising and lowering generators. Read at
`iterateFrobenius A p k` it is the `p ^ k`-power Frobenius endomorphism of the carrier, which is
`TauCeti.SlStd.frobenius_eq_pointsMap` in
`TauCeti/Algebra/Lie/SpecialLinear/StandardCarrier/Frobenius.lean`.

The quotient of the ambient general-linear coordinate Hopf algebra by
`TauCeti.SlStd.definingIdeal` represents this functor. Nothing here identifies the carrier's points
with the elementary subgroup its root subgroups generate, and nothing asserts that any group in
sight is finite or simple.

## Main definitions

* `TauCeti.SlStd.pointsMap`: the map on carrier points induced by a homomorphism of value rings.
* `TauCeti.SlStd.pointsFunctor`: the resulting group-valued functor on commutative `ℤ`-algebras.
* `TauCeti.SlStd.pointsMulEquiv` and `TauCeti.SlStd.pointsFunctorNatIso`: the pointwise and natural
  representing isomorphisms.

## Main results

* `TauCeti.SlStd.coe_pointsMap` and `TauCeti.SlStd.coe_pointsMap_apply`: the induced map is the
  entrywise one.
* `TauCeti.SlStd.pointsMap_id` and `TauCeti.SlStd.pointsMap_comp`: the functoriality laws.
* `TauCeti.SlStd.pointsMap_injective`: an injective homomorphism of value rings induces an
  injective map of points.
* `TauCeti.SlStd.pointsMap_rootSubgroupPoints` and `TauCeti.SlStd.pointsMap_weightTorusPoints`:
  naturality of the pinned root subgroups and of the pinned split weight torus.

## References

* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

The interface follows the carrier-independent functor in
`TauCeti/Algebra/AlgebraicGroup/GeneralLinear/HopfIdealPoints/Functor.lean` and the parallel
specializations for the pinned Geck carrier and for the full-weight type-C carrier in
`TauCeti/Algebra/Lie/Symplectic/StandardCarrier/PointsFunctor.lean`. This completes the target
"points over an algebraically closed field as a group, functorially in the field, so that a field
endomorphism induces a group endomorphism of the points" of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md` for the full-weight type-A carrier. Its consumer is the
type-`A` branch of milestone L0 of `TauCetiRoadmap/CFSGStatement/README.md`, which reads the ambient
group of a finite group of Lie type off the points of a pinned Chevalley--Demazure group over an
algebraic closure of `ZMod p`.
-/

public section

open CategoryTheory

namespace TauCeti.SlStd

universe v v'

noncomputable section

variable (r : ℕ)

section Map

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- **The map on the points of the full-weight type-`A_r` carrier induced by a homomorphism of
value rings.** It is `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup` read at the carrier's
defining Hopf ideal, transported along `TauCeti.SlStd.points_def` so that it is stated in the named
type-`A` API rather than in the presentation that API is defined by. -/
def pointsMap (f : A →+* B) : points r A →* points r B :=
  ((MulEquiv.subgroupCongr (points_def r B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup (r + 1) (definingIdeal r) f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (points_def r A)).toMonoidHom)

/-- The induced map on type-`A_r` carrier points is the entrywise map. -/
@[simp]
theorem coe_pointsMap (f : A →+* B) (g : points r A) :
    (pointsMap r f g : Matrix.GeneralLinearGroup (Fin (r + 1)) B) =
      Matrix.GeneralLinearGroup.map f g := by
  -- `mapHopfIdealPointsSubgroup` is stated for the `ℤ`-algebra map induced by `f`, whose
  -- underlying ring homomorphism is `f` again.
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [pointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_symm_apply,
    GeneralLinear.coe_mapHopfIdealPointsSubgroup, MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map applies the homomorphism of value rings to each matrix entry. -/
theorem coe_pointsMap_apply (f : A →+* B) (g : points r A) (i j : Fin (r + 1)) :
    ((pointsMap r f g : Matrix.GeneralLinearGroup (Fin (r + 1)) B) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) B) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j) := by
  rw [coe_pointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism of value rings induces the identity on type-`A_r` carrier points. -/
@[simp]
theorem pointsMap_id : pointsMap r (RingHom.id A) = MonoidHom.id _ := by
  have hid : (RingHom.id A).toIntAlgHom = AlgHom.id ℤ A :=
    AlgHom.ext fun _ ↦ rfl
  rw [pointsMap, hid, GeneralLinear.mapHopfIdealPointsSubgroup_id]
  apply MonoidHom.ext
  intro g
  exact (MulEquiv.subgroupCongr (points_def r A)).symm_apply_apply g

/-- The induced maps on type-`A_r` carrier points compose. -/
@[simp]
theorem pointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    pointsMap r (g.comp f) = (pointsMap r g).comp (pointsMap r f) := by
  have hcomp : (g.comp f).toIntAlgHom = g.toIntAlgHom.comp f.toIntAlgHom :=
    AlgHom.ext fun _ ↦ rfl
  apply MonoidHom.ext
  intro x
  simp only [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hcomp,
    GeneralLinear.mapHopfIdealPointsSubgroup_comp, MulEquiv.apply_symm_apply]

/-- An injective homomorphism of value rings induces an injective map on type-`A_r` carrier
points. -/
theorem pointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (pointsMap r f) := by
  rw [pointsMap]
  exact (MulEquiv.subgroupCongr (points_def r B)).symm.injective.comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup_injective (r + 1) (definingIdeal r) hf).comp
      (MulEquiv.subgroupCongr (points_def r A)).injective)

/-- The induced map carries a numbered root-subgroup parameter along the homomorphism of value
rings. -/
@[simp]
theorem pointsMap_rootSubgroupPoints (f : A →+* B) (k : Fin r ⊕ Fin r) (u : Multiplicative A) :
    pointsMap r f (rootSubgroupPoints r k A u) =
      rootSubgroupPoints r k B (Multiplicative.ofAdd (f (Multiplicative.toAdd u))) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_rootSubgroupPoints, coe_rootSubgroupPoints,
    UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply]

/-- The induced map carries a point of the pinned split weight torus coordinatewise along the
homomorphism of value rings. -/
@[simp]
theorem pointsMap_weightTorusPoints (f : A →+* B) (s : Fin r → Aˣ) :
    pointsMap r f (weightTorusPoints r A s) =
      weightTorusPoints r B fun i => Units.map (f : A →* B) (s i) := by
  apply Subtype.ext
  rw [coe_pointsMap, coe_weightTorusPoints, coe_weightTorusPoints]
  exact UniversalEnvelopingAlgebra.map_kostantTorusMatrix
    (M := (lattice r).toAddSubgroup) (b := latticeBasis r) (wt := weight r) f s

end Map

/-! ## The functor of points -/

section Functor

/-- The group-valued functor of points of the full-weight type-`A_r` carrier. -/
def pointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (points r A)
  map f := GrpCat.ofHom (pointsMap r f.hom.toRingHom)
  map_id _A := congrArg GrpCat.ofHom (pointsMap_id r)
  map_comp f g := congrArg GrpCat.ofHom (pointsMap_comp r f.hom.toRingHom g.hom.toRingHom)

/-- The object part of the type-`A_r` carrier's points functor is its named point group. -/
@[simp]
theorem pointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    (pointsFunctor r).obj A = GrpCat.of (points r A) :=
  (rfl)

/-- The morphism part of the type-`A_r` carrier's points functor is the induced entrywise map. -/
@[simp]
theorem pointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    (pointsFunctor r).map f =
      eqToHom (pointsFunctor_obj r A) ≫
        GrpCat.ofHom (pointsMap r f.hom.toRingHom) ≫
        eqToHom (pointsFunctor_obj r B).symm :=
  (rfl)

/-- At a bundled `ℤ`-algebra, the named carrier points are the ambient general-linear subgroup cut
out by the defining ideal. -/
private theorem points_eq_hopfIdealPointsSubgroup (A : CommAlgCat.{v} ℤ) :
    points r A = GeneralLinear.hopfIdealPointsSubgroup (r + 1) (definingIdeal r) A := by
  rw [points_def r A]
  congr 1
  exact Subsingleton.elim _ _

/-- The points of the quotient coordinate Hopf algebra are the named type-`A_r` carrier points. -/
def pointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) A ≃*
      points r A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv (r + 1) (definingIdeal r) A).trans
    (MulEquiv.subgroupCongr (points_eq_hopfIdealPointsSubgroup r A)).symm

/-- A quotient point, read through `TauCeti.SlStd.pointsMulEquiv`, is its ambient point viewed as
an invertible matrix. -/
@[simp]
theorem coe_pointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) A) :
    (pointsMulEquiv r A q : Matrix.GeneralLinearGroup (Fin (r + 1)) A) =
      GeneralLinear.pointsMulEquiv (r + 1)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r) A q) := by
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply (r + 1) (definingIdeal r) A q

/-- Including the ambient Hopf-algebra point underlying the inverse of
`TauCeti.SlStd.pointsMulEquiv` recovers the point corresponding to the underlying matrix. -/
@[simp]
theorem quotientPointsHom_pointsMulEquiv_symm (A : CommAlgCat.{v} ℤ) (g : points r A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r) A
        ((pointsMulEquiv r A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) (r + 1)).symm
        (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) := by
  simp only [pointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [GeneralLinear.quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm,
    MulEquiv.subgroupCongr_apply]

/-- The pointwise identification with quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem pointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) A) :
    pointsMulEquiv r B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) f q) =
      pointsMap r f.hom.toRingHom (pointsMulEquiv r A q) := by
  apply Subtype.ext
  rw [coe_pointsMap]
  simp only [pointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints (r + 1) (definingIdeal r) f q)).trans
    (GeneralLinear.coe_mapHopfIdealPointsSubgroup (r + 1) (definingIdeal r) f.hom _)

/-- The quotient coordinate Hopf algebra represents the points functor of the full-weight type-`A_r`
carrier. -/
def pointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) ≅
      pointsFunctor r :=
  NatIso.ofComponents (fun A => (pointsMulEquiv r A).toGrpIso)
    (by
      intro A B f
      ext q
      exact pointsMulEquiv_mapPoints r f q)

/-- The forward component of the representing natural isomorphism is the pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) (definingIdeal r)) A) :
    eqToHom (pointsFunctor_obj r A) ((pointsFunctorNatIso r).hom.app A q) =
      pointsMulEquiv r A q :=
  (rfl)

/-- The inverse component of the representing natural isomorphism is the inverse pointwise
identification. -/
@[simp]
theorem pointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : points r A) :
    (pointsFunctorNatIso r).inv.app A (eqToHom (pointsFunctor_obj r A).symm g) =
      (pointsMulEquiv r A).symm g :=
  (rfl)

end Functor

end

end TauCeti.SlStd
