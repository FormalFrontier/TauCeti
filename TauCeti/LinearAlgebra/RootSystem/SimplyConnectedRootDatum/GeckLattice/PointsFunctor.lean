/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Functor
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme

/-!
# The points of the pinned Geck carrier, functorially in the value ring

`TauCeti.DynkinType.geckGroupScheme` is the explicit affine group scheme over `ℤ` attached to a
valid Dynkin type, and `TauCeti.DynkinType.geckPoints` reads its `A`-valued points as a subgroup
of `GLₙ(A)`. Those point groups have so far been available one value ring at a time, together with
the single endomorphism induced by the `p ^ k`-power Frobenius. This file supplies the map induced
by an arbitrary homomorphism of value rings, and assembles the point groups into a functor.

The induced map is entrywise, so on the pinned generating families it acts by

```text
f (xᵢ(u)) = xᵢ(f u),        f (t(s)) = t(f ∘ s),
```

with `i` ranging over the numbered raising and lowering generators. Reading this at
`iterateFrobenius A p k` gives the `q`-power Frobenius endomorphism of the carrier, which
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Frobenius` defines as
exactly this map's value there.

Nothing here identifies the carrier's points with the elementary subgroup its root subgroups
generate; that needs a generation theorem which is not available. The Geck weights span the root
lattice rather than, in general, the full character lattice, so this carrier is not yet the simply
connected one a finite group of Lie type is built from. Nothing below asserts that any subgroup
appearing in it is finite, is simple, or is a named finite group.

## Main definitions

* `TauCeti.DynkinType.geckPointsMap`: the group homomorphism on the points of the pinned Geck
  carrier induced by a homomorphism of value rings.
* `TauCeti.DynkinType.geckPointsFunctor`: the resulting group-valued functor on commutative
  `ℤ`-algebras.
* `TauCeti.DynkinType.geckPointsMulEquiv` and `TauCeti.DynkinType.geckPointsFunctorNatIso`: the
  quotient of the general-linear coordinate Hopf algebra by the Geck defining ideal represents
  that functor, pointwise and naturally.

## Main results

* `TauCeti.DynkinType.coe_geckPointsMap`: the induced map is the entrywise one.
* `TauCeti.DynkinType.geckPointsMap_id` and `TauCeti.DynkinType.geckPointsMap_comp`: the
  functoriality laws.
* `TauCeti.DynkinType.geckPointsMap_injective`: an injective homomorphism of value rings induces
  an injective map of points.
* `TauCeti.DynkinType.geckPointsMap_geckRootSubgroupMatrix` and
  `TauCeti.DynkinType.geckPointsMap_geckTorusMatrix`: the equations on the pinned root subgroups
  and on the pinned weight torus.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.

This is the pinned instance of the target "points over an algebraically closed field as a group,
functorially in the field, so that a field endomorphism induces a group endomorphism of the points"
in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`, whose carrier-independent half is
`TauCeti.GeneralLinear.hopfIdealPointsSubgroupFunctor`. Its consumer is milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`, which reads the carrier of a finite group of Lie type off
the points of a pinned Chevalley--Demazure group over an algebraic closure of `ZMod p`.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.DynkinType

universe v v'

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads them.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

section Map

variable {A : Type v} {B : Type v'} [CommRing A] [CommRing B]

/-- **The map on the points of the pinned Geck carrier induced by a homomorphism of value
rings.** It is `TauCeti.GeneralLinear.mapHopfIdealPointsSubgroup` read at the carrier's defining
Hopf ideal, transported along `TauCeti.DynkinType.geckPoints_def` so that it is stated in the
named Geck API a consumer works in rather than in the presentation that API is defined by. -/
def geckPointsMap (f : A →+* B) : t.geckPoints ht A →* t.geckPoints ht B :=
  ((MulEquiv.subgroupCongr (t.geckPoints_def ht B)).symm.toMonoidHom).comp
    ((GeneralLinear.mapHopfIdealPointsSubgroup (t.geckDim ht) (t.geckDefiningIdeal ht)
          f.toIntAlgHom).comp
      (MulEquiv.subgroupCongr (t.geckPoints_def ht A)).toMonoidHom)

/-- The induced map on the points of the pinned Geck carrier is the entrywise one. -/
@[simp]
theorem coe_geckPointsMap (f : A →+* B) (g : t.geckPoints ht A) :
    (t.geckPointsMap ht f g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) =
      Matrix.GeneralLinearGroup.map f g := by
  -- `mapHopfIdealPointsSubgroup` is stated for the `ℤ`-algebra map that `f` induces, whose
  -- underlying ring homomorphism is `f` again.
  have hring : f.toIntAlgHom.toRingHom = f := RingHom.ext (RingHom.toIntAlgHom_apply f)
  rw [geckPointsMap]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_symm_apply,
    GeneralLinear.coe_mapHopfIdealPointsSubgroup, MulEquiv.subgroupCongr_apply, hring]

/-- Entrywise, the induced map on the points of the pinned Geck carrier applies the homomorphism
of value rings to each matrix entry. -/
theorem coe_geckPointsMap_apply (f : A →+* B) (g : t.geckPoints ht A)
    (r c : Fin (t.geckDim ht)) :
    ((t.geckPointsMap ht f g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) B) r c =
      f (((g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
        Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r c) := by
  rw [coe_geckPointsMap, Matrix.GeneralLinearGroup.map_apply]

/-- The identity homomorphism of value rings induces the identity on the points of the pinned
Geck carrier. -/
@[simp]
theorem geckPointsMap_id : t.geckPointsMap ht (RingHom.id A) = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => Subtype.ext (Matrix.GeneralLinearGroup.ext fun r c => ?_)
  rw [coe_geckPointsMap_apply, MonoidHom.id_apply, RingHom.id_apply]

/-- The induced maps on the points of the pinned Geck carrier compose. -/
@[simp]
theorem geckPointsMap_comp {C : Type*} [CommRing C] (f : A →+* B) (g : B →+* C) :
    t.geckPointsMap ht (g.comp f) =
      (t.geckPointsMap ht g).comp (t.geckPointsMap ht f) := by
  refine MonoidHom.ext fun x => Subtype.ext (Matrix.GeneralLinearGroup.ext fun r c => ?_)
  rw [coe_geckPointsMap_apply, MonoidHom.comp_apply, coe_geckPointsMap_apply,
    coe_geckPointsMap_apply, RingHom.comp_apply]

/-- An injective homomorphism of value rings induces an injective map on the points of the pinned
Geck carrier. -/
theorem geckPointsMap_injective {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (t.geckPointsMap ht f) := by
  intro x y hxy
  refine Subtype.ext (Matrix.GeneralLinearGroup.ext fun r c => hf ?_)
  rw [← coe_geckPointsMap_apply, ← coe_geckPointsMap_apply, hxy]

/-- **The induced map carries the parameter of a numbered Geck root subgroup along the
homomorphism of value rings.** This is the naturality of the pinned simple root subgroups, the
form in which a consumer states its conventions. -/
@[simp]
theorem geckPointsMap_geckRootSubgroupMatrix (f : A →+* B) (i : Fin t.rank ⊕ Fin t.rank)
    (u : Multiplicative A) :
    t.geckPointsMap ht f
        ⟨t.geckRootSubgroupMatrix ht i
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u),
          t.geckRootSubgroupMatrix_mem_geckPoints ht A i _⟩ =
      ⟨t.geckRootSubgroupMatrix ht i
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := B)).symm
            (Multiplicative.ofAdd (f (Multiplicative.toAdd u)))),
        t.geckRootSubgroupMatrix_mem_geckPoints ht B i _⟩ :=
  Subtype.ext (by
    rw [coe_geckPointsMap, TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix,
      AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply, RingHom.toIntAlgHom_apply])

/-- **The induced map carries a point of the pinned Geck weight torus along the homomorphism of
value rings**, parameter by parameter. The left-hand side is stated on the underlying diagonal
matrix, which is the simp normal form of a torus point. -/
@[simp]
theorem geckPointsMap_geckTorusMatrix (f : A →+* B) (s : Fin t.rank → Aˣ) :
    t.geckPointsMap ht f
        ⟨diagGL fun i => torusCharacter s (t.geckWeightFin ht i), by
          simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
            t.geckTorusMatrix_mem_geckPoints ht A s⟩ =
      ⟨t.geckTorusMatrix ht fun j => Units.map (f : A →* B) (s j),
        t.geckTorusMatrix_mem_geckPoints ht B _⟩ :=
  Subtype.ext (by
    rw [coe_geckPointsMap]
    simpa only [TauCeti.UniversalEnvelopingAlgebra.kostantTorusMatrix_apply] using
      TauCeti.UniversalEnvelopingAlgebra.map_kostantTorusMatrix
        (M := (t.geckCoordinateLattice ht).toAddSubgroup) (b := t.geckCoordinateBasisFin ht)
        (wt := t.geckWeightFin ht) f s)

end Map

/-! ## The functor of points -/

section Functor

/-- **The group-valued functor of points of the pinned Geck carrier**, sending a commutative
`ℤ`-algebra to the point group of the carrier over it and an algebra map to the entrywise map it
induces. Its values are the point groups themselves, where the carrier-independent
`TauCeti.GeneralLinear.hopfIdealPointsSubgroupFunctor` wraps them in a `ULift` to reach a
universe its own base ring may need. -/
def geckPointsFunctor : CommAlgCat.{v} ℤ ⥤ GrpCat.{v} where
  obj A := GrpCat.of (t.geckPoints ht A)
  map f := GrpCat.ofHom (t.geckPointsMap ht f.hom.toRingHom)
  map_id _A := congrArg GrpCat.ofHom (t.geckPointsMap_id ht)
  map_comp f g :=
    congrArg GrpCat.ofHom (t.geckPointsMap_comp ht f.hom.toRingHom g.hom.toRingHom)

/-- The object part of the functor of points of the pinned Geck carrier is its point group. -/
@[simp]
theorem geckPointsFunctor_obj (A : CommAlgCat.{v} ℤ) :
    (t.geckPointsFunctor ht).obj A = GrpCat.of (t.geckPoints ht A) :=
  (rfl)

/-- The morphism part of the functor of points of the pinned Geck carrier is the induced entrywise
map, transported along the object identification above. -/
@[simp]
theorem geckPointsFunctor_map {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B) :
    (t.geckPointsFunctor ht).map f =
      eqToHom (t.geckPointsFunctor_obj ht A) ≫
        GrpCat.ofHom (t.geckPointsMap ht f.hom.toRingHom) ≫
        eqToHom (t.geckPointsFunctor_obj ht B).symm :=
  (rfl)

/-- The morphism part of the functor of points evaluates as the induced entrywise map: the
transports along `TauCeti.DynkinType.geckPointsFunctor_obj` introduced by
`TauCeti.DynkinType.geckPointsFunctor_map` cancel on an applied point. -/
@[simp]
theorem geckPointsFunctor_map_apply {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (g : (t.geckPointsFunctor ht).obj A) :
    eqToHom (t.geckPointsFunctor_obj ht B)
        (eqToHom (t.geckPointsFunctor_obj ht B).symm
          (t.geckPointsMap ht (f.hom : ↑A →+* ↑B)
            (eqToHom (t.geckPointsFunctor_obj ht A) g))) =
      t.geckPointsMap ht (f.hom : ↑A →+* ↑B)
        (eqToHom (t.geckPointsFunctor_obj ht A) g) :=
  (rfl)

/-- At a bundled `ℤ`-algebra the points of the Geck carrier are the general-linear subgroup cut
out by its defining ideal, now with the bundled algebra structure: the two `ℤ`-algebra structures
in play agree because `ℤ`-algebra structures are unique. This implementation bridge is kept
private; consumers use the named Geck API. -/
private theorem geckPoints_eq_hopfIdealPointsSubgroup (A : CommAlgCat.{v} ℤ) :
    t.geckPoints ht A =
      GeneralLinear.hopfIdealPointsSubgroup (t.geckDim ht) (t.geckDefiningIdeal ht) A := by
  rw [t.geckPoints_def ht A]
  congr 1
  exact Subsingleton.elim _ _

/-- **The points of the pinned Geck carrier over a value algebra are the points of the quotient
Hopf algebra of its defining ideal.** This is the pointwise face of the representability below. -/
def geckPointsMulEquiv (A : CommAlgCat.{v} ℤ) :
    HopfAlgebra.points
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) A ≃*
      t.geckPoints ht A :=
  (GeneralLinear.hopfIdealPointsSubgroupMulEquiv (t.geckDim ht)
      (t.geckDefiningIdeal ht) A).trans
    (MulEquiv.subgroupCongr (t.geckPoints_eq_hopfIdealPointsSubgroup ht A)).symm

/-- A quotient point, viewed through `TauCeti.DynkinType.geckPointsMulEquiv`, is its included
ambient point read as an invertible matrix. -/
@[simp]
theorem coe_geckPointsMulEquiv_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) A) :
    (t.geckPointsMulEquiv ht A q : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      GeneralLinear.pointsMulEquiv (t.geckDim ht)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)
          A q) := by
  simp only [geckPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply
    (t.geckDim ht) (t.geckDefiningIdeal ht) A q

/-- Including the ambient Hopf-algebra point underlying the inverse of
`TauCeti.DynkinType.geckPointsMulEquiv` recovers the point corresponding to the underlying
matrix. -/
@[simp]
theorem quotientPointsHom_geckPointsMulEquiv_symm (A : CommAlgCat.{v} ℤ)
    (g : t.geckPoints ht A) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht) A
        ((t.geckPointsMulEquiv ht A).symm g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) (t.geckDim ht)).symm
        (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  simp only [geckPointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  rw [GeneralLinear.quotientPointsHom_hopfIdealPointsSubgroupMulEquiv_symm,
    MulEquiv.subgroupCongr_apply]

/-- The pointwise identification with the quotient Hopf-algebra points is natural in the value
algebra. -/
@[simp]
theorem geckPointsMulEquiv_mapPoints {A B : CommAlgCat.{v} ℤ} (f : A ⟶ B)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) A) :
    t.geckPointsMulEquiv ht B
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht))
          f q) =
      t.geckPointsMap ht f.hom.toRingHom (t.geckPointsMulEquiv ht A q) := by
  apply Subtype.ext
  rw [coe_geckPointsMap]
  simp only [geckPointsMulEquiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply]
  exact (congrArg Subtype.val
      (GeneralLinear.hopfIdealPointsSubgroupMulEquiv_mapPoints
        (t.geckDim ht) (t.geckDefiningIdeal ht) f q)).trans
    (GeneralLinear.coe_mapHopfIdealPointsSubgroup (t.geckDim ht) (t.geckDefiningIdeal ht)
      f.hom _)

/-- **The quotient of the general-linear coordinate Hopf algebra by the Geck defining ideal
represents the functor of points of the pinned Geck carrier.** -/
def geckPointsFunctorNatIso :
    HopfAlgebra.pointsFunctor
        (R := ℤ) (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) ≅
      t.geckPointsFunctor ht :=
  NatIso.ofComponents (fun A => (t.geckPointsMulEquiv ht A).toGrpIso)
    (by
      intro A B f
      ext q
      exact t.geckPointsMulEquiv_mapPoints ht f q)

/-- After transport along `TauCeti.DynkinType.geckPointsFunctor_obj`, the forward component of
the representing natural isomorphism is the pointwise identification. -/
@[simp]
theorem geckPointsFunctorNatIso_hom_app_apply (A : CommAlgCat.{v} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ) (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) (t.geckDefiningIdeal ht)) A) :
    eqToHom (t.geckPointsFunctor_obj ht A) ((t.geckPointsFunctorNatIso ht).hom.app A q) =
      t.geckPointsMulEquiv ht A q :=
  (rfl)

/-- After transport back along `TauCeti.DynkinType.geckPointsFunctor_obj`, the inverse component
of the representing natural isomorphism is the inverse pointwise identification. -/
@[simp]
theorem geckPointsFunctorNatIso_inv_app_apply (A : CommAlgCat.{v} ℤ) (g : t.geckPoints ht A) :
    (t.geckPointsFunctorNatIso ht).inv.app A
        (eqToHom (t.geckPointsFunctor_obj ht A).symm g) =
      (t.geckPointsMulEquiv ht A).symm g :=
  (rfl)

end Functor

end

end TauCeti.DynkinType
