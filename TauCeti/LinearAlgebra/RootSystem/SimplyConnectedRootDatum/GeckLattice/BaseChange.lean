/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor

/-!
# Base change of the pinned Geck carrier

For a valid Dynkin type `t`, `DynkinType.geckGroupScheme` is the explicit integral affine group
scheme obtained by closing the numbered Geck root subgroups and the Geck weight torus inside a
general linear group. This file specializes the base-change construction for a general Kostant
toral closure to that pinned carrier.

For every commutative ring `A`, `geckBaseChangeDefiningIdeal` is an ideal in `O(GLₙ/A)` whose
quotient is canonically the scalar extension of the integral coordinate Hopf algebra. The
transported numbered root-subgroup maps and weight-torus map factor through that quotient. Thus
the explicit integral carrier and its pinned generators base-change together; none of the data is
chosen anew over `A`.

The defining ideal transported from `ℤ` is contained in the common kernel of the transported
generators. Equality is not asserted over an arbitrary, possibly non-flat, base: additional
equations can appear after specialization. Nor does this file assert that the carrier is
reductive or that the represented weight torus is maximal.

## Main declarations

* `TauCeti.DynkinType.geckBaseChangeDefiningIdeal`: the transported defining ideal in
  `O(GLₙ/A)`.
* `TauCeti.DynkinType.geckBaseChangeCoordinateIso`: its quotient is the scalar extension of the
  integral Geck coordinate Hopf algebra.
* `TauCeti.DynkinType.geckBaseChangePointsMulEquiv`: the points of that quotient in a commutative
  `A`-algebra are the matrix points of the integral carrier over that algebra.
* `TauCeti.DynkinType.geckRootSubgroupToBaseChangeCoordinateMap`: the transported numbered root
  subgroup factored through the specialized carrier.
* `TauCeti.DynkinType.geckWeightTorusToBaseChangeCoordinateMap`: the transported weight torus
  factored through the specialized carrier.
* `TauCeti.DynkinType.geckBaseChangeDefiningIdeal_le_commonKernel`: the transported carrier
  contains the subgroup generated after base change by those maps.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* B. Conrad, *Reductive Group Schemes*, §1.

This advances the base-change target in Layer 9 of the ReductiveGroups roadmap. The resulting
specialized pinned carrier is an input to milestone L0, "pinned ambient groups", of the
CFSGStatement roadmap.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType

universe v w

noncomputable section

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)
variable (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GLₙ/A)` obtained by transporting the defining ideal of the integral Geck
carrier along `ℤ → A`. -/
noncomputable def geckBaseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht)) :=
  TauCeti.UniversalEnvelopingAlgebra.kostantToralBaseChangePresentationIdeal
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

/-- Base-changing quotient maps commutes with transporting the defining ideal along an equality.
This isolates the dependent equality transport used by `geckBaseChangeCoordinateIso`. -/
private theorem baseChangeMap_mkQuotient_comp_eqToIso
    {I J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))}
    (hIJ : I = J) :
    CommHopfAlgCat.baseChangeMap (K := A)
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) I) ≫
        (eqToIso (congrArg
          (fun K => CommHopfAlgCat.baseChange (K := A)
            (CommHopfAlgCat.quotient
              (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) K)) hIJ)).hom =
      CommHopfAlgCat.baseChangeMap
        (CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) J) := by
  subst J
  simp

/-- Quotient maps commute with transporting their defining ideal along an equality. -/
private theorem mkQuotient_comp_eqToIso
    {I J : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))}
    (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht)) I ≫
        (eqToIso (congrArg
          (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht)))
          hIJ)).hom =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht)) J := by
  subst J
  simp

/-- The equality identifying the named Geck defining ideal with its generic Kostant spelling,
transported through quotient formation and scalar extension. -/
private noncomputable def geckIntegralCoordinateTransportIso :
    CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (kostantToralDefiningIdeal
            (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
            (t.geckCoordinateLattice ht).toAddSubgroup
            (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
            (t.isNilpotent_geckRepresentation_rootGenerator ht)
            (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht))) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckDefiningIdeal ht)) :=
  eqToIso (congrArg
    (fun K => CommHopfAlgCat.baseChange (K := A)
      (CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)) K))
    (t.geckDefiningIdeal_def ht).symm)

/-- The coordinate Hopf algebra cut out over `A` by the transported Geck defining ideal is
canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def geckBaseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckDefiningIdeal ht)) :=
  eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht)))
      (by rfl : t.geckBaseChangeDefiningIdeal ht A =
        kostantToralBaseChangePresentationIdeal
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (t.isNilpotent_geckRepresentation_rootGenerator ht)
          (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A)) ≪≫
    kostantToralBaseChangePresentationIso
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A ≪≫
    t.geckIntegralCoordinateTransportIso ht A

/-- The base-change coordinate isomorphism is compatible with the quotient presentation inside
`GLₙ`. -/
@[simp]
theorem mkQuotient_comp_geckBaseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht A) ≫
        (t.geckBaseChangeCoordinateIso ht A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (t.geckDim ht)).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
            (t.geckDefiningIdeal ht)) := by
  rw [geckBaseChangeCoordinateIso, Iso.trans_hom, Iso.trans_hom,
    ← Category.assoc, t.mkQuotient_comp_eqToIso ht A
      (by rfl : t.geckBaseChangeDefiningIdeal ht A =
        kostantToralBaseChangePresentationIdeal
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (t.isNilpotent_geckRepresentation_rootGenerator ht)
          (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A), ← Category.assoc,
    mkQuotient_comp_kostantToralBaseChangePresentationIso_hom, Category.assoc,
    geckIntegralCoordinateTransportIso,
    t.baseChangeMap_mkQuotient_comp_eqToIso ht A (t.geckDefiningIdeal_def ht).symm]

/-! ## Points of the base-changed carrier -/

/-- **The points of the base-changed Geck carrier are its matrix-valued points over the new
base.**

This is `CommHopfAlgCat.baseChangeIsoPointsMulEquiv`, read at the transport
`geckBaseChangeCoordinateIso`, followed by the represented-points equivalence of the integral
Geck carrier. Thus this definition uses the scalar extension constructed above rather than
choosing a new carrier over `A`.

The value algebra `B` is an arbitrary commutative `A`-algebra, so this identifies the points of
the specialized carrier at every value algebra rather than only at `A`; taking `B` to be
`CommAlgCat.of A A` reads its `A`-points. -/
noncomputable def geckBaseChangePointsMulEquiv (B : CommAlgCat.{w} A) :
    HopfAlgebra.points (R := A)
        (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht A)) B ≃*
      t.geckPoints ht B :=
  (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (t.geckBaseChangeCoordinateIso ht A) B).trans
    (t.geckPointsMulEquiv ht
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B))

/-- Under `geckBaseChangePointsMulEquiv`, a quotient point has the same ambient invertible matrix
as its composite with the quotient map over `A`. -/
@[simp]
theorem coe_geckBaseChangePointsMulEquiv_apply (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A)) B) :
    (t.geckBaseChangePointsMulEquiv ht A B q :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) =
      GeneralLinear.pointsMulEquiv (t.geckDim ht)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht A) B q) := by
  rw [geckBaseChangePointsMulEquiv, MulEquiv.trans_apply, t.coe_geckPointsMulEquiv_apply ht]
  exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
    (t.geckDim ht) (t.geckDefiningIdeal ht) (t.geckBaseChangeDefiningIdeal ht A)
    (t.geckBaseChangeCoordinateIso ht A)
    (t.mkQuotient_comp_geckBaseChangeCoordinateIso_hom ht A) B q

/-- Under the inverse of `geckBaseChangePointsMulEquiv`, the ambient point of the quotient point
attached to a Geck point is the one read off its invertible matrix. -/
@[simp]
theorem quotientPointsHom_geckBaseChangePointsMulEquiv_symm (B : CommAlgCat.{w} A)
    (g : t.geckPoints ht B) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A) B
        ((t.geckBaseChangePointsMulEquiv ht A B).symm g) =
      (GeneralLinear.pointsMulEquiv (R := A) (t.geckDim ht)).symm
        (g : Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) B) := by
  have h := t.coe_geckBaseChangePointsMulEquiv_apply ht A B
    ((t.geckBaseChangePointsMulEquiv ht A B).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- **The identification of the base-changed Geck carrier's points is natural in the value
algebra.** A morphism `χ : B ⟶ C` of value `A`-algebras acts on the specialized carrier's points
by `HopfAlgebra.mapPoints` and on the Geck points by `geckPointsMap` along the same morphism with
its scalars restricted to `ℤ`, and the equivalence intertwines the two. A consumer can therefore
use it functorially without unfolding its composite implementation. -/
@[simp]
theorem geckBaseChangePointsMulEquiv_mapPoints {B C : CommAlgCat.{w} A} (χ : B ⟶ C)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A)) B) :
    t.geckBaseChangePointsMulEquiv ht A C
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
            (t.geckBaseChangeDefiningIdeal ht A)) χ q) =
      t.geckPointsMap ht χ.hom.toRingHom
        (t.geckBaseChangePointsMulEquiv ht A B q) := by
  simp only [geckBaseChangePointsMulEquiv, MulEquiv.trans_apply]
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_mapPoints,
    t.geckPointsMulEquiv_mapPoints ht
      ((TauCeti.CommAlgCat.restrictScalars (algebraMap ℤ A)).map χ)]
  -- Restricting the scalars of `χ` to `ℤ` leaves its underlying ring homomorphism unchanged.
  rfl

/-- The integral `i`th root-subgroup coordinate map, with source expressed using the named Geck
defining ideal. -/
noncomputable def geckRootSubgroupIntegralCoordinateMap
    (i : Fin t.rank ⊕ Fin t.rank) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckDefiningIdeal ht) ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
      (t.geckDefiningIdeal_def ht))).hom ≫
    kostantRootSubgroupToralCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) i

/-- The base change to `A` of a numbered integral Geck root-subgroup coordinate map, transported
to the coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def geckRootSubgroupBaseChangeCoordinateMap
    (i : Fin t.rank ⊕ Fin t.rank) :
    GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupBaseChangePresentationCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) A i

/-- The base-changed `i`th Geck root-subgroup coordinate map factored through the transported
Geck carrier. -/
noncomputable def geckRootSubgroupToBaseChangeCoordinateMap
    (i : Fin t.rank ⊕ Fin t.rank) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A i

/-- The factored Geck root-subgroup map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckRootSubgroupToBaseChangeCoordinateMap
    (i : Fin t.rank ⊕ Fin t.rank) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht A) ≫
        t.geckRootSubgroupToBaseChangeCoordinateMap ht A i =
      t.geckRootSubgroupBaseChangeCoordinateMap ht A i := by
  unfold geckBaseChangeDefiningIdeal geckRootSubgroupToBaseChangeCoordinateMap
    geckRootSubgroupBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A i

/-- Under the Geck coordinate isomorphism, the factored `i`th root-subgroup map is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem geckBaseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap
    (i : Fin t.rank ⊕ Fin t.rank) :
    (t.geckBaseChangeCoordinateIso ht A).hom ≫
          CommHopfAlgCat.baseChangeMap (t.geckRootSubgroupIntegralCoordinateMap ht i) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      t.geckRootSubgroupToBaseChangeCoordinateMap ht A i := by
  let _ : Epi (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
      (t.geckBaseChangeDefiningIdeal ht A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient
    (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
    (t.geckBaseChangeDefiningIdeal ht A))).1
  rw [← Category.assoc, mkQuotient_comp_geckBaseChangeCoordinateIso_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckDefiningIdeal ht))),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    geckRootSubgroupIntegralCoordinateMap, ← Category.assoc
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckDefiningIdeal ht)),
    t.mkQuotient_comp_eqToIso ht ℤ (t.geckDefiningIdeal_def ht),
    mkQuotient_comp_kostantRootSubgroupToralCoordinateMap,
    mkQuotient_comp_geckRootSubgroupToBaseChangeCoordinateMap,
    geckRootSubgroupBaseChangeCoordinateMap]
  simpa only [_root_.CommHopfAlgCat.isoMk_hom] using
    (kostantRootSubgroupBaseChangePresentationCoordinateMap_def
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) A i).symm

/-- The base change to `A` of the integral Geck weight-torus coordinate map, transported to the
coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def geckWeightTorusBaseChangeCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin t.rank))).obj :=
  GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (t.geckWeightFin ht)

/-- The integral weight-torus coordinate map, with source expressed using the named Geck defining
ideal. -/
noncomputable def geckWeightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckDefiningIdeal ht) ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin t.rank))).obj :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht)))
      (t.geckDefiningIdeal_def ht))).hom ≫
    kostantWeightTorusToralCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)

/-- The base-changed Geck weight-torus coordinate map factored through the transported Geck
carrier. -/
noncomputable def geckWeightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
        (t.geckBaseChangeDefiningIdeal ht A) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin t.rank))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

/-- The factored Geck weight-torus map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_geckWeightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
          (t.geckBaseChangeDefiningIdeal ht A) ≫
        t.geckWeightTorusToBaseChangeCoordinateMap ht A =
      t.geckWeightTorusBaseChangeCoordinateMap ht A := by
  unfold geckBaseChangeDefiningIdeal geckWeightTorusToBaseChangeCoordinateMap
    geckWeightTorusBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

/-- Under the Geck coordinate isomorphism, the factored weight-torus map is the scalar extension
of its integral coordinate map. -/
@[simp]
theorem geckBaseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (t.geckBaseChangeCoordinateIso ht A).hom ≫
          CommHopfAlgCat.baseChangeMap (t.geckWeightTorusIntegralCoordinateMap ht) ≫
        (_root_.CommHopfAlgCat.ofHom
          (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
            (G := SplitTorus.characterGroup (Fin t.rank)))) =
      t.geckWeightTorusToBaseChangeCoordinateMap ht A := by
  let _ : Epi (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
      (t.geckBaseChangeDefiningIdeal ht A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient
    (GeneralLinear.coordinateHopfAlgebra A (t.geckDim ht))
    (t.geckBaseChangeDefiningIdeal ht A))).1
  rw [← Category.assoc, mkQuotient_comp_geckBaseChangeCoordinateIso_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
          (t.geckDefiningIdeal ht))),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    geckWeightTorusIntegralCoordinateMap, ← Category.assoc
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (t.geckDim ht))
        (t.geckDefiningIdeal ht)),
    t.mkQuotient_comp_eqToIso ht ℤ (t.geckDefiningIdeal_def ht),
    mkQuotient_comp_kostantWeightTorusToralCoordinateMap,
    mkQuotient_comp_geckWeightTorusToBaseChangeCoordinateMap,
    geckWeightTorusBaseChangeCoordinateMap]
  simpa only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.ObjectProperty.isoMk_hom,
    _root_.CommHopfAlgCat.isoMk_hom, CategoryTheory.ObjectProperty.ι_map,
    CategoryTheory.ObjectProperty.homMk_hom] using
    (GeneralLinear.weightTorusBaseChangeCoordinateMap_def ℤ A
      (t.geckWeightFin ht)).symm

/-- The closed subgroup of `GLₙ/A` generated by the transported numbered Geck root subgroups and
the transported weight torus lies in the base change of the integral Geck carrier.

The reverse inclusion is not asserted over an arbitrary base ring. -/
theorem geckBaseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin t.rank ⊕ Fin t.rank) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A
            (SplitTorus.characterGroup (Fin t.rank))).obj
    t.geckBaseChangeDefiningIdeal ht A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl i => t.geckRootSubgroupBaseChangeCoordinateMap ht A i
          | .inr _ => t.geckWeightTorusBaseChangeCoordinateMap ht A) := by
  dsimp only
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (i | _)
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_root_ker
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A i
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_torus_ker
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht) A

end

end TauCeti.DynkinType
