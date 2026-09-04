/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange

/-!
# Base change of the full-weight type-E6 minuscule carrier

`TauCeti.E6Minuscule.groupScheme` is the explicit integral affine group scheme obtained by
closing the twelve numbered type-`E₆` root subgroups and the minuscule weight torus inside
`GL₂₇`. This file specializes the base-change construction for a general Kostant toral closure
to that pinned carrier.

For every commutative ring `A`, `TauCeti.E6Minuscule.baseChangeDefiningIdeal` is an ideal in
`O(GL₂₇/A)` whose quotient is canonically the scalar extension of the integral coordinate Hopf
algebra. The transported numbered root-subgroup maps and weight-torus map factor through that
quotient. Thus the integral carrier and its pinned generators base-change together; none of the
data is chosen anew over `A`.

The defining ideal transported from `ℤ` is contained in the common kernel of the transported
generators. Equality is not asserted over an arbitrary, possibly non-flat, base: additional
equations can appear after specialization. Nor does this file assert that the carrier is
reductive, that its torus is maximal, or that its root datum has been identified.

## Main declarations

* `TauCeti.E6Minuscule.baseChangeDefiningIdeal`: the transported defining ideal in
  `O(GL₂₇/A)`.
* `TauCeti.E6Minuscule.baseChangeCoordinateIso`: its quotient is the scalar extension of the
  integral carrier coordinate Hopf algebra.
* `TauCeti.E6Minuscule.rootSubgroupToBaseChangeCoordinateMap`: the transported numbered root
  subgroup factored through the specialized carrier.
* `TauCeti.E6Minuscule.weightTorusToBaseChangeCoordinateMap`: the transported weight torus
  factored through the specialized carrier.

## Main results

* `TauCeti.E6Minuscule.mkQuotient_comp_baseChangeCoordinateIso_hom`: the coordinate
  isomorphism is compatible with the quotient presentations.
* `TauCeti.E6Minuscule.baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap` and
  `TauCeti.E6Minuscule.baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap`: the pinned
  generators are the scalar extensions of their integral coordinate maps.
* `TauCeti.E6Minuscule.hopfSpec_map_rootSubgroupIntegralCoordinateMap_op` and
  `TauCeti.E6Minuscule.hopfSpec_map_weightTorusIntegralCoordinateMap_op`: the integral
  coordinate maps represent the existing pinned morphisms.
* `TauCeti.E6Minuscule.baseChangeDefiningIdeal_le_commonKernel`: the transported carrier
  contains the subgroup generated after base change by the transported maps.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* B. Conrad, *Reductive Group Schemes*, §1.

This advances the base-change target in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`.
The resulting specialized pinned carrier is an input to milestone L0, “pinned ambient groups”,
of `TauCetiRoadmap/CFSGStatement/README.md`.

The declaration structure specializes the formal template in
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.BaseChange`. Every construction below uses the
generic Kostant base-change API from
`Kostant/RootSubgroup/Scheme/ToralClosure/GeneralLinearBaseChange.lean`; in particular, none of
the coordinate-ring calculation is repeated here.
-/

public section

open CategoryTheory
open TauCeti.DynkinType
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix TensorProduct

namespace TauCeti.E6Minuscule

universe v

noncomputable section

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GL₂₇/A)` obtained by transporting the defining ideal of the integral
full-weight type-`E₆` minuscule carrier along `ℤ → A`. -/
noncomputable def baseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A 27) :=
  kostantToralBaseChangePresentationIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A

/-- Membership in the transported defining ideal is membership of the corresponding element in
the base change of the named integral defining ideal. -/
@[simp]
theorem mem_baseChangeDefiningIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A 27} :
    x ∈ baseChangeDefiningIdeal A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 27).inv.hom x ∈
        CommHopfAlgCat.baseChangeHopfIdeal (K := A) definingIdeal := by
  rw [baseChangeDefiningIdeal, mem_kostantToralBaseChangePresentationIdeal_iff,
    kostantToralBaseChangeIdeal_def, ← definingIdeal_def]

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the transported defining ideal. -/
theorem map_tmul_mem_baseChangeDefiningIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ 27} (hy : y ∈ definingIdeal) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 27).hom.hom
        (s ⊗ₜ[ℤ] y) ∈ baseChangeDefiningIdeal A := by
  rw [baseChangeDefiningIdeal]
  exact map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A s (definingIdeal_def ▸ hy)

/-- The coordinate Hopf algebra cut out over `A` by the transported type-`E₆` defining ideal is
canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 27)
        (baseChangeDefiningIdeal A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal) :=
  kostantToralBaseChangePresentationIsoOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A definingIdeal_def

/-- The base-change coordinate isomorphism is compatible with the quotient presentation inside
`GL₂₇`. -/
@[simp]
theorem mkQuotient_comp_baseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 27)
          (baseChangeDefiningIdeal A) ≫
        (baseChangeCoordinateIso A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A 27).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal) := by
  rw [baseChangeCoordinateIso]
  exact mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A definingIdeal_def

/-! ## The transported root subgroups -/

/-- The integral `k`th root-subgroup coordinate map, with source expressed using the named
type-`E₆` defining ideal. -/
noncomputable def rootSubgroupIntegralCoordinateMap (k : Fin 6 ⊕ Fin 6) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def k

/-- The integral factored root-subgroup map recovers the represented `k`th root-subgroup
coordinate map inside `GL₂₇`. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupIntegralCoordinateMap (k : Fin 6 ⊕ Fin 6) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal ≫
        rootSubgroupIntegralCoordinateMap k =
      kostantRootSubgroupCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k) latticeBasis := by
  rw [rootSubgroupIntegralCoordinateMap]
  exact mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def k

/-- The integral factored root-subgroup coordinate map represents the carrier's `k`th numbered
root subgroup. -/
theorem hopfSpec_map_rootSubgroupIntegralCoordinateMap_op (k : Fin 6 ⊕ Fin 6) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (rootSubgroupIntegralCoordinateMap k).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        rootSubgroup k ≫ eqToHom groupScheme_def := by
  rw [rootSubgroupIntegralCoordinateMap, rootSubgroup_def]
  exact hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def k

/-- The base-changed `k`th root-subgroup coordinate map factored through the transported
type-`E₆` carrier. -/
noncomputable def rootSubgroupToBaseChangeCoordinateMap (k : Fin 6 ⊕ Fin 6) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 27)
        (baseChangeDefiningIdeal A) ⟶ AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A k

/-- The factored root-subgroup map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap (k : Fin 6 ⊕ Fin 6) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 27)
          (baseChangeDefiningIdeal A) ≫
        rootSubgroupToBaseChangeCoordinateMap A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
        (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
        rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis A k := by
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A k

/-- Under the base-change coordinate isomorphism, the factored `k`th root-subgroup map is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap (k : Fin 6 ⊕ Fin 6) :
    (baseChangeCoordinateIso A).hom ≫
          CommHopfAlgCat.baseChangeMap (rootSubgroupIntegralCoordinateMap k) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      rootSubgroupToBaseChangeCoordinateMap A k := by
  rw [baseChangeCoordinateIso, rootSubgroupIntegralCoordinateMap,
    rootSubgroupToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_rootSubgroupBaseChangeMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A definingIdeal_def k

/-! ## The transported weight torus -/

/-- The integral weight-torus coordinate map, with source expressed using the named type-`E₆`
defining ideal. -/
noncomputable def weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin 6))).obj :=
  kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def

/-- The integral factored weight-torus map recovers the represented weight-torus coordinate map
inside `GL₂₇`. -/
@[simp]
theorem mkQuotient_comp_weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal ≫
        weightTorusIntegralCoordinateMap =
      GeneralLinear.weightTorusCoordinateMap e6MinusculeWeight := by
  rw [weightTorusIntegralCoordinateMap]
  exact mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def

/-- The integral factored weight-torus coordinate map represents the carrier's weight torus. -/
theorem hopfSpec_map_weightTorusIntegralCoordinateMap_op :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        weightTorusIntegralCoordinateMap.op =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ
          (SplitTorus.characterGroup (Fin 6))).symm ≫
        weightTorus ≫ eqToHom groupScheme_def := by
  rw [weightTorusIntegralCoordinateMap, weightTorus_def]
  exact hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight definingIdeal_def

/-- The base-changed weight-torus coordinate map factored through the transported type-`E₆`
carrier. -/
noncomputable def weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A 27)
        (baseChangeDefiningIdeal A) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin 6))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A

/-- The factored weight-torus map recovers its ambient transported coordinate map. -/
@[simp]
theorem mkQuotient_comp_weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A 27)
          (baseChangeDefiningIdeal A) ≫
        weightTorusToBaseChangeCoordinateMap A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A e6MinusculeWeight := by
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A

/-- Under the base-change coordinate isomorphism, the factored weight-torus map is the scalar
extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (baseChangeCoordinateIso A).hom ≫
          CommHopfAlgCat.baseChangeMap weightTorusIntegralCoordinateMap ≫
        (_root_.CommHopfAlgCat.ofHom
          (BialgHomClass.toBialgHom
            (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
              (G := SplitTorus.characterGroup (Fin 6))))) =
      weightTorusToBaseChangeCoordinateMap A := by
  rw [baseChangeCoordinateIso, weightTorusIntegralCoordinateMap,
    weightTorusToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_weightTorusBaseChangeMap
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A definingIdeal_def

/-- The closed subgroup of `GL₂₇/A` generated by the transported numbered root subgroups and
weight torus lies in the base change of the integral type-`E₆` carrier.

The reverse inclusion is not asserted over an arbitrary base ring. -/
theorem baseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin 6 ⊕ Fin 6) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A
            (SplitTorus.characterGroup (Fin 6))).obj
    baseChangeDefiningIdeal A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl k => kostantRootSubgroupBaseChangePresentationCoordinateMap
              (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
              (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
              rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis A k
          | .inr _ =>
              GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A e6MinusculeWeight) := by
  have h := kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
    (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
    rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator latticeBasis
    e6MinusculeWeight A
  -- The generic containment indexes its generators by a `match` of its own, and neither that
  -- matcher nor `commonKernelHopfIdeal` is exposed, so compare the two families branchwise.
  dsimp only at h ⊢
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff] at h ⊢
  rintro (k | _)
  · exact h (.inl k)
  · exact h (.inr ())

end

end TauCeti.E6Minuscule
