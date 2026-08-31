/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.Scheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange

/-!
# Base change of the full-weight type-C carrier

For `n : ℕ`, `TauCeti.SpStd.groupScheme` is the explicit integral affine group scheme obtained by
closing the numbered standard type-`C_(n+1)` root subgroups and the standard weight torus inside
`GL_(2n+2)`. This file specializes the base-change construction for a general Kostant toral
closure to that pinned carrier.

For every commutative ring `A`, `TauCeti.SpStd.baseChangeDefiningIdeal` is an ideal in
`O(GL_(2n+2)/A)` whose quotient is canonically the scalar extension of the integral coordinate
Hopf algebra. The transported numbered root-subgroup maps and weight-torus map factor through
that quotient. Thus the explicit integral carrier and its pinned generators base-change together;
none of the data is chosen anew over `A`.

The defining ideal transported from `ℤ` is contained in the common kernel of the transported
generators. Equality is not asserted over an arbitrary, possibly non-flat, base: additional
equations can appear after specialization. Nor does this file assert that the carrier is
reductive, that the represented weight torus is maximal, or that the carrier is the separately
constructed symplectic group scheme.

## Main declarations

* `TauCeti.SpStd.baseChangeDefiningIdeal`: the transported defining ideal in `O(GL_(2n+2)/A)`.
* `TauCeti.SpStd.baseChangeCoordinateIso`: its quotient is the scalar extension of the integral
  carrier coordinate Hopf algebra.
* `TauCeti.SpStd.rootSubgroupToBaseChangeCoordinateMap`: the transported numbered root subgroup
  factored through the specialized carrier.
* `TauCeti.SpStd.weightTorusToBaseChangeCoordinateMap`: the transported weight torus factored
  through the specialized carrier.

## Main results

* `TauCeti.SpStd.mkQuotient_comp_baseChangeCoordinateIso_hom`: the coordinate isomorphism is
  compatible with the two quotient presentations.
* `TauCeti.SpStd.baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap` and
  `TauCeti.SpStd.baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap`: each factored
  generator is the scalar extension of its integral coordinate map.
* `TauCeti.SpStd.mkQuotient_comp_rootSubgroupIntegralCoordinateMap` and
  `TauCeti.SpStd.mkQuotient_comp_weightTorusIntegralCoordinateMap`: over `ℤ`, each integral
  generator map recovers the coordinate map it factors, and so is determined by it.
* `TauCeti.SpStd.hopfSpec_map_rootSubgroupIntegralCoordinateMap_op` and
  `TauCeti.SpStd.hopfSpec_map_weightTorusIntegralCoordinateMap_op`: those integral generator maps
  represent the carrier's existing pinning morphisms `TauCeti.SpStd.rootSubgroup` and
  `TauCeti.SpStd.weightTorus`.
* `TauCeti.SpStd.baseChangeDefiningIdeal_le_commonKernel`: the transported carrier contains the
  subgroup generated after base change by those maps.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* B. Conrad, *Reductive Group Schemes*, §1.

This advances the base-change target in Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`,
"Base change along `ℤ → k` for any commutative ring `k`, and the compatibility of the pinning with
it". The resulting specialized pinned carrier is an input to milestone L0, "pinned ambient
groups", of `TauCetiRoadmap/CFSGStatement/README.md`, which reads the carrier of a finite group of
Lie type off the points of a pinned Chevalley--Demazure group over an algebraic closure. The
declaration structure follows the sibling specialization for the pinned Geck carrier in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange`. Every
declaration below is the corresponding generic Kostant declaration at this carrier's data; the
transport reading the generic base-change presentation through a named integral defining ideal is
the `...OfEq` family of
`Kostant/RootSubgroup/Scheme/ToralClosure/GeneralLinearBaseChange.lean`, so nothing of that
calculation is repeated here.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.SpStd

universe v

open LieAlgebra.Symplectic

noncomputable section

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (n : ℕ)
variable (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GL_(2n+2)/A)` obtained by transporting the defining ideal of the integral
full-weight type-`C_(n+1)` carrier along `ℤ → A`. -/
noncomputable def baseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1))) :=
  kostantToralBaseChangePresentationIdeal (rootGenerator n) (cartanGenerator n) (rep n)
    (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- The transported defining ideal is the one supplied by the generic Kostant toral-closure base
change. The module system does not expose a definition's body outside its own module, so this is
the form in which downstream files rewrite with the definition. -/
theorem baseChangeDefiningIdeal_def :
    baseChangeDefiningIdeal n A =
      kostantToralBaseChangePresentationIdeal (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A := by
  rw [baseChangeDefiningIdeal]

/-- Membership in the transported defining ideal is membership of the corresponding element in
the base change of the named integral defining ideal. -/
@[simp]
theorem mem_baseChangeDefiningIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1))} :
    x ∈ baseChangeDefiningIdeal n A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A
        ((n + 1) + (n + 1))).inv.hom x ∈
        CommHopfAlgCat.baseChangeHopfIdeal (K := A) (definingIdeal n) := by
  rw [baseChangeDefiningIdeal_def, mem_kostantToralBaseChangePresentationIdeal_iff,
    kostantToralBaseChangeIdeal_def, ← definingIdeal_def]

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the transported defining ideal. -/
theorem map_tmul_mem_baseChangeDefiningIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))}
    (hy : y ∈ definingIdeal n) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A
      ((n + 1) + (n + 1))).hom.hom (s ⊗ₜ[ℤ] y) ∈ baseChangeDefiningIdeal n A := by
  rw [baseChangeDefiningIdeal_def]
  exact map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A s
    (definingIdeal_def n ▸ hy)

/-- The coordinate Hopf algebra cut out over `A` by the transported type-`C_(n+1)` defining ideal
is canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
        (baseChangeDefiningIdeal n A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (definingIdeal n)) :=
  kostantToralBaseChangePresentationIsoOfEq (rootGenerator n) (cartanGenerator n) (rep n)
    (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A (definingIdeal_def n)

/-- The base-change coordinate isomorphism is compatible with the quotient presentation inside
`GL_(2n+2)`. -/
@[simp]
theorem mkQuotient_comp_baseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
          (baseChangeDefiningIdeal n A) ≫
        (baseChangeCoordinateIso n A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A ((n + 1) + (n + 1))).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)) := by
  rw [baseChangeCoordinateIso]
  exact mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A (definingIdeal_def n)

/-! ## The transported root subgroups -/

/-- The integral `k`th root-subgroup coordinate map, with source expressed using the named
type-`C_(n+1)` defining ideal. -/
noncomputable def rootSubgroupIntegralCoordinateMap (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  kostantRootSubgroupToralCoordinateMapOfEq (rootGenerator n) (cartanGenerator n) (rep n)
    (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n) k

/-- The integral root-subgroup coordinate map is the generic Kostant one, read through the named
type-`C_(n+1)` defining ideal. -/
theorem rootSubgroupIntegralCoordinateMap_def (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroupIntegralCoordinateMap n k =
      kostantRootSubgroupToralCoordinateMapOfEq (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)
        (definingIdeal_def n) k := by
  rw [rootSubgroupIntegralCoordinateMap]

/-- The integral factored root-subgroup map recovers the represented `k`th root-subgroup
coordinate map inside `GL_(2n+2)`, and so determines it. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupIntegralCoordinateMap (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (definingIdeal n) ≫
        rootSubgroupIntegralCoordinateMap n k =
      kostantRootSubgroupCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
        (isNilpotent_rep_rootGenerator n k) (latticeBasis n) := by
  rw [rootSubgroupIntegralCoordinateMap]
  exact mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n) k

/-- The integral factored root-subgroup coordinate map represents the carrier's `k`th numbered
root subgroup: its spectrum is `TauCeti.SpStd.rootSubgroup`, read through the quotient-spectrum
presentation of the carrier. -/
-- Not a `simp` lemma: `simp` rewrites `hopfSpec` to `algSpec.mapGrp` composed with the
-- Hopf-algebra/cogroup equivalence, so no equation whose sides mention `hopfSpec.map` has a
-- left-hand side in `simp` normal form.
theorem hopfSpec_map_rootSubgroupIntegralCoordinateMap_op (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (rootSubgroupIntegralCoordinateMap n k).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        rootSubgroup n k ≫ eqToHom (groupScheme_def n) := by
  rw [rootSubgroupIntegralCoordinateMap, rootSubgroup_def]
  exact hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n) k

/-- The base-changed `k`th root-subgroup coordinate map factored through the transported
type-`C_(n+1)` carrier. -/
noncomputable def rootSubgroupToBaseChangeCoordinateMap (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
        (baseChangeDefiningIdeal n A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A k

/-- The factored root-subgroup map recovers its ambient transported coordinate map.

Since `CommHopfAlgCat.mkQuotient` is an epimorphism this determines the factored map, which is why
no separate defining equation for it is stated: its source is spelled with
`TauCeti.SpStd.baseChangeDefiningIdeal`, so such an equation would need an `eqToHom` transport. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
          (baseChangeDefiningIdeal n A) ≫
        rootSubgroupToBaseChangeCoordinateMap n A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) A k := by
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A k

/-- Under the base-change coordinate isomorphism, the factored `k`th root-subgroup map is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap
    (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    (baseChangeCoordinateIso n A).hom ≫
          CommHopfAlgCat.baseChangeMap (rootSubgroupIntegralCoordinateMap n k) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      rootSubgroupToBaseChangeCoordinateMap n A k := by
  rw [baseChangeCoordinateIso, rootSubgroupIntegralCoordinateMap,
    rootSubgroupToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_rootSubgroupBaseChangeMap
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A (definingIdeal_def n) k

/-! ## The transported weight torus -/

/-- The integral weight-torus coordinate map, with source expressed using the named type-`C_(n+1)`
defining ideal. -/
noncomputable def weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  kostantWeightTorusToralCoordinateMapOfEq (rootGenerator n) (cartanGenerator n) (rep n)
    (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n)

/-- The integral weight-torus coordinate map is the generic Kostant one, read through the named
type-`C_(n+1)` defining ideal. -/
theorem weightTorusIntegralCoordinateMap_def :
    weightTorusIntegralCoordinateMap n =
      kostantWeightTorusToralCoordinateMapOfEq (rootGenerator n) (cartanGenerator n) (rep n)
        (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)
        (definingIdeal_def n) := by
  rw [weightTorusIntegralCoordinateMap]

/-- The integral factored weight-torus map recovers the weight-torus coordinate map inside
`GL_(2n+2)`, and so determines it. -/
@[simp]
theorem mkQuotient_comp_weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (definingIdeal n) ≫
        weightTorusIntegralCoordinateMap n =
      GeneralLinear.weightTorusCoordinateMap (basisWeight n) := by
  rw [weightTorusIntegralCoordinateMap]
  exact mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n)

/-- The integral factored weight-torus coordinate map represents the carrier's weight torus: its
spectrum is `TauCeti.SpStd.weightTorus`, read through the quotient-spectrum presentation of the
carrier. -/
theorem hopfSpec_map_weightTorusIntegralCoordinateMap_op :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (weightTorusIntegralCoordinateMap n).op =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ
          (SplitTorus.characterGroup (Fin (n + 1)))).symm ≫
        weightTorus n ≫ eqToHom (groupScheme_def n) := by
  rw [weightTorusIntegralCoordinateMap, weightTorus_def]
  exact hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) (definingIdeal_def n)

/-- The base-changed weight-torus coordinate map factored through the transported type-`C_(n+1)`
carrier. -/
noncomputable def weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
        (baseChangeDefiningIdeal n A) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- The factored weight-torus map recovers its ambient transported coordinate map, and so
determines it. -/
@[simp]
theorem mkQuotient_comp_weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
          (baseChangeDefiningIdeal n A) ≫
        weightTorusToBaseChangeCoordinateMap n A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n) := by
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- Under the base-change coordinate isomorphism, the factored weight-torus map is the scalar
extension of its integral coordinate map. -/
-- The bialgebra equivalence is coerced by name: writing `↑` leaves the source of the coercion a
-- metavariable, and the coordinate ring of the character group only matches the monoid algebra
-- the equivalence is stated for after unfolding, which the coercion elaborator does not do.
@[simp]
theorem baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (baseChangeCoordinateIso n A).hom ≫
          CommHopfAlgCat.baseChangeMap (weightTorusIntegralCoordinateMap n) ≫
        (_root_.CommHopfAlgCat.ofHom
          (BialgHomClass.toBialgHom
            (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
              (G := SplitTorus.characterGroup (Fin (n + 1)))))) =
      weightTorusToBaseChangeCoordinateMap n A := by
  rw [baseChangeCoordinateIso, weightTorusIntegralCoordinateMap,
    weightTorusToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_weightTorusBaseChangeMap
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A (definingIdeal_def n)

/-- The closed subgroup of `GL_(2n+2)/A` generated by the transported numbered root subgroups and
the transported weight torus lies in the base change of the integral type-`C_(n+1)` carrier.

The reverse inclusion is not asserted over an arbitrary base ring. -/
theorem baseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin (n + 1) ⊕ Fin (n + 1)) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A
            (SplitTorus.characterGroup (Fin (n + 1)))).obj
    baseChangeDefiningIdeal n A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl k => kostantRootSubgroupBaseChangePresentationCoordinateMap (rootGenerator n)
              (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
              (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
              (isNilpotent_rep_rootGenerator n) (latticeBasis n) A k
          | .inr _ => GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n)) := by
  have h := kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A
  -- The generic containment indexes its generators by a `match` of its own, and neither that
  -- matcher nor `CommHopfAlgCat.commonKernelHopfIdeal` is exposed for unfolding, so the two
  -- families are compared branchwise on a constructor rather than by a single `exact`.
  dsimp only at h ⊢
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff] at h ⊢
  rintro (k | _)
  · exact h (.inl k)
  · exact h (.inr ())

end

end TauCeti.SpStd
