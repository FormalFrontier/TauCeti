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
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange`.
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

/-- Base-changing quotient maps commutes with transporting the defining ideal along an equality.
This isolates the dependent equality transport used by `TauCeti.SpStd.baseChangeCoordinateIso`. -/
private theorem baseChangeMap_mkQuotient_comp_eqToIso
    {I J : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))}
    (hIJ : I = J) :
    CommHopfAlgCat.baseChangeMap (K := A)
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) I) ≫
        (eqToIso (congrArg
          (fun K => CommHopfAlgCat.baseChange (K := A)
            (CommHopfAlgCat.quotient
              (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) K)) hIJ)).hom =
      CommHopfAlgCat.baseChangeMap
        (CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) J) := by
  subst J
  simp

/-- Quotient maps commute with transporting their defining ideal along an equality. -/
private theorem mkQuotient_comp_eqToIso
    {I J : HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))}
    (hIJ : I = J) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1))) I ≫
        (eqToIso (congrArg
          (CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))) hIJ)).hom =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1))) J := by
  subst J
  simp

/-- The equality identifying the named type-`C_(n+1)` defining ideal with its generic Kostant
spelling, transported through quotient formation and scalar extension. -/
private noncomputable def integralCoordinateTransportIso :
    CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (kostantToralDefiningIdeal (rootGenerator n) (cartanGenerator n) (rep n)
            (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
            (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n))) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (definingIdeal n)) :=
  eqToIso (congrArg
    (fun K => CommHopfAlgCat.baseChange (K := A)
      (CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) K))
    (definingIdeal_def n).symm)

/-- The coordinate Hopf algebra cut out over `A` by the transported type-`C_(n+1)` defining ideal
is canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
        (baseChangeDefiningIdeal n A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
          (definingIdeal n)) :=
  eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1))))
      (baseChangeDefiningIdeal_def n A)) ≪≫
    kostantToralBaseChangePresentationIso (rootGenerator n) (cartanGenerator n) (rep n)
      (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A ≪≫
    integralCoordinateTransportIso n A

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
  rw [baseChangeCoordinateIso, Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    mkQuotient_comp_eqToIso n A (baseChangeDefiningIdeal_def n A),
    ← Category.assoc, mkQuotient_comp_kostantToralBaseChangePresentationIso_hom, Category.assoc,
    integralCoordinateTransportIso,
    baseChangeMap_mkQuotient_comp_eqToIso n A (definingIdeal_def n).symm]

/-! ## The transported root subgroups -/

/-- The integral `k`th root-subgroup coordinate map, with source expressed using the named
type-`C_(n+1)` defining ideal. -/
noncomputable def rootSubgroupIntegralCoordinateMap (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
      (definingIdeal_def n))).hom ≫
    kostantRootSubgroupToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
      (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k

/-- The integral root-subgroup coordinate map is the generic Kostant one, read through the
identification of the two spellings of the defining ideal. -/
theorem rootSubgroupIntegralCoordinateMap_def (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroupIntegralCoordinateMap n k =
      (eqToIso (congrArg
          (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
          (definingIdeal_def n))).hom ≫
        kostantRootSubgroupToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
          (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
          (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) k := by
  rw [rootSubgroupIntegralCoordinateMap]

/-- The base change to `A` of a numbered integral root-subgroup coordinate map, transported to the
coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def rootSubgroupBaseChangeCoordinateMap (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupBaseChangePresentationCoordinateMap (rootGenerator n) (cartanGenerator n)
    (rep n) (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) A k

/-- The transported base-changed root-subgroup coordinate map is the generic Kostant one. -/
theorem rootSubgroupBaseChangeCoordinateMap_def (k : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootSubgroupBaseChangeCoordinateMap n A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap (rootGenerator n)
        (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
        (isNilpotent_rep_rootGenerator n) (latticeBasis n) A k := by
  rw [rootSubgroupBaseChangeCoordinateMap]

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
      rootSubgroupBaseChangeCoordinateMap n A k := by
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
    rootSubgroupBaseChangeCoordinateMap
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
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom =
      rootSubgroupToBaseChangeCoordinateMap n A k := by
  let _ : Epi (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
      (baseChangeDefiningIdeal n A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient
    (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
    (baseChangeDefiningIdeal n A))).1
  rw [← Category.assoc, mkQuotient_comp_baseChangeCoordinateIso_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n))),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    rootSubgroupIntegralCoordinateMap, ← Category.assoc
      (CommHopfAlgCat.mkQuotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)),
    mkQuotient_comp_eqToIso n ℤ (definingIdeal_def n),
    mkQuotient_comp_kostantRootSubgroupToralCoordinateMap,
    mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap,
    rootSubgroupBaseChangeCoordinateMap]
  exact (kostantRootSubgroupBaseChangePresentationCoordinateMap_def (rootGenerator n)
    (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) A k).symm

/-! ## The transported weight torus -/

/-- The base change to `A` of the integral weight-torus coordinate map, transported to the
coordinate Hopf algebras constructed directly over `A`. -/
noncomputable def weightTorusBaseChangeCoordinateMap :
    GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n)

/-- The transported weight-torus coordinate map is the general-linear one at the carrier's
weights. -/
theorem weightTorusBaseChangeCoordinateMap_def :
    weightTorusBaseChangeCoordinateMap n A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n) := by
  rw [weightTorusBaseChangeCoordinateMap]

/-- The integral weight-torus coordinate map, with source expressed using the named type-`C_(n+1)`
defining ideal. -/
noncomputable def weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1)))
        (definingIdeal n) ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin (n + 1)))).obj :=
  (eqToIso (congrArg
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
      (definingIdeal_def n))).hom ≫
    kostantWeightTorusToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
      (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n)

/-- The integral weight-torus coordinate map is the generic Kostant one, read through the
identification of the two spellings of the defining ideal. -/
theorem weightTorusIntegralCoordinateMap_def :
    weightTorusIntegralCoordinateMap n =
      (eqToIso (congrArg
          (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))))
          (definingIdeal_def n))).hom ≫
        kostantWeightTorusToralCoordinateMap (rootGenerator n) (cartanGenerator n) (rep n)
          (lattice n).toAddSubgroup (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
          (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) := by
  rw [weightTorusIntegralCoordinateMap]

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
      weightTorusBaseChangeCoordinateMap n A := by
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
    weightTorusBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
    (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

/-- Under the base-change coordinate isomorphism, the factored weight-torus map is the scalar
extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (baseChangeCoordinateIso n A).hom ≫
          CommHopfAlgCat.baseChangeMap (weightTorusIntegralCoordinateMap n) ≫
        (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso ℤ A
          (SplitTorus.characterGroup (Fin (n + 1)))).hom =
      weightTorusToBaseChangeCoordinateMap n A := by
  let _ : Epi (CommHopfAlgCat.mkQuotient
      (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
      (baseChangeDefiningIdeal n A)) :=
    ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.mkQuotient_surjective _ _)
  apply (cancel_epi (CommHopfAlgCat.mkQuotient
    (GeneralLinear.coordinateHopfAlgebra A ((n + 1) + (n + 1)))
    (baseChangeDefiningIdeal n A))).1
  rw [← Category.assoc, mkQuotient_comp_baseChangeCoordinateIso_hom,
    Category.assoc, ← Category.assoc
      (CommHopfAlgCat.baseChangeMap (K := A)
        (CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n))),
    ← (CommHopfAlgCat.baseChangeFunctor (K := A)).map_comp,
    weightTorusIntegralCoordinateMap, ← Category.assoc
      (CommHopfAlgCat.mkQuotient
        (GeneralLinear.coordinateHopfAlgebra ℤ ((n + 1) + (n + 1))) (definingIdeal n)),
    mkQuotient_comp_eqToIso n ℤ (definingIdeal_def n),
    mkQuotient_comp_kostantWeightTorusToralCoordinateMap,
    mkQuotient_comp_weightTorusToBaseChangeCoordinateMap,
    weightTorusBaseChangeCoordinateMap]
  exact (GeneralLinear.weightTorusBaseChangeCoordinateMap_def ℤ A (basisWeight n)).symm

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
          | .inl k => rootSubgroupBaseChangeCoordinateMap n A k
          | .inr _ => weightTorusBaseChangeCoordinateMap n A) := by
  dsimp only
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff]
  rintro (k | _)
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_root_ker (rootGenerator n)
      (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A k
  · exact kostantToralBaseChangePresentationIdeal_toIdeal_le_torus_ker (rootGenerator n)
      (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv)
      (isNilpotent_rep_rootGenerator n) (latticeBasis n) (basisWeight n) A

end

end TauCeti.SpStd
