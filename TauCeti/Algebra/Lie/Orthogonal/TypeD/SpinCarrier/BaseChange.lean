/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.BaseChange
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.GeneralLinearBaseChange

/-!
# Base change of the full-weight type-D spin carrier

For `4 ≤ n`, `TauCeti.TypeDSpinCarrier.groupScheme` is the explicit integral affine group
scheme obtained by closing the numbered type-`Dₙ` root subgroups and the full spin weight torus
inside `GL_(2^n)`. This file specializes the general base-change construction for Kostant toral
closures to that carrier.

For every commutative ring `A`, `TauCeti.TypeDSpinCarrier.baseChangeDefiningIdeal` is an ideal in
`O(GL_(2^n)/A)` whose quotient is canonically the scalar extension of the integral coordinate
Hopf algebra. The transported numbered root-subgroup maps and weight-torus map factor through
that quotient. Thus the explicit integral carrier and its distinguished root-subgroup and torus
maps base-change together; none of the data is chosen anew over `A`.

The defining ideal transported from `ℤ` is contained in the common kernel of the transported
generators. Equality is not asserted over an arbitrary, possibly non-flat, base: additional
equations can appear after specialization. Nor does this file assert that the carrier is
reductive, that the represented weight torus is maximal, or that its root datum is the simply
connected type-`Dₙ` datum.

## Main declarations

* `TauCeti.TypeDSpinCarrier.baseChangeDefiningIdeal`: the transported defining ideal in the
  coordinate ring of `GL_(2^n)/A`.
* `TauCeti.TypeDSpinCarrier.baseChangeCoordinateIso`: the quotient is the scalar extension of
  the integral carrier coordinate Hopf algebra.
* `TauCeti.TypeDSpinCarrier.baseChangePointsMulEquiv`: the points of that quotient in a
  commutative `A`-algebra are the matrix points of the integral carrier over that algebra.
* `TauCeti.TypeDSpinCarrier.rootSubgroupToBaseChangeCoordinateMap`: the transported numbered
  root subgroup factored through the specialized carrier.
* `TauCeti.TypeDSpinCarrier.weightTorusToBaseChangeCoordinateMap`: the transported weight torus
  factored through the specialized carrier.

## Main results

* `TauCeti.TypeDSpinCarrier.mkQuotient_comp_baseChangeCoordinateIso_hom`: the coordinate
  isomorphism is compatible with the two quotient presentations.
* `TauCeti.TypeDSpinCarrier.baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap` and
  `TauCeti.TypeDSpinCarrier.baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap`: each
  factored generator is the scalar extension of its integral coordinate map.
* `TauCeti.TypeDSpinCarrier.mkQuotient_comp_rootSubgroupIntegralCoordinateMap` and
  `TauCeti.TypeDSpinCarrier.mkQuotient_comp_weightTorusIntegralCoordinateMap`: over `ℤ`, each
  integral generator map recovers the coordinate map it factors.
* `TauCeti.TypeDSpinCarrier.hopfSpec_map_rootSubgroupIntegralCoordinateMap_op` and
  `TauCeti.TypeDSpinCarrier.hopfSpec_map_weightTorusIntegralCoordinateMap_op`: those integral
  maps represent the carrier's existing root-subgroup and weight-torus morphisms.
* `baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap` and
  `baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap`:
  the transported coordinate maps induce the named root-subgroup and weight-torus points.
* `TauCeti.TypeDSpinCarrier.baseChangeDefiningIdeal_le_commonKernel`: the transported carrier
  contains the subgroup generated after base change by those maps.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* B. Conrad, *Reductive Group Schemes*, §1.

This supplies a prerequisite for the base-change target in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, "Base change along `ℤ → k` for any commutative ring
`k`, and the compatibility of the pinning with it": it transports the underlying type-`D`
carrier and its distinguished generator maps. It does not provide the pinning compatibility or
a specialized pinned carrier. Those require the subsequent proofs that this carrier is
reductive, that its torus is maximal with the simply connected type-`Dₙ` root datum, and that the
maps supply a pinning. This file depends only on the already-constructed integral carrier and the
generic scalar-extension machinery; those subsequent proofs can consume the declarations here as
their underlying scalar-extension data. The declaration structure follows the sibling
specialization for the pinned Geck carrier in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.BaseChange`. The ideal and
generator-map declarations below specialize the corresponding generic Kostant declarations at
this carrier's data; the points equivalences instead use the general Hopf-algebra and
general-linear points APIs. The transport reading the generic base-change presentation through a
named integral defining ideal is the `...OfEq` family of
`Kostant/RootSubgroup/Scheme/ToralClosure/GeneralLinearBaseChange.lean`, so nothing of that
calculation is repeated here.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeDSpinCarrier

universe v w

noncomputable section

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n)
variable (A : Type v) [CommRing A]

/-- The Hopf ideal in `O(GL_(2^n)/A)` obtained by transporting the defining ideal of the integral
full-weight type-`Dₙ` carrier along `ℤ → A`. -/
noncomputable def baseChangeDefiningIdeal :
    HopfIdeal A (GeneralLinear.coordinateHopfAlgebra A (dimension n)) :=
  kostantToralBaseChangePresentationIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
    (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A

/-- The transported defining ideal is the one supplied by the generic Kostant toral-closure base
change. -/
theorem baseChangeDefiningIdeal_def :
    baseChangeDefiningIdeal n hn A =
      kostantToralBaseChangePresentationIdeal
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
        (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A := by
  rw [baseChangeDefiningIdeal]

/-- Membership in the transported defining ideal is membership of the corresponding element in
the base change of the named integral defining ideal. -/
@[simp]
theorem mem_baseChangeDefiningIdeal_iff
    {x : GeneralLinear.coordinateHopfAlgebra A (dimension n)} :
    x ∈ baseChangeDefiningIdeal n hn A ↔
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A
        (dimension n)).inv.hom x ∈
        CommHopfAlgCat.baseChangeHopfIdeal (K := A) (definingIdeal n hn) := by
  rw [baseChangeDefiningIdeal_def, mem_kostantToralBaseChangePresentationIdeal_iff,
    kostantToralBaseChangeIdeal_def, ← definingIdeal_def]

/-- Transporting a pure tensor of a scalar and an integral defining equation produces an equation
in the transported defining ideal. -/
theorem map_tmul_mem_baseChangeDefiningIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)}
    (hy : y ∈ definingIdeal n hn) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A
      (dimension n)).hom.hom (s ⊗ₜ[ℤ] y) ∈ baseChangeDefiningIdeal n hn A := by
  rw [baseChangeDefiningIdeal_def]
  exact map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A s
    (definingIdeal_def n hn ▸ hy)

/-- The coordinate Hopf algebra cut out over `A` by the transported type-`Dₙ` defining ideal
is canonically the scalar extension of the integral coordinate Hopf algebra. -/
noncomputable def baseChangeCoordinateIso :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
          (definingIdeal n hn)) :=
  kostantToralBaseChangePresentationIsoOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
    (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A (definingIdeal_def n hn)

/-- The base-change coordinate isomorphism is compatible with the quotient presentation inside
`GL_(2^n)`. -/
@[simp]
theorem mkQuotient_comp_baseChangeCoordinateIso_hom :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A) ≫
        (baseChangeCoordinateIso n hn A).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A (dimension n)).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn)) := by
  rw [baseChangeCoordinateIso]
  exact mkQuotient_comp_kostantToralBaseChangePresentationIsoOfEq_hom
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A (definingIdeal_def n hn)

/-! ## Points of the base-changed carrier -/

/-- The points of the base-changed type-`Dₙ` carrier over a commutative `A`-algebra are its
matrix-valued carrier points over that algebra. -/
noncomputable def baseChangePointsMulEquiv (B : CommAlgCat.{w} A) :
    HopfAlgebra.points (R := A)
        (H := CommHopfAlgCat.quotient
          (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A)) B ≃*
      points n hn B :=
  (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso n hn A) B).trans
    (pointsMulEquiv n hn
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B))

/-- The base-change points equivalence preserves the ambient invertible matrix. -/
@[simp]
theorem coe_baseChangePointsMulEquiv_apply (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A)) B) :
    (baseChangePointsMulEquiv n hn A B q :
        Matrix.GeneralLinearGroup (Fin (dimension n)) B) =
      GeneralLinear.pointsMulEquiv (dimension n)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A) B q) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, coe_pointsMulEquiv_apply]
  exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
    (dimension n) (definingIdeal n hn) (baseChangeDefiningIdeal n hn A)
    (baseChangeCoordinateIso n hn A) (mkQuotient_comp_baseChangeCoordinateIso_hom n hn A) B q

/-- The quotient point underlying the inverse base-change equivalence is the point determined by
the ambient invertible matrix. -/
@[simp]
theorem quotientPointsHom_baseChangePointsMulEquiv_symm (B : CommAlgCat.{w} A)
    (g : points n hn B) :
    CommHopfAlgCat.quotientPointsHom
        (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A) B
        ((baseChangePointsMulEquiv n hn A B).symm g) =
      (GeneralLinear.pointsMulEquiv (R := A) (dimension n)).symm
        (g : Matrix.GeneralLinearGroup (Fin (dimension n)) B) := by
  have h := coe_baseChangePointsMulEquiv_apply n hn A B
    ((baseChangePointsMulEquiv n hn A B).symm g)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

/-- The identification of the base-changed carrier's points is natural in the value algebra. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPoints {B C : CommAlgCat.{w} A} (f : B ⟶ C)
    (q : HopfAlgebra.points (R := A)
      (H := CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A)) B) :
    baseChangePointsMulEquiv n hn A C
        (HopfAlgebra.mapPoints
          (H := CommHopfAlgCat.quotient
            (GeneralLinear.coordinateHopfAlgebra A (dimension n))
            (baseChangeDefiningIdeal n hn A)) f q) =
      pointsMap n hn f.hom.toRingHom (baseChangePointsMulEquiv n hn A B q) := by
  simp only [baseChangePointsMulEquiv, MulEquiv.trans_apply]
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_mapPoints,
    pointsMulEquiv_mapPoints n hn
      ((TauCeti.CommAlgCat.restrictScalars (algebraMap ℤ A)).map f)]
  have hring :
      ((TauCeti.CommAlgCat.restrictScalars (algebraMap ℤ A)).map f).hom.toRingHom =
        f.hom.toRingHom := by
    rw [TauCeti.CommAlgCat.restrictScalars_map,
      TauCeti.CommAlgCat.restrictScalarsMap_hom]
    exact RingHom.ext fun x ↦ AlgHom.restrictScalars_apply ℤ f.hom x
  rw [hring]

/-- Point transport commutes with a coordinate map presented by compatible scalar-extension
isomorphisms. This is the common categorical argument behind the root-subgroup and weight-torus
compatibility proofs below; the remaining work in each proof identifies its generator parameter. -/
private theorem baseChangeIsoPointsMulEquiv_mapPointsFunctor
    {K : CommHopfAlgCat ℤ} {KA : CommHopfAlgCat.{v} A}
    (gK : CommHopfAlgCat.baseChange (K := A) K ⟶ KA)
    (f : CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) ⟶ K)
    (fA : CommHopfAlgCat.quotient
        (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A) ⟶ KA)
    (hcompat : (baseChangeCoordinateIso n hn A).hom ≫
      CommHopfAlgCat.baseChangeMap f ≫ gK = fA)
    (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points (R := A) (H := KA) B) :
    CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso n hn A) B
        (WithConv.toConv (q.ofConv.comp fA.hom.toAlgHom)) =
      WithConv.toConv
        ((CommHopfAlgCat.baseChangePointsMulEquiv (K := A) B K
          (WithConv.toConv (q.ofConv.comp gK.hom.toAlgHom))).ofConv.comp
            f.hom.toAlgHom) := by
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro x
  rw [CommHopfAlgCat.baseChangeIsoPointsMulEquiv_apply_apply]
  simp only [AlgHom.comp_apply]
  rw [CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply]
  simp only [AlgHom.comp_apply]
  rw [← hcompat, _root_.CommHopfAlgCat.hom_comp, _root_.CommHopfAlgCat.hom_comp]
  -- Category composition is stored as nested `BialgHom.comp`, while the isomorphism cancellation
  -- and pure-tensor rules are stated for applications. This conversion exposes exactly those two
  -- public interfaces and keeps the representation-dependent proofs below independent of wrappers.
  change q.ofConv (gK.hom ((CommHopfAlgCat.baseChangeMap f).hom
      ((baseChangeCoordinateIso n hn A).hom.hom
        ((baseChangeCoordinateIso n hn A).inv (1 ⊗ₜ[ℤ] x))))) =
    q.ofConv (gK.hom (1 ⊗ₜ[ℤ] f.hom x))
  rw [Iso.inv_hom_id_apply, CommHopfAlgCat.baseChangeMap_apply_tmul]

/-! ## The transported root subgroups -/

/-- The integral `k`th root-subgroup coordinate map, with source expressed using the named
type-`Dₙ` defining ideal. -/
noncomputable def rootSubgroupIntegralCoordinateMap (k : Fin n ⊕ Fin n) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
        (definingIdeal n hn) ⟶
      AdditiveGroup.coordinateHopfAlgebra ℤ :=
  kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
    (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) (definingIdeal_def n hn) k

/-- The integral root-subgroup coordinate map is the generic Kostant one, read through the named
type-`Dₙ` defining ideal. -/
theorem rootSubgroupIntegralCoordinateMap_def (k : Fin n ⊕ Fin n) :
    rootSubgroupIntegralCoordinateMap n hn k =
      kostantRootSubgroupToralCoordinateMapOfEq
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
        (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)
        (definingIdeal_def n hn) k := by
  rw [rootSubgroupIntegralCoordinateMap]

/-- The integral factored root-subgroup map recovers the represented `k`th root-subgroup
coordinate map inside `GL_(2^n)`, and so determines it. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupIntegralCoordinateMap (k : Fin n ⊕ Fin n) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
          (definingIdeal n hn) ≫
        rootSubgroupIntegralCoordinateMap n hn k =
      kostantRootSubgroupCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
        (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn) k
        (isNilpotent_rep_rootGenerator n hn k) (latticeBasis n) := by
  rw [rootSubgroupIntegralCoordinateMap]
  exact mkQuotient_comp_kostantRootSubgroupToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) (definingIdeal_def n hn) k

/-- On points, the integral factored coordinate map is the named numbered root subgroup. -/
@[simp]
theorem pointsMulEquiv_mapPointsFunctor_rootSubgroupIntegralCoordinateMap
    (B : CommAlgCat.{w} ℤ) (k : Fin n ⊕ Fin n)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) B) :
    pointsMulEquiv n hn B
        ((CommHopfAlgCat.mapPointsFunctor
          (rootSubgroupIntegralCoordinateMap n hn k)).app B q) =
      rootSubgroupPoints n hn k B (AdditiveGroup.gaPointsMulEquiv q) := by
  -- `coordinateHopfAlgebra` is definitionally the symmetric-algebra model used by the public
  -- additive-points lemmas below; naming that model also fixes the intended `ℤ`-algebra instance.
  change WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] B) at q
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_pointsMulEquiv_apply, coe_rootSubgroupPoints]
  rw [CommHopfAlgCat.quotientPointsHom_apply, GeneralLinear.pointsMulEquiv_apply]
  -- The preceding public application lemmas leave the quotient and categorical composition
  -- wrappers folded. This conversion exposes their underlying algebra-hom precomposition.
  change GeneralLinear.pointToGeneralLinear (dimension n)
      (WithConv.toConv (q.ofConv.comp
        ((CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) ≫
            rootSubgroupIntegralCoordinateMap n hn k).hom :
          GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) →ₐ[ℤ]
            AdditiveGroup.coordinateHopfAlgebra ℤ))) = _
  rw [mkQuotient_comp_rootSubgroupIntegralCoordinateMap]
  let q' := WithConv.toConv q.ofConv.toRingHom.toIntAlgHom
  let u : Multiplicative B := AdditiveGroup.gaPointsMulEquiv q
  let u' := (@AdditiveGroup.gaPointsMulEquiv ℤ Int.instCommSemiring B _
    (Ring.toIntAlgebra B)) q'
  have hu : u' = u := by
    apply Multiplicative.toAdd.injective
    calc
      Multiplicative.toAdd u' = q'.ofConv (SymmetricAlgebra.ι ℤ ℤ 1) := by
        exact @AdditiveGroup.toAdd_gaPointsMulEquiv ℤ Int.instCommSemiring B _
          (Ring.toIntAlgebra B) q'
      _ = q.ofConv (SymmetricAlgebra.ι ℤ ℤ 1) :=
        RingHom.toIntAlgHom_apply q.ofConv.toRingHom _
      _ = Multiplicative.toAdd u := by
        exact (@AdditiveGroup.toAdd_gaPointsMulEquiv ℤ Int.instCommSemiring B _
          (CommAlgCat.algebra B) q).symm
  -- The generic Kostant matrix theorem uses `Ring.toIntAlgebra B`, whereas the named point uses
  -- the definitionally equal algebra carried by `CommAlgCat`; `hu` compares the two parameters.
  change _ = kostantRootSubgroupMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn k)
    (latticeBasis n)
      ((@AdditiveGroup.gaPointsMulEquiv ℤ Int.instCommSemiring B _
        (Ring.toIntAlgebra B)).symm u)
  rw [← hu]
  have hcancel :
      (@AdditiveGroup.gaPointsMulEquiv ℤ Int.instCommSemiring B _
        (Ring.toIntAlgebra B)).symm u' = q' := by
    exact (@AdditiveGroup.gaPointsMulEquiv ℤ Int.instCommSemiring B _
      (Ring.toIntAlgebra B)).symm_apply_apply q'
  rw [hcancel]
  have hroot := pointsMulEquiv_kostantRootSubgroupCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn k)
    (latticeBasis n) B q'
  rw [← hroot]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [GeneralLinear.pointToGeneralLinear_apply, GeneralLinear.pointToGeneralLinear_apply]
  exact RingHom.toIntAlgHom_apply q.ofConv.toRingHom _

/-- Explicit precomposition form of
`pointsMulEquiv_mapPointsFunctor_rootSubgroupIntegralCoordinateMap`. -/
private theorem pointsMulEquiv_rootSubgroupIntegralCoordinateMap_apply
    (B : CommAlgCat.{w} ℤ) (k : Fin n ⊕ Fin n)
    (q : HopfAlgebra.points
      (R := ℤ) (H := AdditiveGroup.coordinateHopfAlgebra ℤ) B) :
    pointsMulEquiv n hn B
        (WithConv.toConv (q.ofConv.comp
          (rootSubgroupIntegralCoordinateMap n hn k).hom.toAlgHom)) =
      rootSubgroupPoints n hn k B (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
  exact pointsMulEquiv_mapPointsFunctor_rootSubgroupIntegralCoordinateMap n hn B k q

/-- The integral factored root-subgroup coordinate map represents the carrier's `k`th numbered
root subgroup: its spectrum is `TauCeti.TypeDSpinCarrier.rootSubgroup`, read through the
quotient-spectrum presentation of the carrier. -/
-- Not a `simp` lemma: `simp` rewrites `hopfSpec` to `algSpec.mapGrp` composed with the
-- Hopf-algebra/cogroup equivalence, so no equation whose sides mention `hopfSpec.map` has a
-- left-hand side in `simp` normal form.
theorem hopfSpec_map_rootSubgroupIntegralCoordinateMap_op (k : Fin n ⊕ Fin n) :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (rootSubgroupIntegralCoordinateMap n hn k).op =
      eqToHom (AdditiveGroup.groupScheme_def ℤ).symm ≫
        rootSubgroup n hn k ≫ eqToHom (groupScheme_def n hn) := by
  simpa only [rootSubgroupIntegralCoordinateMap, rootSubgroup_def, Category.assoc,
    eqToHom_trans] using
    hopfSpec_map_kostantRootSubgroupToralCoordinateMapOfEq_op
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
      (latticeBasis n) (basisWeight n) (definingIdeal_def n hn) k

/-- The base-changed `k`th root-subgroup coordinate map factored through the transported
type-`Dₙ` carrier. -/
noncomputable def rootSubgroupToBaseChangeCoordinateMap (k : Fin n ⊕ Fin n) :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A) ⟶
      AdditiveGroup.coordinateHopfAlgebra A :=
  kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A k

/-- The factored root-subgroup map recovers its ambient transported coordinate map after composition
with the quotient map. -/
@[simp]
theorem mkQuotient_comp_rootSubgroupToBaseChangeCoordinateMap
    (k : Fin n ⊕ Fin n) :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A) ≫
        rootSubgroupToBaseChangeCoordinateMap n hn A k =
      kostantRootSubgroupBaseChangePresentationCoordinateMap
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) A k := by
  unfold baseChangeDefiningIdeal rootSubgroupToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantRootSubgroupToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A k

/-- Under the base-change coordinate isomorphism, the factored `k`th root-subgroup map is the
scalar extension of its integral coordinate map. -/
@[simp]
theorem baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap
    (k : Fin n ⊕ Fin n) :
    (baseChangeCoordinateIso n hn A).hom ≫
          CommHopfAlgCat.baseChangeMap (rootSubgroupIntegralCoordinateMap n hn k) ≫
        (_root_.CommHopfAlgCat.ofHom
          (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A))) =
      rootSubgroupToBaseChangeCoordinateMap n hn A k := by
  rw [baseChangeCoordinateIso, rootSubgroupIntegralCoordinateMap,
    rootSubgroupToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_rootSubgroupBaseChangeMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A
    (definingIdeal_def n hn) k

/-- On points, the transported factored coordinate map is the named numbered root subgroup. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPointsFunctor_rootSubgroupToBaseChangeCoordinateMap
    (B : CommAlgCat.{w} A) (k : Fin n ⊕ Fin n)
    (q : HopfAlgebra.points
      (R := A) (H := AdditiveGroup.coordinateHopfAlgebra A) B) :
    baseChangePointsMulEquiv n hn A B
        ((CommHopfAlgCat.mapPointsFunctor
          (rootSubgroupToBaseChangeCoordinateMap n hn A k)).app B q) =
      rootSubgroupPoints n hn k B (AdditiveGroup.gaPointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  let qTensor :=
    WithConv.toConv (q.ofConv.comp
      (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom.hom.toAlgHom)
  let qIntegral := CommHopfAlgCat.baseChangePointsMulEquiv (K := A) B
    (AdditiveGroup.coordinateHopfAlgebra ℤ) qTensor
  have hparam : AdditiveGroup.gaPointsMulEquiv qIntegral =
      AdditiveGroup.gaPointsMulEquiv q := by
    apply Multiplicative.toAdd.injective
    rw [AdditiveGroup.toAdd_gaPointsMulEquiv, AdditiveGroup.toAdd_gaPointsMulEquiv]
    dsimp only [qIntegral]
    rw [CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply]
    dsimp only [qTensor]
    rw [AlgHom.comp_apply]
    -- The additive coordinate ring is implemented by a symmetric algebra; this conversion
    -- exposes the source expected by the public scalar-tensor generator lemma.
    change q.ofConv
        (AdditiveGroup.gaScalarTensorBialgEquiv (k := ℤ) (K := A)
          (1 ⊗ₜ[ℤ] SymmetricAlgebra.ι ℤ ℤ 1)) =
      q.ofConv (SymmetricAlgebra.ι A A 1)
    rw [AdditiveGroup.gaScalarTensorBialgEquiv_tmul_ι]
    simp
  rw [← hparam,
    ← pointsMulEquiv_rootSubgroupIntegralCoordinateMap_apply n hn
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B) k qIntegral]
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply]
  apply congrArg (pointsMulEquiv n hn
    (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B))
  dsimp only [qIntegral, qTensor]
  exact baseChangeIsoPointsMulEquiv_mapPointsFunctor n hn A
    (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ A).hom
    (rootSubgroupIntegralCoordinateMap n hn k)
    (rootSubgroupToBaseChangeCoordinateMap n hn A k)
    (baseChangeCoordinateIso_hom_comp_rootSubgroupBaseChangeMap n hn A k) B q

/-! ## The transported weight torus -/

/-- The integral weight-torus coordinate map, with source expressed using the named type-`Dₙ`
defining ideal. -/
noncomputable def weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
        (definingIdeal n hn) ⟶
      (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin n))).obj :=
  kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
    (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) (definingIdeal_def n hn)

/-- The integral weight-torus coordinate map is the generic Kostant one, read through the named
type-`Dₙ` defining ideal. -/
theorem weightTorusIntegralCoordinateMap_def :
    weightTorusIntegralCoordinateMap n hn =
      kostantWeightTorusToralCoordinateMapOfEq
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)
        (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)
        (definingIdeal_def n hn) := by
  rw [weightTorusIntegralCoordinateMap]

/-- The integral factored weight-torus map recovers the weight-torus coordinate map inside
`GL_(2^n)`, and so determines it. -/
@[simp]
theorem mkQuotient_comp_weightTorusIntegralCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n))
          (definingIdeal n hn) ≫
        weightTorusIntegralCoordinateMap n hn =
      GeneralLinear.weightTorusCoordinateMap (basisWeight n) := by
  rw [weightTorusIntegralCoordinateMap]
  exact mkQuotient_comp_kostantWeightTorusToralCoordinateMapOfEq
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) (definingIdeal_def n hn)

/-- On points, the integral factored coordinate map is the named spin weight torus. -/
@[simp]
theorem pointsMulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap
    (B : CommAlgCat.{w} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ)
      (H := (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin n))).obj) B) :
    pointsMulEquiv n hn B
        ((CommHopfAlgCat.mapPointsFunctor
          (weightTorusIntegralCoordinateMap n hn)).app B q) =
      weightTorusPoints n hn B (SplitTorus.pointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  apply Subtype.ext
  rw [coe_pointsMulEquiv_apply, coe_weightTorusPoints,
    CommHopfAlgCat.quotientPointsHom_apply, GeneralLinear.pointsMulEquiv_apply]
  -- As in the root-subgroup proof, expose the algebra-hom precomposition hidden by the quotient,
  -- general-linear points equivalence, and categorical composition wrappers.
  change GeneralLinear.pointToGeneralLinear (dimension n)
      (WithConv.toConv (q.ofConv.comp
        ((CommHopfAlgCat.mkQuotient
          (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) ≫
            weightTorusIntegralCoordinateMap n hn).hom :
          GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) →ₐ[ℤ]
            MonoidAlgebra ℤ (SplitTorus.characterGroup (Fin n))))) = _
  rw [mkQuotient_comp_weightTorusIntegralCoordinateMap]
  rw [← GeneralLinear.pointsMulEquiv_apply,
    ← CommHopfAlgCat.mapPointsFunctor_app_apply,
    GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap,
    kostantTorusMatrix_apply]

/-- Explicit precomposition form of
`pointsMulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap`. -/
private theorem pointsMulEquiv_weightTorusIntegralCoordinateMap_apply
    (B : CommAlgCat.{w} ℤ)
    (q : HopfAlgebra.points
      (R := ℤ)
      (H := (DiagonalizableGroup.coordinateRing ℤ
        (SplitTorus.characterGroup (Fin n))).obj) B) :
    pointsMulEquiv n hn B
        (WithConv.toConv (q.ofConv.comp
          (weightTorusIntegralCoordinateMap n hn).hom.toAlgHom)) =
      weightTorusPoints n hn B (SplitTorus.pointsMulEquiv q) := by
  rw [← CommHopfAlgCat.mapPointsFunctor_app_apply]
  exact pointsMulEquiv_mapPointsFunctor_weightTorusIntegralCoordinateMap n hn B q

/-- The integral factored weight-torus coordinate map represents the carrier's weight torus: its
spectrum is `TauCeti.TypeDSpinCarrier.weightTorus`, read through the quotient-spectrum
presentation of the carrier. -/
theorem hopfSpec_map_weightTorusIntegralCoordinateMap_op :
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
        (weightTorusIntegralCoordinateMap n hn).op =
      eqToHom (DiagonalizableGroup.groupScheme_def ℤ
          (SplitTorus.characterGroup (Fin n))).symm ≫
        weightTorus n hn ≫ eqToHom (groupScheme_def n hn) := by
  simpa only [weightTorusIntegralCoordinateMap, weightTorus_def, Category.assoc,
    eqToHom_trans] using
    hopfSpec_map_kostantWeightTorusToralCoordinateMapOfEq_op
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
      (latticeBasis n) (basisWeight n) (definingIdeal_def n hn)

/-- The base-changed weight-torus coordinate map factored through the transported type-`Dₙ`
carrier. -/
noncomputable def weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
        (baseChangeDefiningIdeal n hn A) ⟶
      (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin n))).obj :=
  kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A

/-- The factored weight-torus map recovers its ambient transported coordinate map, and so
determines it. -/
@[simp]
theorem mkQuotient_comp_weightTorusToBaseChangeCoordinateMap :
    CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra A (dimension n))
          (baseChangeDefiningIdeal n hn A) ≫
        weightTorusToBaseChangeCoordinateMap n hn A =
      GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n) := by
  unfold baseChangeDefiningIdeal weightTorusToBaseChangeCoordinateMap
  exact mkQuotient_comp_kostantWeightTorusToralBaseChangePresentationCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A

/-- Under the base-change coordinate isomorphism, the factored weight-torus map is the scalar
extension of its integral coordinate map. -/
-- The bialgebra equivalence is coerced by name: writing `↑` leaves the source of the coercion a
-- metavariable, and the coordinate ring of the character group only matches the monoid algebra
-- the equivalence is stated for after unfolding, which the coercion elaborator does not do.
@[simp]
theorem baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap :
    (baseChangeCoordinateIso n hn A).hom ≫
          CommHopfAlgCat.baseChangeMap (weightTorusIntegralCoordinateMap n hn) ≫
        (_root_.CommHopfAlgCat.ofHom
          (BialgHomClass.toBialgHom
            (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A
              (G := SplitTorus.characterGroup (Fin n))))) =
      weightTorusToBaseChangeCoordinateMap n hn A := by
  rw [baseChangeCoordinateIso, weightTorusIntegralCoordinateMap,
    weightTorusToBaseChangeCoordinateMap]
  exact kostantToralBaseChangePresentationIsoOfEq_hom_comp_weightTorusBaseChangeMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A
    (definingIdeal_def n hn)

/-- On points, the transported factored weight-torus map is the named spin weight torus. -/
@[simp]
theorem baseChangePointsMulEquiv_mapPointsFunctor_weightTorusToBaseChangeCoordinateMap
    (B : CommAlgCat.{w} A)
    (q : HopfAlgebra.points
      (R := A)
      (H := (DiagonalizableGroup.coordinateRing A
        (SplitTorus.characterGroup (Fin n))).obj) B) :
    baseChangePointsMulEquiv n hn A B
        ((CommHopfAlgCat.mapPointsFunctor
          (weightTorusToBaseChangeCoordinateMap n hn A)).app B q) =
      weightTorusPoints n hn B (SplitTorus.pointsMulEquiv q) := by
  rw [CommHopfAlgCat.mapPointsFunctor_app_apply]
  let qTensor :=
    WithConv.toConv (q.ofConv.comp
      (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso ℤ A
        (SplitTorus.characterGroup (Fin n))).hom.hom.toAlgHom)
  let qIntegral := CommHopfAlgCat.baseChangePointsMulEquiv (K := A) B
    (DiagonalizableGroup.coordinateRing ℤ
      (SplitTorus.characterGroup (Fin n))).obj qTensor
  have hparam : SplitTorus.pointsMulEquiv qIntegral =
      SplitTorus.pointsMulEquiv q := by
    funext i
    apply Units.ext
    rw [SplitTorus.pointsMulEquiv_apply_coe, SplitTorus.pointsMulEquiv_apply_coe]
    dsimp only [qIntegral]
    rw [CommHopfAlgCat.baseChangePointsMulEquiv_apply_apply]
    dsimp only [qTensor]
    rw [AlgHom.comp_apply]
    congr 1
    -- The diagonalizable coordinate ring unfolds to a monoid algebra; this conversion exposes
    -- the pure tensor of a basis character used by the scalar-tensor equivalence lemma.
    change (TauCeti.MonoidAlgebra.scalarTensorBialgEquiv ℤ A)
      (1 ⊗ₜ[ℤ] MonoidAlgebra.single
        (Multiplicative.ofAdd (Finsupp.single i 1)) 1) = _
    rw [TauCeti.MonoidAlgebra.scalarTensorBialgEquiv_tmul]
    simp
  rw [← hparam,
    ← pointsMulEquiv_weightTorusIntegralCoordinateMap_apply n hn
      (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B) qIntegral]
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply]
  apply congrArg (pointsMulEquiv n hn
    (TauCeti.CommAlgCat.restrictScalarsObj (algebraMap ℤ A) B))
  dsimp only [qIntegral, qTensor]
  exact baseChangeIsoPointsMulEquiv_mapPointsFunctor n hn A
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso ℤ A
      (SplitTorus.characterGroup (Fin n))).hom
    (weightTorusIntegralCoordinateMap n hn)
    (weightTorusToBaseChangeCoordinateMap n hn A)
    (baseChangeCoordinateIso_hom_comp_weightTorusBaseChangeMap n hn A) B q

/-- The closed subgroup of `GL_(2^n)/A` generated by the transported numbered root subgroups and
the transported weight torus lies in the base change of the integral type-`Dₙ` carrier.

The reverse inclusion is not asserted over an arbitrary base ring. -/
theorem baseChangeDefiningIdeal_le_commonKernel :
    let K : Sum (Fin n ⊕ Fin n) Unit → CommHopfAlgCat A
      | .inl _ => AdditiveGroup.coordinateHopfAlgebra A
      | .inr _ =>
          (DiagonalizableGroup.coordinateRing A
            (SplitTorus.characterGroup (Fin n))).obj
    baseChangeDefiningIdeal n hn A ≤
      CommHopfAlgCat.commonKernelHopfIdeal (K := K)
        (fun j => match j with
          | .inl k => kostantRootSubgroupBaseChangePresentationCoordinateMap
              (TauCeti.serreRootGenerator (CartanMatrix.D n))
              (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
              (rep_kostantForm_mem_lattice n hn)
              (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) A k
          | .inr _ => GeneralLinear.weightTorusBaseChangeCoordinateMap ℤ A (basisWeight n)) := by
  have h := kostantToralBaseChangePresentationIdeal_le_commonKernelHopfIdeal
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A
  -- The generic containment indexes its generators by a `match` of its own, and neither that
  -- matcher nor `CommHopfAlgCat.commonKernelHopfIdeal` is exposed for unfolding, so the two
  -- families are compared branchwise on a constructor rather than by a single `exact`.
  dsimp only at h ⊢
  rw [CommHopfAlgCat.le_commonKernelHopfIdeal_iff] at h ⊢
  rintro (k | _)
  · exact h (.inl k)
  · exact h (.inr ())

end

end TauCeti.TypeDSpinCarrier
