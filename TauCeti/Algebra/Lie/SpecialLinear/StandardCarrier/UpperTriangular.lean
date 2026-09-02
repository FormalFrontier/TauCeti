/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne

/-!
# The upper-triangular subgroup of the type-A full-weight carrier

The full-weight type-`A_r` carrier is an explicit closed subgroup scheme of `GL_(r+1)`.  This file
intersects it scheme-theoretically with the standard upper-triangular subgroup scheme of `GL_(r+1)`.
On coordinate Hopf algebras, intersection is the join of the two defining Hopf ideals.  The
resulting `TauCeti.SlStd.upperTriangularGroupScheme` is therefore a closed subgroup scheme of the
actual Chevalley carrier, not a separately chosen matrix group; it comes with closed immersions
into both the carrier and the ambient upper-triangular subgroup scheme of `GL_(r+1)`.

Over every commutative value ring `A`, its embedded matrix points are exactly

```text
SlStd.points r A ∩ upperTriangularGroup (Fin (r + 1)) A.
```

The named split torus and every positive simple-root subgroup factor through this intersection as
morphisms of group schemes, and their factorizations recompose to the carrier's own pinning
morphisms.  A negative simple-root *point* lies in the intersection exactly when its parameter is
zero, so no comparable factorization of a negative root subgroup can exist: the construction
selects the positive half of the carrier's pinning rather than merely containing all of its
generators.

No maximal-solvability assertion is made here.  Identifying this closed subgroup as a Borel and
the named split torus as maximal requires the reductivity and root-datum structure of the carrier.

## Main definitions

* `TauCeti.SlStd.upperTriangularDefiningIdeal`: the join of the carrier and upper-triangular
  defining Hopf ideals.
* `TauCeti.SlStd.upperTriangularGroupScheme`: the corresponding closed subgroup scheme.
* `TauCeti.SlStd.upperTriangularInclusion`: its closed immersion into the type-`A` carrier.
* `TauCeti.SlStd.upperTriangularAmbientInclusion`: its closed immersion into the upper-triangular
  subgroup scheme of `GL_(r+1)`.
* `TauCeti.SlStd.upperTriangularPoints`: its matrix points inside `GL_(r+1)`.
* `TauCeti.SlStd.rootSubgroupUpperTriangular` and `TauCeti.SlStd.weightTorusUpperTriangular`: the
  positive numbered root subgroups and the split weight torus, factored through it.

## Main results

* `TauCeti.SlStd.upperTriangularPoints_eq`: the point group is the intersection of the carrier
  points with the upper-triangular matrices.
* `TauCeti.SlStd.isUpperTriangular_coe_rootSubgroupPoints_positive` and
  `TauCeti.SlStd.rootSubgroupPoints_positive_mem_upperTriangularPoints`: every positive numbered
  root subgroup point lies in the intersection.
* `TauCeti.SlStd.isUpperTriangular_coe_rootSubgroupPoints_negative_iff` and
  `TauCeti.SlStd.rootSubgroupPoints_negative_mem_upperTriangularPoints_iff`: a negative numbered
  root subgroup point lies in it only at the identity.
* `TauCeti.SlStd.isUpperTriangular_coe_weightTorusPoints` and
  `TauCeti.SlStd.weightTorusPoints_mem_upperTriangularPoints`: every split weight torus point lies
  in the intersection.
* `TauCeti.SlStd.rootSubgroupUpperTriangular_comp_upperTriangularInclusion` and
  `TauCeti.SlStd.weightTorusUpperTriangular_comp_upperTriangularInclusion`: the scheme-level
  factorizations recompose to the carrier's pinning morphisms.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--28.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Sections 3--4.
* The ambient upper-triangular Hopf ideal, group scheme and point identification are
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic`; the intersection of point
  groups cut out by a join of Hopf ideals is
  `TauCeti.GeneralLinear.hopfIdealPointsSubgroup_sup`, resting on
  `TauCeti.CommHopfAlgCat.quotientPointsSubgroup_sup` from
  `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order`.
* The carrier itself, its defining ideal, its numbered root subgroups and its weight torus are the
  existing `SlStd` formalization in `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Basic` and
  `TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne`, built on the Kostant
  root-subgroup scheme API of
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme`; the scheme-level
  factorizations below follow the same `CommHopfAlgCat.liftQuotient` pattern used there.

This advances the "Pinnings" target of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`: it constructs the closed positive subgroup containing
the torus and positive simple-root subgroups for the explicit type-`A` carrier.  Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes that pinned carrier.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.SlStd

universe v

variable (r : ℕ)

/-! ## The scheme-theoretic intersection -/

/-- The defining ideal of the upper-triangular subgroup of the type-`A_r` carrier.  The join
imposes both the carrier equations and the vanishing of every coordinate below the diagonal. -/
noncomputable def upperTriangularDefiningIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) :=
  definingIdeal r ⊔ GeneralLinear.UpperTriangular.definingHopfIdeal ℤ (r + 1)

/-- The carrier defining ideal is contained in the upper-triangular defining ideal. -/
theorem definingIdeal_le_upperTriangularDefiningIdeal :
    definingIdeal r ≤ upperTriangularDefiningIdeal r := by
  rw [upperTriangularDefiningIdeal]
  exact le_sup_left

/-- The ambient upper-triangular defining ideal is contained in the upper-triangular defining
ideal of the carrier. -/
theorem generalLinearUpperTriangularDefiningHopfIdeal_le_upperTriangularDefiningIdeal :
    GeneralLinear.UpperTriangular.definingHopfIdeal ℤ (r + 1) ≤
      upperTriangularDefiningIdeal r := by
  rw [upperTriangularDefiningIdeal]
  exact le_sup_right

/-- The upper-triangular closed subgroup scheme of the full-weight type-`A_r` carrier. -/
noncomputable abbrev upperTriangularGroupScheme : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  CommHopfAlgCat.quotientSpec (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
    (upperTriangularDefiningIdeal r)

/-- The canonical closed immersion of the upper-triangular subgroup scheme into the type-`A_r`
carrier, induced by the inclusion of defining Hopf ideals. -/
noncomputable def upperTriangularInclusion : upperTriangularGroupScheme r ⟶ groupScheme r :=
  CommHopfAlgCat.quotientSpecMapOfLe
    (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
    (definingIdeal_le_upperTriangularDefiningIdeal r)

/-- The upper-triangular subgroup scheme is closed in the type-`A_r` carrier. -/
instance isClosedImmersion_upperTriangularInclusion :
    IsClosedImmersion (upperTriangularInclusion r).hom.hom.left := by
  unfold upperTriangularInclusion
  infer_instance

/-- The canonical closed immersion of the upper-triangular subgroup scheme of the type-`A_r`
carrier into the ambient upper-triangular subgroup scheme of `GL_(r+1)`. -/
noncomputable def upperTriangularAmbientInclusion :
    upperTriangularGroupScheme r ⟶ GeneralLinear.UpperTriangular.groupScheme ℤ (r + 1) :=
  CommHopfAlgCat.quotientSpecMapOfLe
    (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
    (generalLinearUpperTriangularDefiningHopfIdeal_le_upperTriangularDefiningIdeal r)

/-- The upper-triangular subgroup scheme of the carrier is closed in the ambient upper-triangular
subgroup scheme of `GL_(r+1)`. -/
instance isClosedImmersion_upperTriangularAmbientInclusion :
    IsClosedImmersion (upperTriangularAmbientInclusion r).hom.hom.left := by
  unfold upperTriangularAmbientInclusion
  infer_instance

/-- Including the upper-triangular subgroup into the carrier and then into `GL_(r+1)` is the
quotient-spectrum inclusion cut out by the joined ideal. -/
@[simp]
theorem upperTriangularInclusion_comp_carrierι :
    upperTriangularInclusion r ≫ carrierι r =
      CommHopfAlgCat.quotientSpecι (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
          (upperTriangularDefiningIdeal r) ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ (r + 1)).symm := by
  rw [upperTriangularInclusion, carrierι_def,
    UniversalEnvelopingAlgebra.kostantToralGroupSchemeι_def, ← Category.assoc,
    CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι]

/-- The two closed immersions of the upper-triangular subgroup scheme agree over `GL_(r+1)`. -/
@[simp]
theorem upperTriangularAmbientInclusion_comp_inclusion :
    upperTriangularAmbientInclusion r ≫ GeneralLinear.UpperTriangular.inclusion ℤ (r + 1) =
      upperTriangularInclusion r ≫ carrierι r := by
  rw [upperTriangularInclusion_comp_carrierι, upperTriangularAmbientInclusion,
    GeneralLinear.UpperTriangular.inclusion, GeneralLinear.weightParabolicInclusion_def,
    ← Category.assoc, CommHopfAlgCat.quotientSpecMapOfLe_comp_quotientSpecι, eqToIso.hom]

/-! ## Matrix points -/

/-- The matrix points of the upper-triangular subgroup scheme of the type-`A_r` carrier. -/
noncomputable def upperTriangularPoints (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (r + 1)) A) :=
  GeneralLinear.hopfIdealPointsSubgroup (r + 1) (upperTriangularDefiningIdeal r) A

/-- **The upper-triangular points of the carrier are the intersection of the carrier points and
the invertible upper-triangular matrices.**  This is the general law that a join of Hopf ideals
cuts out an intersection of point groups, specialized to the two ideals at hand. -/
theorem upperTriangularPoints_eq (A : Type v) [CommRing A] :
    upperTriangularPoints r A =
      points r A ⊓ upperTriangularGroup (Fin (r + 1)) A := by
  rw [upperTriangularPoints, upperTriangularDefiningIdeal,
    GeneralLinear.hopfIdealPointsSubgroup_sup, ← points_def,
    GeneralLinear.UpperTriangular.hopfIdealPointsSubgroup_eq]

/-- Membership in the upper-triangular carrier points means carrier membership together with
upper triangularity of the underlying matrix. -/
@[simp]
theorem mem_upperTriangularPoints_iff
    (A : Type v) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ upperTriangularPoints r A ↔
      g ∈ points r A ∧ (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
  rw [upperTriangularPoints_eq, Subgroup.mem_inf, UpperTriangularGroup.mem_iff]

/-! ## Triangularity of the pinning matrices -/

/-- The divided-power exponential matrix of a positive numbered root generator is upper
triangular: it is a transvection whose only off-diagonal entry sits above the diagonal. -/
private theorem isUpperTriangular_coe_kostantRootSubgroupMatrix_inl
    {A : Type*} [CommRing A] (i : Fin r)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    ((UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
          (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
          (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (.inl i)
          (isNilpotent_rep_rootGenerator r (.inl i)) (latticeBasis r) q :
        Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
  rw [kostantRootSubgroupMatrix_eq_transvection, coe_transvectionUnit]
  simp only [rootTarget_inl, rootSource_inl]
  exact Matrix.blockTriangular_transvection (b := id) (Fin.castSucc_le_succ i) _

/-- A positive numbered root-subgroup matrix is upper triangular. -/
theorem isUpperTriangular_coe_rootSubgroupPoints_positive
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    ((rootSubgroupPoints r (.inl i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
  rw [coe_rootSubgroupPoints]
  exact isUpperTriangular_coe_kostantRootSubgroupMatrix_inl r i _

/-- A negative numbered root-subgroup matrix is upper triangular exactly when its parameter is
zero: its only nonzero off-diagonal entry sits below the diagonal. -/
theorem isUpperTriangular_coe_rootSubgroupPoints_negative_iff
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    ((rootSubgroupPoints r (.inr i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular ↔
      Multiplicative.toAdd u = 0 := by
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection,
    MulEquiv.apply_symm_apply, coe_transvectionUnit]
  simp only [rootTarget_inr, rootSource_inr]
  exact isUpperTriangular_transvection_iff (Fin.castSucc_lt_succ (i := i)) _

/-- A split weight torus matrix is diagonal, hence upper triangular. -/
theorem isUpperTriangular_coe_weightTorusPoints
    (A : Type v) [CommRing A] (s : Fin r → Aˣ) :
    ((weightTorusPoints r A s : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
  rw [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  exact Matrix.blockTriangular_diagonal _

/-! ## The positive pinning lies in the intersection -/

/-- Every positive numbered root-subgroup point belongs to the upper-triangular subgroup of the
type-`A_r` carrier. -/
theorem rootSubgroupPoints_positive_mem_upperTriangularPoints
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    (rootSubgroupPoints r (.inl i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
      upperTriangularPoints r A := by
  rw [mem_upperTriangularPoints_iff]
  exact ⟨(rootSubgroupPoints r (.inl i) A u).property,
    isUpperTriangular_coe_rootSubgroupPoints_positive r A i u⟩

/-- A negative numbered root-subgroup point lies in the upper-triangular subgroup exactly when
its parameter is zero.  In particular, the intersection selects the positive, rather than both,
halves of the pinning. -/
theorem rootSubgroupPoints_negative_mem_upperTriangularPoints_iff
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    (rootSubgroupPoints r (.inr i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
        upperTriangularPoints r A ↔
      Multiplicative.toAdd u = 0 := by
  rw [mem_upperTriangularPoints_iff, isUpperTriangular_coe_rootSubgroupPoints_negative_iff,
    and_iff_right (rootSubgroupPoints r (.inr i) A u).property]

/-- Every point of the named split weight torus belongs to the upper-triangular subgroup of the
type-`A_r` carrier. -/
theorem weightTorusPoints_mem_upperTriangularPoints
    (A : Type v) [CommRing A] (s : Fin r → Aˣ) :
    (weightTorusPoints r A s : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
      upperTriangularPoints r A := by
  rw [mem_upperTriangularPoints_iff]
  exact ⟨(weightTorusPoints r A s).property, isUpperTriangular_coe_weightTorusPoints r A s⟩

/-! ## Scheme-level factorization of the positive pinning -/

/-- The coordinate morphism of the numbered root subgroup of the type-`A_r` carrier. -/
private noncomputable abbrev rootCoordinateMap (k : Fin r ⊕ Fin r) :
    GeneralLinear.coordinateHopfAlgebra ℤ (r + 1) ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ :=
  UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) k
    (isNilpotent_rep_rootGenerator r k) (latticeBasis r)

/-- The tautological matrix point of a positive root-subgroup coordinate map is the generic
transvection, hence upper triangular. -/
private theorem isUpperTriangular_pointToGeneralLinear_rootCoordinateMap (i : Fin r) :
    ((GeneralLinear.pointToGeneralLinear (r + 1)
          (toConv (rootCoordinateMap r (.inl i)).hom.toAlgHom) :
        Matrix.GeneralLinearGroup (Fin (r + 1)) (AdditiveGroup.coordinateHopfAlgebra ℤ)) :
      Matrix (Fin (r + 1)) (Fin (r + 1))
        (AdditiveGroup.coordinateHopfAlgebra ℤ)).IsUpperTriangular := by
  -- The tautological point of the additive group, at which the generic-point identity is read.
  let q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ]
      AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))
  have hq : q.ofConv = AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ) :=
    WithConv.ofConv_toConv _
  have hpoint : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (q.ofConv.comp (rootCoordinateMap r (.inl i)).hom.toAlgHom)) =
      UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (.inl i)
        (isNilpotent_rep_rootGenerator r (.inl i)) (latticeBasis r) q :=
    UniversalEnvelopingAlgebra.pointsMulEquiv_kostantRootSubgroupCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (.inl i)
      (isNilpotent_rep_rootGenerator r (.inl i)) (latticeBasis r)
      (AdditiveGroup.coordinateHopfAlgebra ℤ) q
  have hpoint' : GeneralLinear.pointToGeneralLinear (r + 1)
      (toConv (rootCoordinateMap r (.inl i)).hom.toAlgHom) =
      UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix (rootGenerator r)
        (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
        (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv) (.inl i)
        (isNilpotent_rep_rootGenerator r (.inl i)) (latticeBasis r) q := by
    simpa only [hq, AlgHom.id_comp, WithConv.ofConv_toConv] using hpoint
  rw [hpoint']
  exact isUpperTriangular_coe_kostantRootSubgroupMatrix_inl r i q

/-- A positive root-subgroup coordinate map kills the upper-triangular defining ideal: it kills
the carrier ideal, and its tautological point is the generic upper-triangular transvection. -/
private theorem upperTriangularDefiningIdeal_le_ker_rootCoordinateMap (i : Fin r) :
    (upperTriangularDefiningIdeal r).toIdeal ≤
      RingHom.ker (rootCoordinateMap r (.inl i)).hom.toAlgHom.toRingHom := by
  rw [upperTriangularDefiningIdeal, HopfIdeal.sup_toIdeal]
  exact sup_le (UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_toIdeal_le_root_ker
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (.inl i))
    (GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker_of_isUpperTriangular
      ℤ (r + 1) _ (isUpperTriangular_pointToGeneralLinear_rootCoordinateMap r i))

/-- The weight-torus coordinate map kills the upper-triangular defining ideal: a diagonal matrix
has no coordinates below the diagonal. -/
private theorem upperTriangularDefiningIdeal_le_ker_weightTorusCoordinateMap :
    (upperTriangularDefiningIdeal r).toIdeal ≤
      RingHom.ker
        (GeneralLinear.weightTorusCoordinateMap (weight r)).hom.toAlgHom.toRingHom := by
  rw [upperTriangularDefiningIdeal, HopfIdeal.sup_toIdeal]
  refine sup_le (UniversalEnvelopingAlgebra.kostantToralDefiningIdeal_toIdeal_le_torus_ker
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r))
    (GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal_le_ker ℤ (r + 1) _
      fun a b hba => ?_)
  have hzero : (GeneralLinear.weightTorusCoordinateMap (weight r)).hom
      (GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (r + 1)
        (GeneralLinear.coordinateRingMap ℤ (r + 1) (MvPolynomial.X (a, b)))) = 0 := by
    rw [GeneralLinear.weightTorusCoordinateMap_X]
    simp only [hba.ne', ↓reduceIte]
  simpa only [BialgHom.coe_toAlgHom] using hzero

/-- **The positive numbered root subgroup, factored through the upper-triangular subgroup scheme
of the type-`A_r` carrier.** -/
noncomputable def rootSubgroupUpperTriangular (i : Fin r) :
    AdditiveGroup.groupScheme ℤ ⟶ upperTriangularGroupScheme r :=
  eqToHom (AdditiveGroup.groupScheme_def ℤ) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
      (CommHopfAlgCat.liftQuotient (upperTriangularDefiningIdeal r)
        (rootCoordinateMap r (.inl i))
        (upperTriangularDefiningIdeal_le_ker_rootCoordinateMap r i)).op

/-- **The split weight torus, factored through the upper-triangular subgroup scheme of the
type-`A_r` carrier.** -/
noncomputable def weightTorusUpperTriangular :
    SplitTorus.groupScheme ℤ (Fin r) ⟶ upperTriangularGroupScheme r :=
  eqToHom (DiagonalizableGroup.groupScheme_def ℤ (SplitTorus.characterGroup (Fin r))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map
      (CommHopfAlgCat.liftQuotient (upperTriangularDefiningIdeal r)
        (GeneralLinear.weightTorusCoordinateMap (weight r))
        (upperTriangularDefiningIdeal_le_ker_weightTorusCoordinateMap r)).op

/-- Factoring a positive root subgroup through the upper-triangular subgroup and then including
into the carrier recovers the carrier's own root subgroup. -/
@[simp]
theorem rootSubgroupUpperTriangular_comp_upperTriangularInclusion (i : Fin r) :
    rootSubgroupUpperTriangular r i ≫ upperTriangularInclusion r = rootSubgroup r (.inl i) := by
  have hcoord := CommHopfAlgCat.quotientMapOfLe_comp_liftQuotient_eq
    (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
    (definingIdeal_le_upperTriangularDefiningIdeal r) (rootCoordinateMap r (.inl i))
    (upperTriangularDefiningIdeal_le_ker_rootCoordinateMap r i) _
    (UniversalEnvelopingAlgebra.mkQuotient_comp_kostantRootSubgroupToralCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r) (.inl i))
  rw [rootSubgroupUpperTriangular, upperTriangularInclusion,
    CommHopfAlgCat.quotientSpecMapOfLe_def, rootSubgroup_def,
    UniversalEnvelopingAlgebra.kostantRootSubgroupToToral_def, Category.assoc,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map_comp, ← op_comp, hcoord]

/-- Factoring the split weight torus through the upper-triangular subgroup and then including
into the carrier recovers the carrier's own weight torus. -/
@[simp]
theorem weightTorusUpperTriangular_comp_upperTriangularInclusion :
    weightTorusUpperTriangular r ≫ upperTriangularInclusion r = weightTorus r := by
  have hcoord := CommHopfAlgCat.quotientMapOfLe_comp_liftQuotient_eq
    (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1))
    (definingIdeal_le_upperTriangularDefiningIdeal r)
    (GeneralLinear.weightTorusCoordinateMap (weight r))
    (upperTriangularDefiningIdeal_le_ker_weightTorusCoordinateMap r) _
    (UniversalEnvelopingAlgebra.mkQuotient_comp_kostantWeightTorusToralCoordinateMap
      (rootGenerator r) (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
      (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r))
  rw [weightTorusUpperTriangular, upperTriangularInclusion,
    CommHopfAlgCat.quotientSpecMapOfLe_def, weightTorus_def,
    UniversalEnvelopingAlgebra.kostantWeightTorusToToral_def, Category.assoc,
    ← (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).map_comp, ← op_comp, hcoord]

end TauCeti.SlStd
