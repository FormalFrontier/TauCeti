/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.UpperTriangular.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne

/-!
# Upper-triangular points of the type-A full-weight carrier

The full-weight type-`A_r` carrier is an explicit closed subgroup scheme of `GL_(r+1)`.  This file
intersects it scheme-theoretically with the standard upper-triangular subgroup scheme of `GL_(r+1)`.
On coordinate Hopf algebras, intersection is the join of the two defining Hopf ideals.  The
resulting `TauCeti.SlStd.upperTriangularGroupScheme` is therefore a closed subgroup scheme of the
actual Chevalley carrier, not a separately chosen matrix group.

Over every commutative value ring `A`, its embedded matrix points are exactly

```text
SlStd.points r A ∩ upperTriangularGroup (Fin (r + 1)) A.
```

The named split torus and every positive simple-root subgroup lie in this intersection.  A
negative simple-root point lies in it exactly when its parameter is zero.  Thus the construction
selects the positive half of the carrier's pinning rather than merely containing all of its
generators.

No maximal-solvability assertion is made here.  Identifying this closed subgroup as a Borel and
the named split torus as maximal requires the reductivity and root-datum structure of the carrier.

## Main definitions

* `TauCeti.SlStd.upperTriangularDefiningIdeal`: the join of the carrier and upper-triangular
  defining Hopf ideals.
* `TauCeti.SlStd.upperTriangularGroupScheme`: the corresponding closed subgroup scheme.
* `TauCeti.SlStd.upperTriangularInclusion`: its closed immersion into the type-`A` carrier.
* `TauCeti.SlStd.upperTriangularPoints`: its matrix points inside `GL_(r+1)`.

## Main results

* `TauCeti.SlStd.upperTriangularPoints_eq`: the point group is the intersection of the carrier
  points with the upper-triangular matrices.
* `TauCeti.SlStd.rootSubgroupPoints_inl_mem_upperTriangularPoints`: every positive numbered root
  subgroup lies in the intersection.
* `TauCeti.SlStd.rootSubgroupPoints_inr_mem_upperTriangularPoints_iff`: a negative numbered root
  subgroup meets it only at the identity.
* `TauCeti.SlStd.weightTorusPoints_mem_upperTriangularPoints`: the split weight torus lies in the
  intersection.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--28.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Sections 3--4.

This advances the "Pinnings" target of Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`: it constructs the closed positive subgroup containing
the torus and positive simple-root subgroups for the explicit type-`A` carrier.  Milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md` consumes that pinned carrier.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.SlStd

universe v

variable (r : ℕ)

/-! ## The scheme-theoretic intersection -/

/-- The defining Hopf ideal of the full-weight type-`A_r` carrier, named in the ambient
coordinate Hopf algebra of `GL_(r+1)`. -/
noncomputable abbrev definingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (r + 1)) :=
  UniversalEnvelopingAlgebra.kostantToralDefiningIdeal (rootGenerator r)
    (cartanGenerator r) (rep r) (lattice r).toAddSubgroup
    (fun _ hu _ hv => rep_kostantForm_mem_lattice r hu hv)
    (isNilpotent_rep_rootGenerator r) (latticeBasis r) (weight r)

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

/-- The underlying ideal of the upper-triangular carrier is the join of the two underlying
defining ideals. -/
@[simp]
theorem upperTriangularDefiningIdeal_toIdeal :
    (upperTriangularDefiningIdeal r).toIdeal =
      (definingIdeal r).toIdeal ⊔
        Ideal.span (GeneralLinear.UpperTriangular.definingRelationSet ℤ (r + 1)) := by
  rw [upperTriangularDefiningIdeal, HopfIdeal.sup_toIdeal,
    GeneralLinear.UpperTriangular.definingHopfIdeal_toIdeal]

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

/-! ## Matrix points -/

/-- The matrix points of the upper-triangular subgroup scheme of the type-`A_r` carrier. -/
noncomputable def upperTriangularPoints (A : Type v) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin (r + 1)) A) :=
  GeneralLinear.hopfIdealPointsSubgroup (r + 1) (upperTriangularDefiningIdeal r) A

/-- **The upper-triangular points of the carrier are the intersection of the carrier points and
the invertible upper-triangular matrices.** -/
theorem upperTriangularPoints_eq (A : Type v) [CommRing A] :
    upperTriangularPoints r A =
      points r A ⊓ upperTriangularGroup (Fin (r + 1)) A := by
  ext g
  rw [upperTriangularPoints, upperTriangularDefiningIdeal,
    GeneralLinear.mem_hopfIdealPointsSubgroup_iff, Subgroup.mem_inf, mem_points_iff,
    UpperTriangularGroup.mem_iff]
  have hupper :
      (∀ x ∈ GeneralLinear.UpperTriangular.definingHopfIdeal ℤ (r + 1),
          ((GeneralLinear.pointsMulEquiv (R := ℤ) (r + 1)).symm g).ofConv x = 0) ↔
        (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
    rw [← GeneralLinear.mem_hopfIdealPointsSubgroup_iff,
      GeneralLinear.UpperTriangular.hopfIdealPointsSubgroup_eq,
      UpperTriangularGroup.mem_iff]
  constructor
  · intro hg
    refine ⟨fun x hx ↦ hg x (Ideal.mem_sup_left hx), hupper.mp ?_⟩
    exact fun x hx ↦ hg x (Ideal.mem_sup_right hx)
  · rintro ⟨hcarrier, htri⟩ x hx
    have hu := hupper.mpr htri
    obtain ⟨y, hy, z, hz, rfl⟩ := HopfIdeal.mem_sup.mp hx
    rw [map_add, hcarrier y hy, hu z hz, add_zero]

/-- Membership in the upper-triangular carrier points means carrier membership together with
upper triangularity of the underlying matrix. -/
@[simp]
theorem mem_upperTriangularPoints_iff
    (A : Type v) [CommRing A] (g : Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
    g ∈ upperTriangularPoints r A ↔
      g ∈ points r A ∧ (g : Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsUpperTriangular := by
  rw [upperTriangularPoints_eq, Subgroup.mem_inf, UpperTriangularGroup.mem_iff]

/-! ## The positive pinning lies in the intersection -/

/-- Every positive numbered root-subgroup point belongs to the upper-triangular subgroup of the
type-`A_r` carrier. -/
theorem rootSubgroupPoints_inl_mem_upperTriangularPoints
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    (rootSubgroupPoints r (.inl i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
      upperTriangularPoints r A := by
  rw [mem_upperTriangularPoints_iff]
  refine ⟨(rootSubgroupPoints r (.inl i) A u).property, ?_⟩
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection,
    MulEquiv.apply_symm_apply, coe_transvectionUnit]
  simp only [rootTarget_inl, rootSource_inl]
  -- `IsUpperTriangular` hides the two matrix indices as implicit `BlockTriangular` arguments.
  change ∀ ⦃a b : Fin (r + 1)⦄, b < a → Matrix.transvection i.castSucc i.succ
    (Multiplicative.toAdd u) a b = 0
  intro a b hba
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  simp only [hba.ne', ↓reduceIte, zero_add]
  split
  · rename_i h
    obtain ⟨rfl, rfl⟩ := h
    exact (lt_asymm (Fin.castSucc_lt_succ (i := i)) hba).elim
  · rfl

/-- A negative numbered root-subgroup point is upper triangular exactly when its parameter is
zero.  In particular, the intersection selects the positive, rather than both, halves of the
pinning. -/
theorem rootSubgroupPoints_inr_mem_upperTriangularPoints_iff
    (A : Type v) [CommRing A] (i : Fin r) (u : Multiplicative A) :
    (rootSubgroupPoints r (.inr i) A u : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
        upperTriangularPoints r A ↔
      Multiplicative.toAdd u = 0 := by
  rw [mem_upperTriangularPoints_iff]
  constructor
  · rintro ⟨_, htri⟩
    have hzero := htri (i := i.succ) (j := i.castSucc) (Fin.castSucc_lt_succ (i := i))
    rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection,
      MulEquiv.apply_symm_apply, coe_transvectionUnit] at hzero
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      rootTarget_inr, rootSource_inr, (Fin.castSucc_lt_succ (i := i)).ne', ↓reduceIte,
      zero_add] at hzero
    exact hzero
  · intro hu
    refine ⟨(rootSubgroupPoints r (.inr i) A u).property, ?_⟩
    rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection,
      MulEquiv.apply_symm_apply, hu,
      transvectionUnit_zero]
    exact Matrix.blockTriangular_one

/-- Every point of the named split weight torus belongs to the upper-triangular subgroup of the
type-`A_r` carrier. -/
theorem weightTorusPoints_mem_upperTriangularPoints
    (A : Type v) [CommRing A] (s : Fin r → Aˣ) :
    (weightTorusPoints r A s : Matrix.GeneralLinearGroup (Fin (r + 1)) A) ∈
      upperTriangularPoints r A := by
  rw [mem_upperTriangularPoints_iff]
  refine ⟨(weightTorusPoints r A s).property, ?_⟩
  rw [coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  -- Expose the implicit row and column of `BlockTriangular` after rewriting to a diagonal matrix.
  change ∀ ⦃i j : Fin (r + 1)⦄, j < i →
    Matrix.diagonal (fun k ↦ (torusCharacter s (weight r k) : A)) i j = 0
  intro i j hji
  exact Matrix.diagonal_apply_ne _ hji.ne'

end TauCeti.SlStd
