/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Kostant.RootSubgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Points
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The rank-one Kostant elementary group on field-valued points

This file identifies the elementary group obtained by applying the Kostant construction to the
standard two-dimensional representation of `sl₂` with the determinant-one matrices.  Over an
arbitrary commutative ring its two Kostant root subgroups are the upper and lower elementary
transvections `TauCeti.transvectionUnit`, so the elementary group always lies in the image of
`SL₂`; only the reverse inclusion needs a field, where those transvections generate `SL₂`.

## Main declarations

* `TauCeti.Sl2Std.kostantRootSubgroupMatrix_eq_transvectionUnit` and
  `TauCeti.Sl2Std.map_kostantRootSubgroupParam_eq_transvectionUnit`: over any commutative ring the
  two Kostant root subgroups are the standard upper and lower root subgroups of `SL₂`, in matrix
  and in parameter form.
* `TauCeti.Sl2Std.transvectionUnit_mem_map_kostantElementarySubgroup` and
  `TauCeti.Sl2Std.map_kostantElementarySubgroup_le_range_toGL`: over any commutative ring the
  standard transvections lie in the matrix image of the Kostant elementary group, and that image
  lies in the image of `SL₂`.
* `TauCeti.Sl2Std.map_kostantElementarySubgroup_eq_range_toGL`: over a field, the standard
  rank-one Kostant elementary group is exactly the image of `SL₂` in `GL₂`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 8.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

This verifies the elementary-group side of the rank-one point-generation case of Layer 9,
"pinned Chevalley--Demazure group schemes over `ℤ`", of
`TauCetiRoadmap/ReductiveGroups/README.md`.  Together with
`TauCeti.UniversalEnvelopingAlgebra.map_kostantElementarySubgroup_le_generatedPoints`, it places
every `SL₂` point inside the points of the constructed group scheme; identifying that scheme with
the standard special-linear scheme is a separate scheme-theoretic step.
-/

public section

open TensorProduct WithConv

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => repEnveloping ℚ 1
local notation "b" => integralLatticeAddSubgroupBasis 1

private theorem toGL_transvection_eq_transvectionUnit {A : Type*} [CommRing A]
    {i j : Fin 2} (hij : i ≠ j) (t : A) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) =
      TauCeti.transvectionUnit hij t := by
  -- `transvectionUnit` is opaque outside its defining module, whose public coercion equation is
  -- `coe_transvectionUnit`; compare the two `GL₂` elements through their underlying matrices.
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [TauCeti.coe_transvectionUnit]
  rfl

private theorem kostantRootSubgroupMatrix_apply_rankOne {A : Type*} [CommRing A]
    (i r s : Fin 2) (t : Multiplicative A) :
    kostantRootSubgroupMatrix e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_repEnveloping_root ℚ 1 i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) r s =
      Matrix.transvection i i.rev (Multiplicative.toAdd t) r s := by
  rw [kostantRootSubgroupMatrix_apply,
    kostantRootSubgroupPoints_apply_baseChange_basis_one]
  simp only [map_add, Module.Basis.repr_self, Finsupp.add_apply, MulEquiv.apply_symm_apply,
    Matrix.transvection, Matrix.add_apply]
  fin_cases i <;> fin_cases r <;> fin_cases s <;> simp

/-- **The rank-one Kostant root subgroups are the standard transvections.** The matrix of a
Kostant root-subgroup element for the root `i` is the determinant-one transvection at the index
pair `(i, i.rev)`, over an arbitrary commutative ring. -/
theorem kostantRootSubgroupMatrix_eq_transvectionUnit {A : Type*} [CommRing A]
    (i : Fin 2) (t : Multiplicative A) :
    kostantRootSubgroupMatrix e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_repEnveloping_root ℚ 1 i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) =
      TauCeti.transvectionUnit (i := i) (j := i.rev) (by fin_cases i <;> decide)
        (Multiplicative.toAdd t) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  simpa only [TauCeti.coe_transvectionUnit] using
    kostantRootSubgroupMatrix_apply_rankOne i r s t

/-- In basis coordinates a rank-one Kostant root-subgroup parameter value is the standard
transvection of the same parameter. -/
theorem map_kostantRootSubgroupParam_eq_transvectionUnit (A : Type) [CommRing A]
    (i : Fin 2) (t : Multiplicative A) :
    Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange A)).toMulEquiv
        (kostantRootSubgroupParam e h ρ (integralLattice 1).toAddSubgroup
          (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_repEnveloping_root ℚ 1 i)
            (CommAlgCat.of ℤ A) t) =
      TauCeti.transvectionUnit (i := i) (j := i.rev) (by fin_cases i <;> decide)
        (Multiplicative.toAdd t) := by
  rw [basisMatrix_kostantRootSubgroupParam e h ρ (integralLattice 1).toAddSubgroup
      (kostantForm_apply_mem_integralLattice 1) (isNilpotent_repEnveloping_root ℚ 1) b A i t,
    kostantRootSubgroupMatrix_eq_transvectionUnit]

/-- Every standard rank-one transvection belongs to the matrix image of the Kostant elementary
group, over an arbitrary commutative ring. -/
theorem transvectionUnit_mem_map_kostantElementarySubgroup
    (A : Type) [CommRing A] {i j : Fin 2} (hij : i ≠ j) (t : A) :
    TauCeti.transvectionUnit hij t ∈
      (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) (isNilpotent_repEnveloping_root ℚ 1)
          (CommAlgCat.of ℤ A)).map
          (Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange A)).toMulEquiv) := by
  obtain rfl : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨_, kostantRootSubgroupParam_mem_kostantElementarySubgroup e h ρ
      (integralLattice 1).toAddSubgroup (kostantForm_apply_mem_integralLattice 1)
        (isNilpotent_repEnveloping_root ℚ 1) (CommAlgCat.of ℤ A) i (Multiplicative.ofAdd t),
    map_kostantRootSubgroupParam_eq_transvectionUnit A i (Multiplicative.ofAdd t)⟩

/-- Over an arbitrary commutative ring the matrix image of the standard rank-one Kostant
elementary group lies in the image of `SL₂` in `GL₂`: it is generated by transvections, which have
determinant one. -/
theorem map_kostantElementarySubgroup_le_range_toGL (A : Type) [CommRing A] :
    (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
      (kostantForm_apply_mem_integralLattice 1) (isNilpotent_repEnveloping_root ℚ 1)
        (CommAlgCat.of ℤ A)).map
        (Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange A)).toMulEquiv) ≤
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := A)).range := by
  refine map_kostantElementarySubgroup_le_of_matrix_mem e h ρ
    (integralLattice 1).toAddSubgroup (kostantForm_apply_mem_integralLattice 1)
      (isNilpotent_repEnveloping_root ℚ 1) b A fun i q => ?_
  have hrev : i ≠ i.rev := by fin_cases i <;> decide
  rw [← (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm_apply_apply q,
    kostantRootSubgroupMatrix_eq_transvectionUnit]
  exact ⟨_, toGL_transvection_eq_transvectionUnit hrev _⟩

/-- **The rank-one elementary-group identification for the Kostant construction.** Over a field,
the matrix image of the elementary group constructed from the standard two-dimensional `sl₂`
lattice is exactly the image of `SL₂` in `GL₂`. -/
theorem map_kostantElementarySubgroup_eq_range_toGL (F : Type) [Field F] :
    (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
      (kostantForm_apply_mem_integralLattice 1) (isNilpotent_repEnveloping_root ℚ 1)
        (CommAlgCat.of ℤ F)).map
        (Units.map (LinearMap.toMatrixAlgEquiv ((b).baseChange F)).toMulEquiv) =
      (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := F)).range := by
  refine le_antisymm (map_kostantElementarySubgroup_le_range_toGL F) ?_
  rintro _ ⟨g, rfl⟩
  -- Over a field the transvections at the two off-diagonal positions generate `SL₂`, so the
  -- reverse inclusion follows from `Matrix.SL2.transvection_induction`.
  induction g using Matrix.SL2.transvection_induction with
  | htransvec i j hij t =>
    rw [toGL_transvection_eq_transvectionUnit hij]
    exact transvectionUnit_mem_map_kostantElementarySubgroup F hij t
  | hmul g g' hg hg' => simpa only [map_mul] using mul_mem hg hg'

end TauCeti.Sl2Std
