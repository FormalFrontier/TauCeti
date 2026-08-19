/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.RootSubgroup
public import TauCeti.Algebra.Lie.Sl2.KostantRootSubgroup
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Points
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The rank-one Kostant elementary group on field-valued points

This file identifies the elementary group obtained by applying the Kostant construction to the
standard two-dimensional representation of `sl₂` with the determinant-one matrices.  Its two
Kostant root subgroups are the upper and lower elementary transvections, and those transvections
generate `SL₂` over every field.

## Main declarations

* `TauCeti.Sl2Std.rootTransvection`: the determinant-one transvection indexed by either root.
* `TauCeti.Sl2Std.kostantRootSubgroupMatrix_eq_rootTransvectionGL`: the two Kostant root
  subgroups are the standard upper and lower root subgroups of `SL₂`.
* `TauCeti.Sl2Std.map_kostantElementarySubgroup_eq_range_toGL`: over a field, the standard
  rank-one Kostant elementary group is exactly the image of `SL₂` in `GL₂`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 8.2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

This verifies the elementary-group side of the rank-one point-generation case of Layer 9,
"pinned Chevalley--Demazure group schemes over `ℤ`", of
`TauCetiRoadmap/ReductiveGroups/README.md`.  Together with the general containment theorem, it
places every `SL₂` point inside the points of the constructed group scheme; identifying that
scheme with the standard special-linear scheme is a separate scheme-theoretic step.
-/

public section

open TensorProduct WithConv

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => repEnveloping ℚ 1
local notation "b" => integralLatticeAddSubgroupBasis 1
local notation "hnil" => isNilpotent_repEnveloping_root

/-- The other coordinate of `Fin 2`, used as the column of the root transvection whose row is
`i`. -/
def other (i : Fin 2) : Fin 2 := ![1, 0] i

/-- A coordinate of `Fin 2` differs from the other coordinate. -/
theorem ne_other (i : Fin 2) : i ≠ other i := by
  fin_cases i <;> simp [other]

/-- The standard determinant-one root element indexed by either root of `sl₂`.  Index `0` is
the upper transvection and index `1` is the lower transvection. -/
def rootTransvection {A : Type*} [CommRing A] (i : Fin 2) (t : A) :
    Matrix.SpecialLinearGroup (Fin 2) A :=
  Matrix.SpecialLinearGroup.transvection (ne_other i) t

/-- The standard root element, viewed in `GL₂`. -/
def rootTransvectionGL {A : Type*} [CommRing A] (i : Fin 2) (t : A) :
    Matrix.GeneralLinearGroup (Fin 2) A :=
  TauCeti.transvectionUnit (ne_other i) t

/-- Including a determinant-one root element into `GL₂` gives the corresponding general-linear
transvection. -/
@[simp]
theorem toGL_rootTransvection {A : Type*} [CommRing A] (i : Fin 2) (t : A) :
    Matrix.SpecialLinearGroup.toGL (rootTransvection i t) = rootTransvectionGL i t := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  change (rootTransvection i t).1 r s =
    (TauCeti.transvectionUnit (ne_other i) t).1 r s
  rw [TauCeti.coe_transvectionUnit]
  rfl

private theorem nilpotencyClass_repEnveloping_root (i : Fin 2) :
    nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) = 2 := by
  apply nilpotencyClass_eq_succ_iff.mpr
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [repEnveloping_ι_slFinTwoBasis]
    constructor
    · exact raise_pow_eq_zero
    · rw [pow_one]
      intro he
      have hz := DFunLike.congr_fun he (basis ℚ 1 1)
      exact (basis ℚ 1).ne_zero 0 (by simpa [raise_basis] using hz)
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [repEnveloping_ι_slFinTwoBasis]
    constructor
    · exact lower_pow_eq_zero
    · rw [pow_one]
      intro he
      have hz := DFunLike.congr_fun he (basis ℚ 1 0)
      exact (basis ℚ 1).ne_zero 1 (by simpa [lower_basis] using hz)

private theorem integralDividedPower_one_apply_basis (i s : Fin 2) :
    integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
        (integralLattice 1).toAddSubgroup 1
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ
          (kostantForm_apply_mem_integralLattice 1) i 1 hv) (b s) =
      if s = other i then b i else 0 := by
  apply Subtype.ext
  rw [coe_integralDividedPower_apply, Associative.dividedPower_one]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [repEnveloping_ι_slFinTwoBasis]
    fin_cases s <;>
      simp [other, coe_integralLatticeAddSubgroupBasis_apply, raise_basis]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [repEnveloping_ι_slFinTwoBasis]
    fin_cases s
    · simp [other, coe_integralLatticeAddSubgroupBasis_apply, lower_basis]
    · simp only [other, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      funext j
      fin_cases j <;>
        simp [coe_integralLatticeAddSubgroupBasis_apply, lower_apply, basis_apply]

/-- The matrix of either rank-one Kostant root-subgroup element is the corresponding standard
determinant-one transvection. -/
theorem kostantRootSubgroupMatrix_eq_rootTransvectionGL
    {A : Type*} [CommRing A] (i : Fin 2) (t : Multiplicative A) :
    kostantRootSubgroupMatrix e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i (hnil i) b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) =
      rootTransvectionGL i (Multiplicative.toAdd t) := by
  rw [← toGL_rootTransvection]
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  change _ = (rootTransvection i (Multiplicative.toAdd t)).1 r s
  rw [kostantRootSubgroupMatrix_apply]
  simp only [rootTransvection, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rw [Module.Basis.baseChange_apply, kostantRootSubgroupPoints_tmul,
    nilpotencyClass_repEnveloping_root]
  rw [Finset.sum_range_succ, Finset.sum_range_one,
    integralDividedPower_one_apply_basis]
  fin_cases i <;> fin_cases r <;> fin_cases s
  all_goals
    simp [other, integralDividedPower_zero]

/-- Every standard rank-one root transvection belongs to the matrix image of the Kostant
elementary group, over an arbitrary commutative ring. -/
theorem rootTransvectionGL_mem_map_kostantElementarySubgroup
    (A : Type) [CommRing A] (i : Fin 2) (t : A) :
    rootTransvectionGL i t ∈
      (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) hnil (CommAlgCat.of ℤ A)).map
          (Units.map (LinearMap.toMatrixAlgEquiv
            ((b).baseChange A)).toMonoidHom) := by
  let u := kostantRootSubgroupParam e h ρ (integralLattice 1).toAddSubgroup
    (kostantForm_apply_mem_integralLattice 1) i (hnil i) (CommAlgCat.of ℤ A)
      (Multiplicative.ofAdd t)
  refine ⟨u, kostantRootSubgroupParam_mem_kostantElementarySubgroup
    e h ρ (integralLattice 1).toAddSubgroup
      (kostantForm_apply_mem_integralLattice 1) hnil (CommAlgCat.of ℤ A) i
        (Multiplicative.ofAdd t), ?_⟩
  change Units.map (LinearMap.toMatrixAlgEquiv
      ((b).baseChange A)).toMonoidHom
        (kostantRootSubgroupParam e h ρ (integralLattice 1).toAddSubgroup
          (kostantForm_apply_mem_integralLattice 1) i (hnil i) (CommAlgCat.of ℤ A)
            (Multiplicative.ofAdd t)) = rootTransvectionGL i t
  calc
    _ = kostantRootSubgroupMatrix e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i (hnil i) b
          ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
            (Multiplicative.ofAdd t)) := by
      exact basisMatrix_kostantRootSubgroupParam e h ρ
        (integralLattice 1).toAddSubgroup (kostantForm_apply_mem_integralLattice 1)
          hnil b A i (Multiplicative.ofAdd t)
    _ = _ := kostantRootSubgroupMatrix_eq_rootTransvectionGL i (Multiplicative.ofAdd t)

/-- **The rank-one elementary-group identification for the Kostant construction.** Over a field, the
matrix image of the elementary group constructed from the standard two-dimensional `sl₂` lattice
is exactly the image of `SL₂` in `GL₂`.

The forward inclusion is the explicit divided-power calculation above.  The reverse inclusion
uses Mathlib's `Matrix.SL2.transvection_induction`, which says that the two determinant-one root
subgroups generate `SL₂` over a field. -/
theorem map_kostantElementarySubgroup_eq_range_toGL (F : Type) [Field F] :
    (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
      (kostantForm_apply_mem_integralLattice 1) hnil (CommAlgCat.of ℤ F)).map
        (Units.map (LinearMap.toMatrixAlgEquiv
          ((b).baseChange (CommAlgCat.of ℤ F))).toMonoidHom) =
      Matrix.SpecialLinearGroup.toGL.range := by
  apply le_antisymm
  · rw [kostantElementarySubgroup_eq_closure, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, t, rfl⟩ := by
      simpa only [Set.mem_iUnion, Set.mem_range] using hx
    have hmatrix :
        Units.map (LinearMap.toMatrixAlgEquiv
          ((b).baseChange (CommAlgCat.of ℤ F))).toMonoidHom
            (kostantRootSubgroupParam e h ρ (integralLattice 1).toAddSubgroup
              (kostantForm_apply_mem_integralLattice 1) i (hnil i)
                (CommAlgCat.of ℤ F) t) = rootTransvectionGL i (Multiplicative.toAdd t) := by
      calc
        _ = kostantRootSubgroupMatrix e h ρ (integralLattice 1).toAddSubgroup
            (kostantForm_apply_mem_integralLattice 1) i (hnil i) b
              ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := F)).symm t) := by
          exact basisMatrix_kostantRootSubgroupParam e h ρ
            (integralLattice 1).toAddSubgroup
              (kostantForm_apply_mem_integralLattice 1) hnil b F i t
        _ = _ := kostantRootSubgroupMatrix_eq_rootTransvectionGL i t
    rw [hmatrix, ← toGL_rootTransvection]
    exact ⟨rootTransvection i (Multiplicative.toAdd t), rfl⟩
  · rintro _ ⟨g, rfl⟩
    apply Matrix.SL2.transvection_induction
      (fun s => Matrix.SpecialLinearGroup.toGL s ∈
        (kostantElementarySubgroup e h ρ (integralLattice 1).toAddSubgroup
          (kostantForm_apply_mem_integralLattice 1) hnil (CommAlgCat.of ℤ F)).map
            (Units.map (LinearMap.toMatrixAlgEquiv
              ((b).baseChange (CommAlgCat.of ℤ F))).toMonoidHom))
    · intro i j hij t
      fin_cases i
      · obtain rfl : j = 1 := by fin_cases j <;> tauto
        change Matrix.SpecialLinearGroup.toGL (rootTransvection 0 t) ∈ _
        rw [toGL_rootTransvection]
        exact rootTransvectionGL_mem_map_kostantElementarySubgroup F 0 t
      · obtain rfl : j = 0 := by fin_cases j <;> tauto
        change Matrix.SpecialLinearGroup.toGL (rootTransvection 1 t) ∈ _
        rw [toGL_rootTransvection]
        exact rootTransvectionGL_mem_map_kostantElementarySubgroup F 1 t
    · intro g g' hg hg'
      simpa only [map_mul] using mul_mem hg hg'

end TauCeti.Sl2Std
