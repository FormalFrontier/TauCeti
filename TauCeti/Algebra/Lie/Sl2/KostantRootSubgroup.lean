/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.IntegralLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# Kostant root subgroups for the standard `sl₂` representation

This file supplies a concrete rank-one witness for the general Kostant root-step criterion. Both
roots in the standard two-dimensional `sl₂` representation have a unit root step on the integral
coordinate lattice, so both resulting root-subgroup morphisms are closed immersions.

## Main declarations

* `TauCeti.Sl2Std.integralLatticeAddSubgroupBasis`: the coordinate basis of the standard integral
  lattice, viewed as an additive subgroup.
* `TauCeti.Sl2Std.isNilpotent_representation_root`: both root operators are nilpotent.
* `TauCeti.Sl2Std.exists_unit_rootStep_representation_one`: both root operators have a unit root
  step on the two-dimensional integral lattice.
* `TauCeti.Sl2Std.isClosedImmersion_kostantRootSubgroup_one`: both associated root subgroups are
  closed immersions.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.Sl2Std

open TauCeti.UniversalEnvelopingAlgebra

local notation "e" => ![slFinTwoBasis ℚ 0, slFinTwoBasis ℚ 1]
local notation "h" => ![slFinTwoBasis ℚ 2]
local notation "ρ" => TauCeti.UniversalEnvelopingAlgebra.representation ℚ
  (LieAlgebra.SpecialLinear.sl (Fin 2) ℚ) (Sl2Std ℚ 1)

/-- The coordinate basis of the standard integral `sl₂` lattice, viewed through its underlying
additive subgroup as required by the Kostant root-subgroup construction. -/
noncomputable def integralLatticeAddSubgroupBasis (n : ℕ) :
    Module.Basis (Fin (n + 1)) ℤ (integralLattice n).toAddSubgroup :=
  (Pi.basisFun ℤ (Fin (n + 1))).map (integerCoordinatesLinearEquiv n)

/-- The integral-lattice coordinate basis has the expected underlying rational basis vectors. -/
@[simp]
theorem coe_integralLatticeAddSubgroupBasis_apply (n : ℕ) (i : Fin (n + 1)) :
    ((integralLatticeAddSubgroupBasis n i : (integralLattice n).toAddSubgroup) :
      Sl2Std ℚ n) = basis ℚ n i := by
  rw [integralLatticeAddSubgroupBasis, Module.Basis.coe_map]
  funext j
  simp only [Function.comp_apply]
  rw [coe_integerCoordinatesLinearEquiv_apply]
  classical
  by_cases hji : j = i
  · subst j
    simp [Pi.basisFun_apply, basis_apply]
  · simp [Pi.basisFun_apply, basis_apply, hji]

local notation "b" => integralLatticeAddSubgroupBasis 1

/-- Both root operators in the standard two-dimensional `sl₂` representation are nilpotent. -/
theorem isNilpotent_representation_root (i : Fin 2) :
    IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) := by
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
      Matrix.cons_val_zero]
    rw [representation_ι_slFinTwoBasis (n := 1) 0]
    exact ⟨2, raise_pow_eq_zero⟩
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [representation_ι_slFinTwoBasis (n := 1) 1]
    exact ⟨2, lower_pow_eq_zero⟩

/-- Every root operator in the standard two-dimensional `sl₂` representation has a unit root
step on the integral coordinate basis. For the raising operator the step is `v₁ ↦ v₀`; for
the lowering operator it is `v₀ ↦ v₁`. -/
theorem exists_unit_rootStep_representation_one (i : Fin 2) :
    ∃ r s : Fin 2, ∃ c : ℤ, IsUnit c ∧
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : Sl2Std ℚ 1) =
        c • (b r : Sl2Std ℚ 1) ∧
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : Sl2Std ℚ 1)) = 0 := by
  fin_cases i
  · refine ⟨0, 1, 1, isUnit_one, ?_, ?_⟩
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero]
      rw [representation_ι_slFinTwoBasis,
        coe_integralLatticeAddSubgroupBasis_apply,
        coe_integralLatticeAddSubgroupBasis_apply]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, one_smul]
      rw [raise_basis]
      norm_num
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero]
      rw [representation_ι_slFinTwoBasis,
        coe_integralLatticeAddSubgroupBasis_apply]
      have hz := DFunLike.congr_fun (raise_pow_eq_zero (K := ℚ) (n := 1)) (basis ℚ 1 1)
      simpa [pow_two, Module.End.mul_apply] using hz
  · refine ⟨1, 0, 1, isUnit_one, ?_, ?_⟩
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [representation_ι_slFinTwoBasis,
        coe_integralLatticeAddSubgroupBasis_apply,
        coe_integralLatticeAddSubgroupBasis_apply]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, one_smul]
      rw [lower_basis _ (by norm_num)]
      norm_num
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [representation_ι_slFinTwoBasis,
        coe_integralLatticeAddSubgroupBasis_apply]
      have hz := DFunLike.congr_fun (lower_pow_eq_zero (K := ℚ) (n := 1)) (basis ℚ 1 0)
      simpa [pow_two, Module.End.mul_apply] using hz

/-- Both Kostant root subgroups in the standard two-dimensional integral `sl₂` representation
are closed immersions. This is a nondegenerate instance of the general root-step criterion. -/
theorem isClosedImmersion_kostantRootSubgroup_one (i : Fin 2) :
    IsClosedImmersion
      (kostantRootSubgroup e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i
        (isNilpotent_representation_root i) b).hom.hom.left := by
  obtain ⟨r, s, c, hc, hstep, hsq⟩ := exists_unit_rootStep_representation_one i
  exact isClosedImmersion_kostantRootSubgroup e h ρ (integralLattice 1).toAddSubgroup
    (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_representation_root i) b
    hc hstep hsq

end TauCeti.Sl2Std
