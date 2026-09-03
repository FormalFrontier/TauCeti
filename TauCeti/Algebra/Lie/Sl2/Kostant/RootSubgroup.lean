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
* `TauCeti.Sl2Std.repEnveloping_root_apply_basis`: each root operator maps one coordinate basis
  vector to the other and annihilates the remaining vector.
* `TauCeti.Sl2Std.kostantRootSubgroupPoints_apply_baseChange_basis_one`: the resulting class-two
  root-subgroup action on the base-changed coordinate basis.
* `TauCeti.Sl2Std.nilpotencyClass_repEnveloping_root`: both root operators are nilpotent of
  class exactly two.
* `TauCeti.Sl2Std.exists_unit_rootStep_repEnveloping_one`: both root operators have a unit root
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
local notation "ρ" => repEnveloping ℚ 1

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

/-- **Each root operator maps one integral basis vector to the other.** In the standard
two-dimensional `sl₂` representation the raising operator sends `v₁` to `v₀` and kills `v₀`, and
the lowering operator sends `v₀` to `v₁` and kills `v₁`; both index changes are `Fin.rev`. -/
theorem repEnveloping_root_apply_basis (i s : Fin 2) :
    ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : Sl2Std ℚ 1) =
      if s = i.rev then (b i : Sl2Std ℚ 1) else 0 := by
  fin_cases i
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
      Matrix.cons_val_zero]
    rw [repEnveloping_ι_slFinTwoBasis]
    fin_cases s <;> simp [coe_integralLatticeAddSubgroupBasis_apply, raise_basis]
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [repEnveloping_ι_slFinTwoBasis]
    fin_cases s
    · simp [coe_integralLatticeAddSubgroupBasis_apply, lower_basis]
    · simpa [coe_integralLatticeAddSubgroupBasis_apply] using lower_basis_last (K := ℚ) (n := 1)

/-- Both root operators in the standard two-dimensional `sl₂` representation are nilpotent of
class exactly two: their square vanishes, and they are themselves nonzero. -/
theorem nilpotencyClass_repEnveloping_root (i : Fin 2) :
    nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) = 2 := by
  refine nilpotencyClass_eq_succ_iff.mpr ⟨?_, ?_⟩
  · fin_cases i
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.zero_eta,
        Matrix.cons_val_zero]
      rw [repEnveloping_ι_slFinTwoBasis]
      exact raise_pow_eq_zero
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [repEnveloping_ι_slFinTwoBasis]
      exact lower_pow_eq_zero
  · rw [pow_one]
    intro hzero
    have hz := DFunLike.congr_fun hzero (b i.rev : Sl2Std ℚ 1)
    rw [repEnveloping_root_apply_basis, ite_eq_left rfl,
      coe_integralLatticeAddSubgroupBasis_apply] at hz
    exact (basis ℚ 1).ne_zero i hz

private theorem integralDividedPower_one_apply_basis (i s : Fin 2) :
    integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
        (integralLattice 1).toAddSubgroup 1
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ
          (kostantForm_apply_mem_integralLattice 1) i 1 hv) (b s) =
      if s = i.rev then b i else 0 := by
  apply Subtype.ext
  rw [coe_integralDividedPower_apply, Associative.dividedPower_one, Module.End.smul_def,
    repEnveloping_root_apply_basis]
  split <;> simp

/-- A rank-one Kostant root-subgroup point acts on the base-changed integral basis by the
class-two formula `v_s ↦ v_s + t v_i` when `s = i.rev`, and fixes `v_s` otherwise. -/
theorem kostantRootSubgroupPoints_apply_baseChange_basis_one {A : Type*} [CommRing A]
    (i s : Fin 2) (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupPoints e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_repEnveloping_root ℚ 1 i) f).val
        ((b).baseChange A s) =
      (b).baseChange A s + if s = i.rev then
        Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f) • (b).baseChange A i else 0 := by
  rw [Module.Basis.baseChange_apply, kostantRootSubgroupPoints_tmul,
    nilpotencyClass_repEnveloping_root, Finset.sum_range_succ, Finset.sum_range_one,
    integralDividedPower_zero, integralDividedPower_one_apply_basis]
  split <;> simp [smul_tmul']

/-- Every root operator in the standard two-dimensional `sl₂` representation has a unit root
step on the integral coordinate basis. For the raising operator the step is `v₁ ↦ v₀`; for
the lowering operator it is `v₀ ↦ v₁`. -/
theorem exists_unit_rootStep_repEnveloping_one (i : Fin 2) :
    ∃ r s : Fin 2, ∃ c : ℤ, IsUnit c ∧
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : Sl2Std ℚ 1) =
        c • (b r : Sl2Std ℚ 1) ∧
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
        (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) (b s : Sl2Std ℚ 1)) = 0 := by
  have hrev : i ≠ i.rev := by fin_cases i <;> decide
  refine ⟨i, i.rev, 1, isUnit_one, ?_, ?_⟩
  · rw [repEnveloping_root_apply_basis, ite_eq_left rfl, one_smul]
  · rw [repEnveloping_root_apply_basis, ite_eq_left rfl, repEnveloping_root_apply_basis,
      ite_eq_right hrev]

/-- Both Kostant root subgroups in the standard two-dimensional integral `sl₂` representation
are closed immersions. This is a nondegenerate instance of the general root-step criterion. -/
theorem isClosedImmersion_kostantRootSubgroup_one (i : Fin 2) :
    IsClosedImmersion
      (kostantRootSubgroup e h ρ (integralLattice 1).toAddSubgroup
        (kostantForm_apply_mem_integralLattice 1) i
        (isNilpotent_repEnveloping_root ℚ 1 i) b).hom.hom.left := by
  obtain ⟨r, s, c, hc, hstep, hsq⟩ := exists_unit_rootStep_repEnveloping_one i
  exact isClosedImmersion_kostantRootSubgroup e h ρ (integralLattice 1).toAddSubgroup
    (kostantForm_apply_mem_integralLattice 1) i (isNilpotent_repEnveloping_root ℚ 1 i) b
    hc hstep hsq

end TauCeti.Sl2Std
