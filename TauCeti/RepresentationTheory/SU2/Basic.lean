/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# `SU(2)` and its maximal torus

`SU(2)` is `Matrix.specialUnitaryGroup (Fin 2) ℂ`, the compact group that grounds the compact-group
representation theory of the [compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
Its compactness and topological group structure come from
`TauCeti/Topology/Algebra/UnitaryGroup.lean`, where they are proved for every special unitary
matrix group; Hausdorffness is inherited from the ambient matrix topology, `SU(2)` carrying the
subtype topology.

This file builds the **maximal torus** `T ⊂ SU(2)`, the diagonal circle subgroup

`T = { diag (z, z⁻¹) : |z| = 1 }`,

and identifies it with Mathlib's `Circle` as a topological group. Three facts pin it down:

* `TauCeti.SU2.mem_torus_iff`: an element of `SU(2)` lies in `T` exactly when it is diagonal, so
  `T` really is *the* diagonal subgroup and not merely some circle inside `SU(2)`;
* `TauCeti.SU2.centralizer_torus`: `T` is its own centralizer, whence
  `TauCeti.SU2.eq_torus_of_isMulCommutative`: `T` is a maximal abelian subgroup, which is what earns
  it the name "maximal torus";
* `TauCeti.SU2.mem_torus_iff_exists_torusExp`: every element of `T` is `diag (e^{iθ}, e^{-iθ})`,
  the parametrisation the Weyl integration and character formulas for `SU(2)` are stated in.

## Main definitions

* `TauCeti.SU2`: the group `SU(2)`.
* `TauCeti.SU2.torusHom`: the circle parametrisation `z ↦ diag (z, z⁻¹)` of the maximal torus.
* `TauCeti.SU2.torus`: the maximal torus of `SU(2)`, the range of `torusHom`.
* `TauCeti.SU2.torusContinuousMulEquiv`: the isomorphism of topological groups `Circle ≃ₜ* T`.
* `TauCeti.SU2.torusExp`: the torus element `diag (e^{iθ}, e^{-iθ})`.
-/

public section

namespace TauCeti

/-- `SU(2)`, the special unitary group of `2 × 2` complex matrices. It is a compact Hausdorff
topological group: the compactness and topological group instances come from
`TauCeti/Topology/Algebra/UnitaryGroup.lean`, and Hausdorffness from the ambient matrix
topology. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

namespace SU2

/-! ### The diagonal matrices `diag (z, z⁻¹)` -/

/-- The diagonal matrix `diag (z, z⁻¹)` attached to a point `z` of the unit circle. -/
noncomputable def torusMatrix (z : Circle) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(z : ℂ), ((z : ℂ))⁻¹]

@[simp]
theorem torusMatrix_apply_zero_zero (z : Circle) : torusMatrix z 0 0 = (z : ℂ) := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_one_one (z : Circle) : torusMatrix z 1 1 = ((z : ℂ))⁻¹ := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_zero_one (z : Circle) : torusMatrix z 0 1 = 0 := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_apply_one_zero (z : Circle) : torusMatrix z 1 0 = 0 := by
  simp [torusMatrix]

@[simp]
theorem torusMatrix_one : torusMatrix 1 = 1 := by
  rw [torusMatrix, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[simp]
theorem torusMatrix_mul (z w : Circle) :
    torusMatrix (z * w) = torusMatrix z * torusMatrix w := by
  rw [torusMatrix, torusMatrix, torusMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_comm]

@[simp]
theorem star_torusMatrix (z : Circle) : star (torusMatrix z) = torusMatrix z⁻¹ := by
  have hz : star (z : ℂ) = ((z : ℂ))⁻¹ := by simpa using (Circle.coe_inv_eq_conj z).symm
  rw [Matrix.star_eq_conjTranspose, torusMatrix, torusMatrix, Matrix.diagonal_conjTranspose]
  congr 1
  ext i
  fin_cases i <;> simp [hz]

@[simp]
theorem det_torusMatrix (z : Circle) : (torusMatrix z).det = 1 := by
  rw [torusMatrix, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem torusMatrix_mem (z : Circle) :
    torusMatrix z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, det_torusMatrix z⟩
  rw [Matrix.mem_unitaryGroup_iff, star_torusMatrix, ← torusMatrix_mul, mul_inv_cancel,
    torusMatrix_one]

theorem continuous_torusMatrix : Continuous torusMatrix := by
  have hcoe : Continuous fun z : Circle => (z : ℂ) := continuous_subtype_val
  have hinv : Continuous fun z : Circle => ((z : ℂ))⁻¹ := hcoe.inv₀ fun z => z.coe_ne_zero
  refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
  fin_cases i
  · exact hcoe
  · exact hinv

/-! ### The maximal torus -/

/-- The circle parametrisation `z ↦ diag (z, z⁻¹)` of the maximal torus of `SU(2)`. -/
noncomputable def torusHom : Circle →* SU2 where
  toFun z := ⟨torusMatrix z, torusMatrix_mem z⟩
  map_one' := Subtype.ext torusMatrix_one
  map_mul' z w := Subtype.ext (torusMatrix_mul z w)

-- `(rfl)`, not `rfl`: the parenthesised form proves the accessor without requiring `torusHom` to
-- be `@[expose]`d, so the definition stays opaque downstream. Likewise below.
@[simp]
theorem coe_torusHom (z : Circle) : (torusHom z : Matrix (Fin 2) (Fin 2) ℂ) = torusMatrix z := (rfl)

theorem continuous_torusHom : Continuous torusHom :=
  continuous_induced_rng.mpr continuous_torusMatrix

/-- The **maximal torus** of `SU(2)`: the diagonal circle subgroup. -/
noncomputable def torus : Subgroup SU2 := torusHom.range

theorem torusHom_mem_torus (z : Circle) : torusHom z ∈ torus := ⟨z, rfl⟩

/-- An element of `SU(2)` lies in the maximal torus exactly when it is a diagonal matrix: unitarity
makes the `(0, 0)` entry a point of the unit circle, and the determinant condition then forces the
`(1, 1)` entry to be its inverse. -/
@[simp]
theorem mem_torus_iff {g : SU2} :
    g ∈ torus ↔ Matrix.IsDiag (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · rintro ⟨z, rfl⟩
    rw [coe_torusHom, torusMatrix]
    exact Matrix.isDiag_diagonal _
  · intro hdiag
    have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := hdiag (by decide)
    have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := hdiag (by decide)
    have hunit : (g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    have hmul : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * star ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
        = 1 := by
      have h := congrFun (congrFun hunit 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_two] at h
      simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.one_apply,
        h01] using h
    have hnorm : ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = 1 := by
      have h := congrArg norm hmul
      rw [norm_mul, norm_star, norm_one] at h
      nlinarith [norm_nonneg ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)]
    have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := by
      have h := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
      rw [Matrix.det_fin_two, h01] at h
      simpa using h
    have h11 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_right hdet
    obtain ⟨z, hz⟩ : ∃ z : Circle, (z : ℂ) = (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 :=
      ⟨⟨_, mem_sphere_zero_iff_norm.mpr hnorm⟩, rfl⟩
    refine ⟨z, Subtype.ext ?_⟩
    rw [coe_torusHom, torusMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz, h01, h10, h11]

theorem torusHom_injective : Function.Injective torusHom := fun z w h => by
  have h00 := congrArg (fun g : SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  exact Circle.ext (by simpa using h00)

/-- The maximal torus of `SU(2)` *is* the circle group, as a topological group. -/
noncomputable def torusContinuousMulEquiv : Circle ≃ₜ* torus where
  __ := MonoidHom.ofInjective torusHom_injective
  continuous_toFun := continuous_torusHom.subtype_mk _
  continuous_invFun :=
    (Continuous.homeoOfEquivCompactToT2
      (f := (MonoidHom.ofInjective torusHom_injective).toEquiv)
      (continuous_torusHom.subtype_mk _)).continuous_invFun

@[simp]
theorem torusContinuousMulEquiv_apply (z : Circle) :
    (torusContinuousMulEquiv z : SU2) = torusHom z := (rfl)

instance : IsMulCommutative torus :=
  .of_setLike_mul_comm <| by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]

/-! ### Maximality -/

/-- The maximal torus is its own centralizer in `SU(2)`. -/
theorem centralizer_torus : Subgroup.centralizer (torus : Set SU2) = torus := by
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · -- `g` commutes with `diag (i, -i)`, which forces the off-diagonal entries of `g` to vanish.
    have hI : ‖Complex.I‖ = 1 := by simp
    set zi : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr hI⟩
    have hzi : (zi : ℂ) = Complex.I := rfl
    have hne : (2 : ℂ) * Complex.I ≠ 0 := by simp
    have hmat : torusMatrix zi * (g : Matrix (Fin 2) (Fin 2) ℂ)
        = (g : Matrix (Fin 2) (Fin 2) ℂ) * torusMatrix zi :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg (torusHom zi)
        (torusHom_mem_torus zi))
    have h01 : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by
      have h := congrFun (congrFun hmat 0) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, torusMatrix_apply_zero_zero,
        torusMatrix_apply_zero_one, torusMatrix_apply_one_one, hzi, Complex.inv_I] at h
      have h2 : 2 * Complex.I * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2).resolve_left hne
    have h10 : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by
      have h := congrFun (congrFun hmat 1) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two, torusMatrix_apply_zero_zero,
        torusMatrix_apply_one_one, torusMatrix_apply_one_zero, hzi, Complex.inv_I] at h
      have h2 : 2 * Complex.I * (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h2).resolve_left hne
    refine mem_torus_iff.mpr fun i j hij => ?_
    fin_cases i <;> fin_cases j <;> simp_all
  · rw [Subgroup.mem_centralizer_iff]
    rintro h ⟨w, rfl⟩
    obtain ⟨z, rfl⟩ := hg
    rw [← map_mul, ← map_mul, mul_comm]

/-- The maximal torus is a maximal abelian subgroup of `SU(2)`: a commutative subgroup containing
it is equal to it. -/
theorem eq_torus_of_isMulCommutative {H : Subgroup SU2} [IsMulCommutative H] (hH : torus ≤ H) :
    H = torus := by
  refine le_antisymm (fun g hg => ?_) hH
  rw [← centralizer_torus, Subgroup.mem_centralizer_iff]
  intro h hh
  exact setLike_mul_comm (hH hh) hg

/-! ### The angle parametrisation -/

/-- The torus element `diag (e^{iθ}, e^{-iθ})` of `SU(2)`. -/
noncomputable def torusExp (θ : ℝ) : SU2 := torusHom (Circle.exp θ)

@[simp]
theorem coe_torusExp (θ : ℝ) :
    (torusExp θ : Matrix (Fin 2) (Fin 2) ℂ)
      = Matrix.diagonal ![Complex.exp (θ * Complex.I), Complex.exp (-(θ * Complex.I))] := by
  rw [torusExp, coe_torusHom, torusMatrix]
  congr 1
  ext i
  fin_cases i <;> simp [← Complex.exp_neg]

theorem torusExp_mem_torus (θ : ℝ) : torusExp θ ∈ torus := torusHom_mem_torus _

@[simp]
theorem torusExp_add (θ φ : ℝ) : torusExp (θ + φ) = torusExp θ * torusExp φ := by
  rw [torusExp, torusExp, torusExp, Circle.exp_add, map_mul]

@[simp]
theorem torusExp_zero : torusExp 0 = 1 := by rw [torusExp, Circle.exp_zero, map_one]

/-- Every element of the maximal torus is `diag (e^{iθ}, e^{-iθ})` for some angle `θ`. -/
theorem mem_torus_iff_exists_torusExp {g : SU2} : g ∈ torus ↔ ∃ θ : ℝ, g = torusExp θ := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
    exact ⟨θ, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact torusExp_mem_torus θ

end SU2

end TauCeti
