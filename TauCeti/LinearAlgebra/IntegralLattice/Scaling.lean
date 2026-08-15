/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram

/-!
# Scaling and negating integral lattices

Multiplying the form of an integral lattice by an integer leaves its carrier fixed and preserves
integrality. This file equips integral lattices with that scalar action and computes the induced
integral form, Gram matrix, determinant, and discriminant. In particular, negating the form changes
the signed determinant by `(-1) ^ rank` and leaves the discriminant unchanged.

The scalar is integral because arbitrary rational scaling need not preserve an integral form. A
later development may admit rational scalars together with the necessary integrality hypothesis;
the canonical operation internal to integral lattices is the integer action defined here.

## Main definitions and results

* `TauCeti.IntegralLattice.scale`: multiply the rational form by an integer while keeping the
  carrier fixed.
* `TauCeti.IntegralLattice.instMulActionInt`: the integer multiplicative action on integral
  lattices.
* `TauCeti.IntegralLattice.instNeg`: form negation, defined as scaling by `-1`.
* `TauCeti.IntegralLattice.gramMatrix_smul`: scaling multiplies every Gram-matrix entry.
* `TauCeti.IntegralLattice.determinant_smul`: the determinant is multiplied by the scalar to the
  lattice rank.
* `TauCeti.IntegralLattice.discriminant_smul`: the discriminant is multiplied by the absolute
  scalar to the lattice rank.
* `TauCeti.IntegralLattice.discriminant_neg`: form negation preserves the discriminant.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1, form scaling and negation.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## Integer scaling -/

/-- Scale the form of an integral lattice by an integer, leaving its carrier unchanged.

Integer scaling preserves integrality because an integer multiple of every integral pairing is
again integral. The scalar acts on the rational form through the canonical map `ℤ → ℚ`. -/
def scale (n : ℤ) (L : IntegralLattice V) : IntegralLattice V where
  carrier := L.carrier
  form := (n : ℚ) • L.form
  isLattice := L.isLattice
  isSymm := L.isSymm.smul (n : ℚ)
  le_dual := by
    intro x hx
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    have hmem := Submodule.smul_mem (1 : Submodule ℤ ℚ) n
      (L.form_mem_one ⟨x, hx⟩ ⟨y, hy⟩)
    simpa only [LinearMap.smul_apply, Int.cast_smul_eq_zsmul] using hmem

/-- Integral lattices carry the canonical multiplicative action which scales their forms by
integers. -/
instance : MulAction ℤ (IntegralLattice V) where
  smul := scale
  one_smul L := by
    apply IntegralLattice.ext (L := scale 1 L) (M := L)
    · rfl
    · ext x y
      simp [scale]
  mul_smul m n L := by
    apply IntegralLattice.ext (L := scale (m * n) L) (M := scale m (scale n L))
    · rfl
    · ext x y
      simp only [scale, LinearMap.smul_apply, Int.cast_mul]
      ring

@[simp]
theorem smul_carrier (n : ℤ) (L : IntegralLattice V) :
    (n • L).carrier = L.carrier :=
  (rfl)

@[simp]
theorem smul_form (n : ℤ) (L : IntegralLattice V) :
    (n • L).form = (n : ℚ) • L.form :=
  (rfl)

/-- The carrier of a scaled lattice is canonically the original carrier. This equivalence is the
identity on underlying vectors. -/
def scaleCarrierEquiv (n : ℤ) (L : IntegralLattice V) : scale n L ≃ₗ[ℤ] L where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨x, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_scaleCarrierEquiv (n : ℤ) (L : IntegralLattice V) (x : scale n L) :
    (scaleCarrierEquiv n L x : V) = x :=
  (rfl)

@[simp]
theorem coe_scaleCarrierEquiv_symm (n : ℤ) (L : IntegralLattice V) (x : L) :
    ((scaleCarrierEquiv n L).symm x : V) = x :=
  (rfl)

/-- A carrier basis of an integral lattice, regarded as a basis of any integer scaling of that
lattice. -/
noncomputable def scaleBasis (n : ℤ) (L : IntegralLattice V) {ι : Type v}
    (e : Basis ι ℤ L) : Basis ι ℤ (scale n L) :=
  e.map (scaleCarrierEquiv n L).symm

@[simp]
theorem coe_scaleBasis (n : ℤ) (L : IntegralLattice V) {ι : Type v}
    (e : Basis ι ℤ L) (i : ι) :
    (scaleBasis n L e i : V) = e i := by
  simp [scaleBasis]

/-- Scaling the form does not change the rank of the carrier. -/
@[simp]
theorem finrank_scale (n : ℤ) (L : IntegralLattice V) :
    Module.finrank ℤ (scale n L) = Module.finrank ℤ L :=
  LinearEquiv.finrank_eq (scaleCarrierEquiv n L)

/-- Scaling by zero retains the carrier and replaces the form by zero. -/
theorem zero_smul_form (L : IntegralLattice V) : ((0 : ℤ) • L).form = 0 := by
  simp

/-- The integral form of a scaled lattice is the corresponding integer multiple of the original
integral form. -/
@[simp]
theorem integralForm_smul_apply (n : ℤ) (L : IntegralLattice V) (x y : L) :
    (scale n L).integralForm ((scaleCarrierEquiv n L).symm x)
      ((scaleCarrierEquiv n L).symm y) = n * L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  rw [integralForm_cast, Int.cast_mul, integralForm_cast]
  change (n : ℚ) * L.form x y = (n : ℚ) * L.form x y
  rfl

/-- Scaling commutes with the construction of the restricted integral form. -/
theorem integralForm_smul (n : ℤ) (L : IntegralLattice V) :
    (scale n L).integralForm.compl₁₂ (scaleCarrierEquiv n L).symm.toLinearMap
      (scaleCarrierEquiv n L).symm.toLinearMap = n • L.integralForm := by
  ext x y
  simp [integralForm_smul_apply]

/-! ## Gram matrices and invariants -/

/-- Scaling a lattice multiplies every entry of every Gram matrix by the scalar. -/
@[simp]
theorem gramMatrix_smul (n : ℤ) (L : IntegralLattice V) {ι : Type v}
    (e : Basis ι ℤ L) :
    (scale n L).gramMatrix (scaleBasis n L e) =
      (n • L.gramMatrix e : Matrix ι ι ℤ) := by
  ext i j
  rw [gramMatrix_apply]
  change (scale n L).integralForm ((scaleCarrierEquiv n L).symm (e i))
    ((scaleCarrierEquiv n L).symm (e j)) = n * L.gramMatrix e i j
  rw [integralForm_smul_apply]
  rw [gramMatrix_apply]

/-- The Gram determinant of a scaled lattice is multiplied by the scalar to the size of the
basis. -/
@[simp]
theorem gramDet_smul (n : ℤ) (L : IntegralLattice V) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (e : Basis ι ℤ L) :
    (scale n L).gramDet (scaleBasis n L e) = n ^ Fintype.card ι * L.gramDet e := by
  rw [gramDet_def, gramMatrix_smul, Matrix.det_smul, gramDet_def]

/-- Scaling by a nonzero integer preserves nondegeneracy of the rational form. -/
theorem nondegenerate_smul_iff {n : ℤ} (hn : n ≠ 0) (L : IntegralLattice V) :
    (n • L).form.Nondegenerate ↔ L.form.Nondegenerate := by
  change (scale n L).form.Nondegenerate ↔ L.form.Nondegenerate
  rw [← determinant_ne_zero_iff, ← determinant_ne_zero_iff]
  classical
  rw [determinant_eq_gramDet (scale n L)
      (scaleBasis n L (Module.Free.chooseBasis ℤ L)),
    gramDet_smul, ← determinant_eq_gramDet L (Module.Free.chooseBasis ℤ L)]
  exact mul_ne_zero_iff_left (pow_ne_zero _ hn)

/-- Scaling multiplies the signed determinant by the scalar to the rank of the lattice. -/
@[simp]
theorem determinant_smul (n : ℤ) (L : IntegralLattice V) :
    (n • L).determinant = n ^ Module.finrank ℤ L * L.determinant := by
  change (scale n L).determinant = _
  classical
  rw [determinant_eq_gramDet (scale n L)
      (scaleBasis n L (Module.Free.chooseBasis ℤ L)),
    gramDet_smul, ← Module.finrank_eq_card_chooseBasisIndex,
    ← determinant_eq_gramDet L (Module.Free.chooseBasis ℤ L)]

/-- Scaling multiplies the discriminant by the absolute scalar to the rank of the lattice. -/
@[simp]
theorem discriminant_smul (n : ℤ) (L : IntegralLattice V) :
    (n • L).discriminant = n.natAbs ^ Module.finrank ℤ L * L.discriminant := by
  rw [discriminant_def, determinant_smul, Int.natAbs_mul, Int.natAbs_pow, discriminant_def]

/-! ## Form negation -/

/-- Negating an integral lattice negates its form and leaves its carrier fixed. -/
instance : Neg (IntegralLattice V) := ⟨fun L ↦ (-1 : ℤ) • L⟩

@[simp]
theorem neg_carrier (L : IntegralLattice V) : (-L).carrier = L.carrier :=
  (rfl)

@[simp]
theorem neg_form (L : IntegralLattice V) : (-L).form = -L.form := by
  ext x y
  change (-1 : ℚ) * L.form x y = -L.form x y
  ring

/-- Negating a lattice twice recovers the original lattice. -/
@[simp]
theorem neg_neg (L : IntegralLattice V) : - -L = L := by
  ext <;> simp

/-- The integral form of the negated lattice is the negative of the original integral form. -/
@[simp]
theorem integralForm_neg_apply (L : IntegralLattice V) (x y : L) :
    (-L).integralForm ((scaleCarrierEquiv (-1) L).symm x)
      ((scaleCarrierEquiv (-1) L).symm y) = -L.integralForm x y := by
  change (scale (-1) L).integralForm ((scaleCarrierEquiv (-1) L).symm x)
    ((scaleCarrierEquiv (-1) L).symm y) = _
  rw [integralForm_smul_apply]
  ring

/-- Negation multiplies every Gram-matrix entry by `-1`. -/
@[simp]
theorem gramMatrix_neg (L : IntegralLattice V) {ι : Type v} (e : Basis ι ℤ L) :
    (-L).gramMatrix (scaleBasis (-1) L e) = -L.gramMatrix e := by
  change (scale (-1) L).gramMatrix (scaleBasis (-1) L e) = _
  rw [gramMatrix_smul]
  exact neg_one_smul ℤ (L.gramMatrix e)

/-- Negating the form multiplies a Gram determinant by `(-1)` to the size of its basis. -/
@[simp]
theorem gramDet_neg (L : IntegralLattice V) {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    (-L).gramDet (scaleBasis (-1) L e) =
      (-1 : ℤ) ^ Fintype.card ι * L.gramDet e := by
  change (scale (-1) L).gramDet (scaleBasis (-1) L e) = _
  exact gramDet_smul (-1) L e

/-- Negating the form multiplies the signed determinant by `(-1)` to the lattice rank. -/
@[simp]
theorem determinant_neg (L : IntegralLattice V) :
    (-L).determinant = (-1 : ℤ) ^ Module.finrank ℤ L * L.determinant := by
  simp [Neg.neg]

/-- Form negation preserves nondegeneracy. -/
@[simp]
theorem nondegenerate_neg_iff (L : IntegralLattice V) :
    (-L.form).Nondegenerate ↔ L.form.Nondegenerate := by
  rw [← neg_form]
  exact nondegenerate_smul_iff (by norm_num) L

/-- Form negation preserves the nonnegative discriminant. -/
@[simp]
theorem discriminant_neg (L : IntegralLattice V) : (-L).discriminant = L.discriminant := by
  rw [show -L = (-1 : ℤ) • L from rfl, discriminant_smul]
  norm_num

end TauCeti.IntegralLattice
