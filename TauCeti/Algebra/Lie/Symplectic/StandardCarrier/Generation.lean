/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.AlternatingForm
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# Root-subgroup generation data for the type-C full-weight carrier

The numbered root subgroups of the full-weight type `C_(n+1)` carrier are the standard positive
and negative simple-root subgroups of `Sp_(2n+2)`.  The nonfinal nodes give the paired
transvections for the roots `e_i - e_(i+1)`, while the final node gives the long-root
transvection for `2e_n`.

These formulas hold over every commutative ring and supply the root-subgroup generation data used
to identify the carrier's field-valued points with the full symplectic group.

## Main results

* `TauCeti.SpStd.coe_rootSubgroupPoints_inl_of_ne_last` and its three companions identify the
  numbered carrier root subgroups with the standard symplectic simple-root elements over a
  commutative ring.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §5.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

The organization follows the type-`A` carrier generation file
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Generation`.  The comparison with paired
symplectic transvections is specific to type `C`.
-/

public section

open Matrix WithConv
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.SpStd

universe u

noncomputable section

attribute [local instance high] Algebra.toModule

variable (n : ℕ)
variable {A : Type u} [CommRing A]

private theorem map_intCast_eq_mapMatrix {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℤ) :
    M.map (Int.cast : ℤ → A) = (Int.castRingHom A).mapMatrix M := rfl

private theorem rootIntMatrix_eq_of_map_eq
    (k : Fin (n + 1) ⊕ Fin (n + 1))
    {M : Matrix (Fin ((n + 1) + (n + 1))) (Fin ((n + 1) + (n + 1))) ℤ}
    (h : (rootGenerator n k :
          Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℚ).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm = (Int.castRingHom ℚ).mapMatrix M) :
    rootIntMatrix n k = M := by
  apply Matrix.map_injective (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
  exact (map_rootIntMatrix n k).trans
    (h.trans (map_intCast_eq_mapMatrix (A := ℚ) M).symm)

private theorem rootIntMatrix_inl_last :
    rootIntMatrix n (.inl (Fin.last n)) =
      Matrix.single
        (finSumFinEquiv (Sum.inl (Fin.last n)))
        (finSumFinEquiv (Sum.inr (Fin.last n))) 1 := by
  apply rootIntMatrix_eq_of_map_eq
  simp only [val_rootGenerator_inl, positiveRootMatrix_last, Matrix.submatrix_single_equiv,
    RingHom.mapMatrix_apply, Matrix.map_single, map_one, Equiv.symm_symm]

private theorem rootIntMatrix_inr_last :
    rootIntMatrix n (.inr (Fin.last n)) =
      Matrix.single
        (finSumFinEquiv (Sum.inr (Fin.last n)))
        (finSumFinEquiv (Sum.inl (Fin.last n))) 1 := by
  apply rootIntMatrix_eq_of_map_eq
  simp only [val_rootGenerator_inr, negativeRootMatrix_last, Matrix.submatrix_single_equiv,
    RingHom.mapMatrix_apply, Matrix.map_single, map_one, Equiv.symm_symm]

private theorem rootIntMatrix_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inl i) =
      Matrix.single
          (finSumFinEquiv (Sum.inl i))
          (finSumFinEquiv (Sum.inl (next n i hi))) 1 -
        Matrix.single
          (finSumFinEquiv (Sum.inr (next n i hi)))
          (finSumFinEquiv (Sum.inr i)) 1 := by
  apply rootIntMatrix_eq_of_map_eq
  simp only [val_rootGenerator_inl, positiveRootMatrix_of_ne_last n i hi,
    Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_single_equiv, map_sub,
    RingHom.mapMatrix_apply, Matrix.map_single, map_one, Equiv.symm_symm]

private theorem rootIntMatrix_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inr i) =
      Matrix.single
          (finSumFinEquiv (Sum.inl (next n i hi)))
          (finSumFinEquiv (Sum.inl i)) 1 -
        Matrix.single
          (finSumFinEquiv (Sum.inr i))
          (finSumFinEquiv (Sum.inr (next n i hi))) 1 := by
  apply rootIntMatrix_eq_of_map_eq
  simp only [val_rootGenerator_inr, negativeRootMatrix_of_ne_last n i hi,
    Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_single_equiv, map_sub,
    RingHom.mapMatrix_apply, Matrix.map_single, map_one, Equiv.symm_symm]

private theorem val_rootSubgroupPoints_eq_one_add_smul
    (k : Fin (n + 1) ⊕ Fin (n + 1)) (c : A) :
    ((rootSubgroupPoints n k A (Multiplicative.ofAdd c) : points n A) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A).val =
      1 + c • (rootIntMatrix n k).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    (kostantRootSubgroupMatrix_eq_one_add_smul
      (rootGenerator n) (cartanGenerator n) (rep n) (lattice n).toAddSubgroup
      (fun _ hu _ hv => rep_kostantForm_mem_lattice n hu hv) k
      (isNilpotent_rep_rootGenerator n k) (latticeBasis n) (rootIntMatrix n k)
      (nilpotencyClass_rep_rootGenerator n k).le
      (rep_rootGenerator_latticeBasis_eq_sum n k)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
        (Multiplicative.ofAdd c)))

/-- The final raising root subgroup of the carrier is the positive long-root subgroup of the
standard symplectic group. -/
theorem coe_rootSubgroupPoints_inl_last (c : A) :
    (rootSubgroupPoints n (.inl (Fin.last n)) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.positiveLongRootTransvectionUnit (Fin.last n) c := by
  apply Units.ext
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_last,
    GLSymplecticFin.coe_positiveLongRootTransvectionUnit, TauCeti.coe_transvectionUnit]
  rw [map_intCast_eq_mapMatrix]
  rw [RingHom.mapMatrix_apply, Matrix.map_single, map_one, Matrix.smul_single,
    smul_eq_mul, mul_one, Matrix.transvection]

/-- The final lowering root subgroup of the carrier is the negative long-root subgroup of the
standard symplectic group. -/
theorem coe_rootSubgroupPoints_inr_last (c : A) :
    (rootSubgroupPoints n (.inr (Fin.last n)) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n) c := by
  apply Units.ext
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_last,
    GLSymplecticFin.coe_negativeLongRootTransvectionUnit, TauCeti.coe_transvectionUnit]
  rw [map_intCast_eq_mapMatrix]
  rw [RingHom.mapMatrix_apply, Matrix.map_single, map_one, Matrix.smul_single,
    smul_eq_mul, mul_one, Matrix.transvection]

/-- A nonfinal raising root subgroup of the carrier is the adjacent positive difference-root
subgroup of the standard symplectic group. -/
theorem coe_rootSubgroupPoints_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (c : A) :
    (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne c := by
  apply Units.ext
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul,
    TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]
  rw [map_intCast_eq_mapMatrix]
  rw [map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_single,
    Matrix.map_single, map_one]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.transvection,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_of_ne _ _ _ _
    (GLSymplecticFin.finSumFinEquiv_inl_ne_inr (next n i hi) (next n i hi)), add_zero,
    ← Matrix.single_neg]
  abel

/-- A nonfinal lowering root subgroup of the carrier is the adjacent negative difference-root
subgroup of the standard symplectic group. -/
theorem coe_rootSubgroupPoints_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (c : A) :
    (rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne' c := by
  apply Units.ext
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul,
    TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit]
  rw [map_intCast_eq_mapMatrix]
  rw [map_sub, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_single,
    Matrix.map_single, map_one]
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.transvection,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_of_ne _ _ _ _
    (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i), add_zero, ← Matrix.single_neg]
  abel

end

end TauCeti.SpStd
