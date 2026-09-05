/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.AlternatingForm
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.TorusGeneration

/-!
# Field-valued points of the type-C full-weight carrier

The numbered root subgroups of the full-weight type `C_(n+1)` carrier are the standard positive
and negative simple-root subgroups of `Sp_(2n+2)`.  The nonfinal nodes give the paired
transvections for the roots `e_i - e_(i+1)`, while the final node gives the long-root
transvection for `2e_n`.

Over a field these simple-root subgroups generate the full symplectic group.  Since the carrier
already preserves the standard alternating form, its matrix points are therefore exactly
`TauCeti.GLSymplecticFin (n + 1) K`.

## Main results

* `TauCeti.SpStd.coe_rootSubgroupPoints_inl_of_ne_last` and its three companions identify the
  numbered carrier root subgroups with the standard symplectic simple-root elements.
* `TauCeti.SpStd.points_eq_GLSymplecticFin`: over a field, the carrier points are the full
  symplectic group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §5.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

The organization follows the type-`A` carrier generation and field-points files
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Generation` and
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FieldPoints`.  The comparison with paired
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

private theorem rootIntMatrix_inl_last :
    rootIntMatrix n (.inl (Fin.last n)) =
      Matrix.single
        (finSumFinEquiv (Sum.inl (Fin.last n)))
        (finSumFinEquiv (Sum.inr (Fin.last n))) 1 := by
  apply Matrix.ext
  intro r s
  have h := congrFun (congrFun (map_rootIntMatrix n (.inl (Fin.last n))) r) s
  exact Int.cast_injective (by simpa only [Matrix.map_apply, Matrix.submatrix_apply,
    val_rootGenerator_inl,
    positiveRootMatrix_last, Matrix.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Equiv.eq_symm_apply, Equiv.symm_apply_eq] using h)

private theorem rootIntMatrix_inr_last :
    rootIntMatrix n (.inr (Fin.last n)) =
      Matrix.single
        (finSumFinEquiv (Sum.inr (Fin.last n)))
        (finSumFinEquiv (Sum.inl (Fin.last n))) 1 := by
  apply Matrix.ext
  intro r s
  have h := congrFun (congrFun (map_rootIntMatrix n (.inr (Fin.last n))) r) s
  exact Int.cast_injective (by simpa only [Matrix.map_apply, Matrix.submatrix_apply,
    val_rootGenerator_inr,
    negativeRootMatrix_last, Matrix.single_apply, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Equiv.eq_symm_apply, Equiv.symm_apply_eq] using h)

private theorem rootIntMatrix_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inl i) =
      Matrix.single
          (finSumFinEquiv (Sum.inl i))
          (finSumFinEquiv (Sum.inl (next n i hi))) 1 -
        Matrix.single
          (finSumFinEquiv (Sum.inr (next n i hi)))
          (finSumFinEquiv (Sum.inr i)) 1 := by
  apply Matrix.ext
  intro r s
  have h := congrFun (congrFun (map_rootIntMatrix n (.inl i)) r) s
  exact Int.cast_injective (by simpa only [Matrix.map_apply, Matrix.submatrix_apply,
    val_rootGenerator_inl,
    positiveRootMatrix_of_ne_last n i hi, Matrix.sub_apply, Matrix.single_apply,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Equiv.eq_symm_apply, Equiv.symm_apply_eq] using h)

private theorem rootIntMatrix_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n) :
    rootIntMatrix n (.inr i) =
      Matrix.single
          (finSumFinEquiv (Sum.inl (next n i hi)))
          (finSumFinEquiv (Sum.inl i)) 1 -
        Matrix.single
          (finSumFinEquiv (Sum.inr i))
          (finSumFinEquiv (Sum.inr (next n i hi))) 1 := by
  apply Matrix.ext
  intro r s
  have h := congrFun (congrFun (map_rootIntMatrix n (.inr i)) r) s
  exact Int.cast_injective (by simpa only [Matrix.map_apply, Matrix.submatrix_apply,
    val_rootGenerator_inr,
    negativeRootMatrix_of_ne_last n i hi, Matrix.sub_apply, Matrix.single_apply,
    Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    Equiv.eq_symm_apply, Equiv.symm_apply_eq] using h)

private theorem one_add_smul_single (a b : Fin ((n + 1) + (n + 1))) (c : A) :
    (1 : Matrix _ _ A) + c • Matrix.single a b 1 = Matrix.transvection a b c := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.transvection]

private theorem one_add_smul_single_sub_single
    (a b d e : Fin ((n + 1) + (n + 1))) (hbd : b ≠ d) (c : A) :
    (1 : Matrix _ _ A) + c • (Matrix.single a b 1 - Matrix.single d e 1) =
      Matrix.transvection a b c * Matrix.transvection d e (-c) := by
  simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one, Matrix.transvection,
    Matrix.mul_add, Matrix.add_mul, Matrix.one_mul]
  rw [Matrix.single_mul_single_of_ne _ _ _ _ hbd, add_zero, ← Matrix.single_neg]
  abel

private theorem map_single_intCast (a b : Fin ((n + 1) + (n + 1))) :
    (Matrix.single a b (1 : ℤ)).map (Int.cast : ℤ → A) = Matrix.single a b 1 := by
  ext r s
  simp [Matrix.map_apply, Matrix.single_apply]

private theorem map_single_sub_single_intCast (a b d e : Fin ((n + 1) + (n + 1))) :
    (Matrix.single a b (1 : ℤ) - Matrix.single d e 1).map (Int.cast : ℤ → A) =
      Matrix.single a b 1 - Matrix.single d e 1 := by
  ext r s
  simp [Matrix.map_apply, Matrix.single_apply]

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
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_last,
    GLSymplecticFin.coe_positiveLongRootTransvectionUnit, TauCeti.coe_transvectionUnit,
    map_single_intCast]
  exact congrFun (congrFun (one_add_smul_single n
    (finSumFinEquiv (Sum.inl (Fin.last n)))
    (finSumFinEquiv (Sum.inr (Fin.last n))) c) r) s

/-- The final lowering root subgroup of the carrier is the negative long-root subgroup of the
standard symplectic group. -/
theorem coe_rootSubgroupPoints_inr_last (c : A) :
    (rootSubgroupPoints n (.inr (Fin.last n)) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.negativeLongRootTransvectionUnit (Fin.last n) c := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_last,
    GLSymplecticFin.coe_negativeLongRootTransvectionUnit, TauCeti.coe_transvectionUnit,
    map_single_intCast]
  exact congrFun (congrFun (one_add_smul_single n
    (finSumFinEquiv (Sum.inr (Fin.last n)))
    (finSumFinEquiv (Sum.inl (Fin.last n))) c) r) s

/-- A nonfinal raising root subgroup of the carrier is the adjacent positive difference-root
subgroup of the standard symplectic group. -/
theorem coe_rootSubgroupPoints_inl_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (c : A) :
    (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne c := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inl_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul,
    TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit,
    map_single_sub_single_intCast]
  exact congrFun (congrFun
    (one_add_smul_single_sub_single n
      (finSumFinEquiv (Sum.inl i))
      (finSumFinEquiv (Sum.inl (next n i hi)))
      (finSumFinEquiv (Sum.inr (next n i hi)))
      (finSumFinEquiv (Sum.inr i))
      (GLSymplecticFin.finSumFinEquiv_inl_ne_inr (next n i hi) (next n i hi)) c) r) s

/-- A nonfinal lowering root subgroup of the carrier is the adjacent negative difference-root
subgroup of the standard symplectic group. -/
theorem coe_rootSubgroupPoints_inr_of_ne_last (i : Fin (n + 1)) (hi : i ≠ Fin.last n)
    (c : A) :
    (rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin ((n + 1) + (n + 1))) A) =
      GLSymplecticFin.differenceShortRootUnit (lt_next n i hi).ne' c := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [val_rootSubgroupPoints_eq_one_add_smul, rootIntMatrix_inr_of_ne_last n i hi,
    GLSymplecticFin.coe_differenceShortRootUnit, Units.val_mul,
    TauCeti.coe_transvectionUnit, TauCeti.coe_transvectionUnit,
    map_single_sub_single_intCast]
  exact congrFun (congrFun
    (one_add_smul_single_sub_single n
      (finSumFinEquiv (Sum.inl (next n i hi)))
      (finSumFinEquiv (Sum.inl i))
      (finSumFinEquiv (Sum.inr i))
      (finSumFinEquiv (Sum.inr (next n i hi)))
      (GLSymplecticFin.finSumFinEquiv_inl_ne_inr i i) c) r) s

/-- **Over a field, the matrix points of the full-weight type `C_(n+1)` carrier are exactly the
standard symplectic group.** -/
theorem points_eq_GLSymplecticFin {K : Type u} [Field K] :
    points n K = GLSymplecticFin (n + 1) K := by
  apply le_antisymm
  · intro g hg
    exact mem_GLSymplecticFin_of_mem_points n hg
  · let H : Subgroup (GLSymplecticFin (n + 1) K) :=
      (points n K).comap (GLSymplecticFin (n + 1) K).subtype
    have hH : H = ⊤ := by
      apply GLSymplecticFin.eq_top_of_adjacent_of_long H (Fin.last n)
      · intro i j hij c hadjacent
        rcases hadjacent with hijSucc | hjiSucc
        · have hi : i ≠ Fin.last n := by
            intro hi
            subst i
            have hjlt := j.isLt
            simp only [Fin.val_last] at hijSucc
            omega
          have hj : next n i hi = j := Fin.ext (by simpa only [val_next] using hijSucc)
          subst j
          rw [Subgroup.mem_comap]
          have hroot := (rootSubgroupPoints n (.inl i) K (Multiplicative.ofAdd c)).property
          rw [coe_rootSubgroupPoints_inl_of_ne_last n i hi c] at hroot
          exact hroot
        · have hj : j ≠ Fin.last n := by
            intro hj
            subst j
            have hilt := i.isLt
            simp only [Fin.val_last] at hjiSucc
            omega
          have hi : next n j hj = i := Fin.ext (by simpa only [val_next] using hjiSucc)
          subst i
          rw [Subgroup.mem_comap]
          have hroot := (rootSubgroupPoints n (.inr j) K (Multiplicative.ofAdd c)).property
          rw [coe_rootSubgroupPoints_inr_of_ne_last n j hj c] at hroot
          exact hroot
      · intro c
        rw [Subgroup.mem_comap]
        have hroot :=
          (rootSubgroupPoints n (.inl (Fin.last n)) K (Multiplicative.ofAdd c)).property
        rw [coe_rootSubgroupPoints_inl_last n c] at hroot
        exact hroot
      · intro c
        rw [Subgroup.mem_comap]
        have hroot :=
          (rootSubgroupPoints n (.inr (Fin.last n)) K (Multiplicative.ofAdd c)).property
        rw [coe_rootSubgroupPoints_inr_last n c] at hroot
        exact hroot
    intro g hg
    have : (⟨g, hg⟩ : GLSymplecticFin (n + 1) K) ∈ H := by
      rw [hH]
      exact Subgroup.mem_top _
    exact this

end

end TauCeti.SpStd
