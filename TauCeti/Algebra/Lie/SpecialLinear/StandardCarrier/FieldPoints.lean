/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

import Mathlib.Data.Nat.Dist

/-!
# Field-valued points of the type A full-weight carrier

This file proves that over a field the matrix points of the full-weight type `A_r` carrier are
exactly `SL_{r+1}`. The key generation statement is that the elementary transvections attached to
the positive and negative simple roots generate every determinant-one matrix. Arbitrary root
transvections are obtained from adjacent ones by the type-A commutator relation, and Mathlib's
diagonal--transvection induction then reaches all of `SL`.

The result is the reverse, on field-valued points, of the determinant-one containment proved in
`TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.DeterminantOne`. It is a pointwise generation
step toward identifying the integral carrier group scheme with the special linear group scheme;
the equality of their defining Hopf ideals over `ℤ` is not asserted here.

## Main results

* `TauCeti.SlStd.transvectionUnit_mem_points`: every elementary transvection over a field is a
  point of the carrier.
* `TauCeti.SlStd.toGL_mem_points`: every determinant-one matrix over a field is a point of the
  carrier.
* `TauCeti.SlStd.points_eq_specialLinear`: the carrier points are exactly the image of
  `SL_{r+1}` in `GL_{r+1}`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26--27.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3--4.

This advances Layer 9, "The Chevalley--Demazure construction", of
`TauCetiRoadmap/ReductiveGroups/README.md`: it proves the missing generation statement for the
explicit full-weight type `A` carrier on points over fields.
-/

public section

open scoped commutatorElement

namespace TauCeti.SlStd

open Matrix

universe u

variable (r : ℕ) {K : Type u} [Field K]

private theorem diag2n_decompose {i j : Fin (r + 1)} (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n hij a ha =
      Matrix.SpecialLinearGroup.transvection hij a *
        Matrix.SpecialLinearGroup.transvection hij.symm (-a⁻¹) *
        Matrix.SpecialLinearGroup.transvection hij a *
        Matrix.SpecialLinearGroup.transvection hij (-1) *
        Matrix.SpecialLinearGroup.transvection hij.symm 1 *
        Matrix.SpecialLinearGroup.transvection hij (-1) := by
  apply Subtype.ext
  -- Expose the underlying matrices so the row-operation API recognizes each transvection.
  change Matrix.diagonal (fun k => if k = i then a else if k = j then a⁻¹ else 1) =
    Matrix.transvection i j a * Matrix.transvection j i (-a⁻¹) *
      Matrix.transvection i j a * Matrix.transvection i j (-1) *
      Matrix.transvection j i 1 * Matrix.transvection i j (-1)
  ext p q
  simp [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, hij,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]
  by_cases hpi : p = i <;> by_cases hpj : p = j <;>
    by_cases hqi : q = i <;> by_cases hqj : q = j
  all_goals simp_all [Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, eq_comm]

private theorem toGL_transvection_eq_transvectionUnit {i j : Fin (r + 1)}
    (hij : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij c) =
      TauCeti.transvectionUnit hij c := by
  apply Matrix.GeneralLinearGroup.ext
  intro p q
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, TauCeti.coe_transvectionUnit]
  rfl

/-! ## Generation by the numbered root subgroups -/

/-- Every elementary transvection attached to a positive or negative simple root is a point of
the type `A_r` carrier. -/
theorem rootTransvection_mem_points (k : Fin r ⊕ Fin r) (c : K) :
    TauCeti.transvectionUnit (rootTarget_ne_rootSource r k) c ∈ points r K := by
  have h := (rootSubgroupPoints r k K (Multiplicative.ofAdd c)).property
  rw [coe_rootSubgroupPoints, kostantRootSubgroupMatrix_eq_transvection] at h
  simpa using h

private theorem transvectionUnit_mem_points_of_succ_eq {i j : Fin (r + 1)}
    (hij : i ≠ j) (hsucc : i.val + 1 = j.val) (c : K) :
    TauCeti.transvectionUnit hij c ∈ points r K := by
  let k : Fin r := ⟨i.val, by omega⟩
  have hi : k.castSucc = i := Fin.ext rfl
  have hj : k.succ = j := Fin.ext (by simp only [k, Fin.val_succ]; omega)
  simpa only [rootTarget_inl, rootSource_inl, hi, hj] using
    rootTransvection_mem_points (K := K) r (.inl k) c

private theorem transvectionUnit_mem_points_of_eq_succ {i j : Fin (r + 1)}
    (hij : i ≠ j) (hsucc : j.val + 1 = i.val) (c : K) :
    TauCeti.transvectionUnit hij c ∈ points r K := by
  let k : Fin r := ⟨j.val, by omega⟩
  have hi : k.succ = i := Fin.ext (by simp only [k, Fin.val_succ]; omega)
  have hj : k.castSucc = j := Fin.ext rfl
  simpa only [rootTarget_inr, rootSource_inr, hi, hj] using
    rootTransvection_mem_points (K := K) r (.inr k) c

private theorem commutatorElement_mem_points
    {x y : Matrix.GeneralLinearGroup (Fin (r + 1)) K}
    (hx : x ∈ points r K) (hy : y ∈ points r K) :
    ⁅x, y⁆ ∈ points r K := by
  rw [commutatorElement_def]
  exact (points r K).mul_mem
    ((points r K).mul_mem ((points r K).mul_mem hx hy) ((points r K).inv_mem hx))
    ((points r K).inv_mem hy)

/-- Every elementary transvection over a field is a point of the type `A_r` carrier. -/
theorem transvectionUnit_mem_points {i j : Fin (r + 1)} (hij : i ≠ j) (c : K) :
    TauCeti.transvectionUnit hij c ∈ points r K := by
  let P : ℕ → Prop := fun d =>
    ∀ (i j : Fin (r + 1)) (hij : i ≠ j), Nat.dist i.val j.val = d → ∀ c : K,
      TauCeti.transvectionUnit hij c ∈
        points r K
  suffices ∀ d, P d by
    exact this (Nat.dist i.val j.val) i j hij rfl c
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro i j hij hdist c
      by_cases hforward : i.val + 1 = j.val
      · exact transvectionUnit_mem_points_of_succ_eq (K := K) r hij hforward c
      by_cases hbackward : j.val + 1 = i.val
      · exact transvectionUnit_mem_points_of_eq_succ (K := K) r hij hbackward c
      let k : Fin (r + 1) := if h : i.val < j.val then
        ⟨i.val + 1, by omega⟩ else ⟨i.val - 1, by omega⟩
      have hik : i ≠ k := by
        intro h
        have hval := Fin.ext_iff.mp h
        by_cases hlt : i.val < j.val
        · simp [k, hlt] at hval
        · simp [k, hlt] at hval
          omega
      have hkj : k ≠ j := by
        intro h
        have hval := Fin.ext_iff.mp h
        by_cases hlt : i.val < j.val
        · simp [k, hlt] at hval
          omega
        · simp [k, hlt] at hval
          omega
      have hdist_ik : Nat.dist i.val k.val < d := by
        rw [← hdist]
        by_cases hlt : i.val < j.val
        · rw [Nat.dist_eq_sub_of_le hlt.le,
            Nat.dist_eq_sub_of_le (by simp [k, hlt])]
          simp [k, hlt]
          omega
        · have hjilt : j.val < i.val := by omega
          rw [Nat.dist_eq_sub_of_le_right hjilt.le,
            Nat.dist_eq_sub_of_le_right (by simp [k, hlt])]
          simp [k, hlt]
          omega
      have hdist_kj : Nat.dist k.val j.val < d := by
        rw [← hdist]
        by_cases hlt : i.val < j.val
        · rw [Nat.dist_eq_sub_of_le hlt.le,
            Nat.dist_eq_sub_of_le (by simp [k, hlt])]
          simp [k, hlt]
          omega
        · have hjilt : j.val < i.val := by omega
          rw [Nat.dist_eq_sub_of_le_right hjilt.le,
            Nat.dist_eq_sub_of_le_right (by simp [k, hlt]; omega)]
          simp [k, hlt]
          omega
      have hik_mem := ih (Nat.dist i.val k.val) hdist_ik i k hik rfl c
      have hkj_mem := ih (Nat.dist k.val j.val) hdist_kj k j hkj rfl 1
      rw [← mul_one c,
        ← TauCeti.commutatorElement_transvectionUnit hik hkj hij c 1]
      exact commutatorElement_mem_points r hik_mem hkj_mem

/-! ## All field-valued points -/

/-- The canonical inclusion of every determinant-one matrix over a field is a point of the
full-weight type `A_r` carrier. -/
theorem toGL_mem_points (g : Matrix.SpecialLinearGroup (Fin (r + 1)) K) :
    Matrix.SpecialLinearGroup.toGL g ∈ points r K := by
  by_cases hr : r = 0
  · subst r
    have hg : g = 1 := by
      apply Subtype.ext
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.det_unique] using g.property
    rw [hg, map_one]
    exact (points 0 K).one_mem
  let _ : Nontrivial (Fin (r + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction'
    (fun g => Matrix.SpecialLinearGroup.toGL g ∈ points r K) g
  · intro i j hij a ha
    rw [diag2n_decompose r hij a ha]
    simp only [map_mul]
    simp only [toGL_transvection_eq_transvectionUnit]
    exact (points r K).mul_mem
      ((points r K).mul_mem
        ((points r K).mul_mem
          ((points r K).mul_mem
            ((points r K).mul_mem
              (transvectionUnit_mem_points (K := K) r hij a)
              (transvectionUnit_mem_points (K := K) r hij.symm (-a⁻¹)))
            (transvectionUnit_mem_points (K := K) r hij a))
          (transvectionUnit_mem_points (K := K) r hij (-1)))
        (transvectionUnit_mem_points (K := K) r hij.symm 1))
      (transvectionUnit_mem_points (K := K) r hij (-1))
  · intro i j hij c
    rw [toGL_transvection_eq_transvectionUnit]
    exact transvectionUnit_mem_points r hij c
  · intro x y hx hy
    simpa only [map_mul] using (points r K).mul_mem hx hy

/-- **Over a field, the matrix points of the full-weight type `A_r` carrier are exactly
`SL_{r+1}`**, viewed through the canonical inclusion into `GL_{r+1}`. -/
theorem points_eq_specialLinear :
    points r K =
      (Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin (r + 1)) K))) := by
  apply le_antisymm
  · intro g hg
    let s : Matrix.SpecialLinearGroup (Fin (r + 1)) K := ⟨g.val, by
      rw [← Matrix.GeneralLinearGroup.val_det_apply,
        det_eq_one_of_mem_points r hg, Units.val_one]⟩
    exact ⟨s, Subgroup.mem_top s, Matrix.GeneralLinearGroup.ext fun _ _ => rfl⟩
  · intro g hg
    obtain ⟨s, -, rfl⟩ := hg
    exact toGL_mem_points r s

end TauCeti.SlStd
