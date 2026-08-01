/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Trace.Basic

/-!
# Trace lemmas for field extensions

This file collects reusable trace facts for finite field extensions.

## Main results

* `TauCeti.NumberField.trace_eq_zero_of_sq_ratCast`: the number-field
  specialization saying that `x² ∈ ℚ`, `x ∉ ℚ` implies `Tr x = 0`.
* `TauCeti.Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range`: the corresponding
  trace-vanishing statement for any finite field extension.
* `TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap`: in a quadratic extension, the
  trace-form discriminant of the square-root basis `{1, x}` is `4a` when `x² = a` and
  `x ∉ F`.

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where these trace facts supported square-root basis computations over number fields.
-/

public section

open Module Polynomial

namespace TauCeti

namespace Algebra

/-- In a finite field extension, an element outside the base field whose square lies in the
base field has trace zero. -/
theorem trace_eq_zero_of_sq_algebraMap_of_not_mem_range {F L : Type*} [Field F] [Field L]
    [Algebra F L] [FiniteDimensional F L] {x : L} {r : F}
    (hx2 : x ^ 2 = algebraMap F L r) (hx : x ∉ (algebraMap F L).range) :
    Algebra.trace F L x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : F[X]) = 0 := by simp [hx2]
  have hdvd : minpoly F x ∣ (X ^ 2 - C r) := minpoly.dvd F x haeval
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : F[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly F x).natDegree = 2 := by
    have hle : (minpoly F x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly F x).natDegree := by
      by_contra h
      rw [not_le] at h
      interval_cases hh : (minpoly F x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly F x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : F[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]

/-- For a quadratic extension `L / F` and an element `x ∉ F` whose square is `a ∈ F`, the
trace-form discriminant of the square-root basis `{1, x}` equals `4 a`. -/
theorem discr_one_elem_eq_of_sq_algebraMap {x : L} {a : F} (hfin : finrank F L = 2)
    (hx2 : x ^ 2 = algebraMap F L a) (hx : x ∉ (algebraMap F L).range) :
    Algebra.discr F ![1, x] = 4 * a := by
  have htr0 : Algebra.trace F L x = 0 :=
    trace_eq_zero_of_sq_algebraMap_of_not_mem_range hx2 hx
  have hone : (1 : L) = algebraMap F L 1 := (map_one _).symm
  have hxmul : x * x = algebraMap F L a := by
    rw [← pow_two]
    exact hx2
  have e00 : Algebra.traceMatrix F ![1, x] 0 0 = 2 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, mul_one]
    rw [hone, Algebra.trace_algebraMap, hfin]
    simp
  have e11 : Algebra.traceMatrix F ![1, x] 1 1 = 2 * a := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hxmul, Algebra.trace_algebraMap, hfin]
    simp [nsmul_eq_mul]
  have e01 : Algebra.traceMatrix F ![1, x] 0 1 = 0 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    exact htr0
  have e10 : Algebra.traceMatrix F ![1, x] 1 0 = 0 := by
    rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one]
    exact htr0
  rw [Algebra.discr_def, Matrix.det_fin_two, e00, e11, e01, e10]
  ring

end Algebra

namespace NumberField

/-- In a number field, an irrational element whose square is rational has trace zero. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K]
    {x : K} {r : ℚ} (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 :=
  TauCeti.Algebra.trace_eq_zero_of_sq_algebraMap_of_not_mem_range hx2 hx

/-- Deprecated compatibility alias for the old NumberField helper name. -/
@[deprecated TauCeti.NumberField.trace_eq_zero_of_sq_ratCast (since := "2026-06-20")]
alias trace_eq_zero_of_sq_ratCast_of_not_mem_range := trace_eq_zero_of_sq_ratCast

end TauCeti.NumberField
