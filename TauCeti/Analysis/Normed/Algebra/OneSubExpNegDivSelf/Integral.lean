/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# An integral formula for the filled exponential quotient

This file identifies the filled quotient `(1 - exp (-a)) / a` with the integral of the
exponential along the line segment from `0` to `-a`. The formula remains valid when `a` is not
invertible.

## Main result

* `oneSubExpNegDivSelf_eq_integral_exp`:
  `oneSubExpNegDivSelf ℝ a = ∫ t in 0..1, exp (t • -a)`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

open NormedSpace
open TopologicalSpace

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private noncomputable def oneSubExpNegDivSelfIntegrand (a : A) (n : ℕ) : C(ℝ, A) :=
  ⟨fun t ↦ (n.factorial⁻¹ : ℝ) • ((t : ℝ) • (-a)) ^ n, by fun_prop⟩

omit [CompleteSpace A] in
@[simp]
private theorem oneSubExpNegDivSelfIntegrand_apply (a : A) (n : ℕ) (t : ℝ) :
    oneSubExpNegDivSelfIntegrand a n t = (n.factorial⁻¹ : ℝ) • (t • (-a)) ^ n := rfl

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
private theorem norm_pow_le_max_one (x : A) (n : ℕ) :
    ‖x ^ n‖ ≤ max ‖(1 : A)‖ ‖x‖ ^ (n + 1) := by
  by_cases hA : Nontrivial A
  · let _ : Nontrivial A := hA
    cases n with
    | zero =>
        simpa only [pow_zero, zero_add, pow_one] using
          (le_max_left (α := ℝ) ‖(1 : A)‖ ‖x‖)
    | succ n =>
        calc
          ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_pow_le' x (Nat.succ_pos n)
          _ ≤ max ‖(1 : A)‖ ‖x‖ ^ (n + 1) := by
            gcongr
            exact le_max_right ‖(1 : A)‖ ‖x‖
          _ ≤ max ‖(1 : A)‖ ‖x‖ ^ (n + 1 + 1) := by
            rw [pow_succ]
            exact le_mul_of_one_le_right
              (pow_nonneg ((norm_nonneg (1 : A)).trans (le_max_left _ _)) (n + 1))
              ((one_le_norm_one A).trans (le_max_left _ _))
  · let _ : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    have hOne : (1 : A) = 0 := Subsingleton.elim _ _
    rw [Subsingleton.elim x 0]
    cases n <;> simp [hOne]

omit [CompleteSpace A] in
private theorem summable_oneSubExpNegDivSelfIntegrand_norm (a : A) :
    Summable fun n : ℕ ↦
      ‖(oneSubExpNegDivSelfIntegrand a n).restrict
        (⟨Set.uIcc 0 1, isCompact_uIcc⟩ : Compacts ℝ)‖ := by
  let c : ℝ := max ‖(1 : A)‖ ‖-a‖
  have hc : Summable fun n : ℕ ↦ c ^ (n + 1) / n.factorial := by
    simpa only [pow_succ', mul_div_assoc] using
      (Real.summable_pow_div_factorial c).mul_left c
  refine hc.of_nonneg_of_le
    (fun n ↦ norm_nonneg _) ?_
  intro n
  refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
  intro t
  rcases t with ⟨t, ht⟩
  simp only [ContinuousMap.restrict_apply]
  rw [oneSubExpNegDivSelfIntegrand_apply, norm_smul]
  have ht_uIcc : t ∈ Set.uIcc 0 1 := by simpa using ht
  simp only [Set.mem_uIcc] at ht_uIcc
  have ht_norm : ‖t‖ ≤ 1 := by
    rcases ht_uIcc with ht | ht
    · rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    · linarith [ht.1, ht.2]
  have hta : ‖t • (-a)‖ ≤ ‖-a‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg (-a)) ht_norm
  calc
    ‖(n.factorial⁻¹ : ℝ)‖ * ‖(t • (-a)) ^ n‖ ≤
        (n.factorial⁻¹ : ℝ) * c ^ (n + 1) := by
      gcongr
      · simp
      · exact (norm_pow_le_max_one (t • (-a)) n).trans <| by
          dsimp only [c]
          gcongr
    _ = c ^ (n + 1) / n.factorial := by
      simp [div_eq_mul_inv, mul_comm]

private theorem integral_oneSubExpNegDivSelfIntegrand (a : A) (n : ℕ) :
    ∫ t in (0 : ℝ)..1, oneSubExpNegDivSelfIntegrand a n t =
      (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n := by
  simp only [oneSubExpNegDivSelfIntegrand_apply]
  simp_rw [smul_pow, smul_smul]
  rw [intervalIntegral.integral_smul_const,
    intervalIntegral.integral_const_mul, integral_pow]
  simp [Nat.factorial_succ]

/-- The regularized exponential quotient is the integral of the exponential along the line
segment from `0` to `-a`. -/
theorem oneSubExpNegDivSelf_eq_integral_exp (a : A) :
    oneSubExpNegDivSelf ℝ a = ∫ t in (0 : ℝ)..1, exp (t • (-a)) := by
  rw [oneSubExpNegDivSelf_eq_tsum]
  calc
    ∑' n : ℕ, (((n + 1).factorial)⁻¹ : ℝ) • (-a) ^ n =
        ∑' n : ℕ, ∫ t in (0 : ℝ)..1, oneSubExpNegDivSelfIntegrand a n t := by
      congr 1
      funext n
      exact (integral_oneSubExpNegDivSelfIntegrand a n).symm
    _ = ∫ t in (0 : ℝ)..1, ∑' n : ℕ, oneSubExpNegDivSelfIntegrand a n t :=
      intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
        (summable_oneSubExpNegDivSelfIntegrand_norm a)
    _ = ∫ t in (0 : ℝ)..1, exp (t • (-a)) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      rw [exp_eq_tsum ℝ]
      simp only [oneSubExpNegDivSelfIntegrand_apply]
