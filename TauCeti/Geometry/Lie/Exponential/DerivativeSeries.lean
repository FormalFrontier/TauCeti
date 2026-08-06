/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The derivative series of the Banach-algebra exponential

This file packages the Fréchet derivative of the exponential in a possibly noncommutative real
Banach algebra. Its `n`th homogeneous contribution inserts the tangent vector in every position
among `n` copies of the base point.

## Main definitions

* `expFDerivSeries`: the convergent series of continuous linear maps representing the derivative.

## Main results

* `hasFDerivAt_exp_noncomm`: the Banach-algebra exponential has derivative `expFDerivSeries x`
  at `x` without a commutativity assumption.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "Differential of the exponential".
-/

public section

open scoped RightActions

noncomputable section

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- The degree-`n` contribution to the Fréchet derivative of the Banach-algebra exponential.
Applied to `y`, this is
`(n + 1)!⁻¹ • ∑ i < n + 1, x ^ (n - i) * y * x ^ i`. -/
noncomputable def expFDerivTerm (x : R) (n : ℕ) : R →L[ℝ] R :=
  ((n + 1).factorial⁻¹ : ℝ) •
    ∑ i ∈ Finset.range (n + 1),
      x ^ (n - i) •> ContinuousLinearMap.id ℝ R <• x ^ i

/-- The convergent Fréchet-derivative series of the Banach-algebra exponential. -/
noncomputable def expFDerivSeries (x : R) : R →L[ℝ] R :=
  ∑' n : ℕ, expFDerivTerm x n

omit [CompleteSpace R] in
/-- Evaluating a homogeneous derivative term inserts the tangent vector in every possible
position. -/
theorem expFDerivTerm_apply (x y : R) (n : ℕ) :
    expFDerivTerm x n y = ((n + 1).factorial⁻¹ : ℝ) •
      ∑ i ∈ Finset.range (n + 1), x ^ (n - i) * y * x ^ i := by
  rw [expFDerivTerm]
  change ((n + 1).factorial⁻¹ : ℝ) •
      (∑ i ∈ Finset.range (n + 1),
        x ^ (n - i) •> ContinuousLinearMap.id ℝ R <• x ^ i) y = _
  congr 1
  change (ContinuousLinearMap.apply ℝ R y)
      (∑ i ∈ Finset.range (n + 1),
        x ^ (n - i) •> ContinuousLinearMap.id ℝ R <• x ^ i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
private theorem norm_pow_le_max_one (x : R) (n : ℕ) :
    ‖x ^ n‖ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n + 1) := by
  by_cases hR : Nontrivial R
  · let _ : Nontrivial R := hR
    cases n with
    | zero =>
        simpa only [pow_zero, zero_add, pow_one] using
          (le_max_left (α := ℝ) ‖(1 : R)‖ ‖x‖)
    | succ n =>
        calc
          ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_pow_le' x (Nat.succ_pos n)
          _ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n + 1) := by
            gcongr
            exact le_max_right ‖(1 : R)‖ ‖x‖
          _ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n + 1 + 1) := by
            rw [pow_succ]
            exact le_mul_of_one_le_right
              (pow_nonneg ((norm_nonneg (1 : R)).trans (le_max_left _ _)) (n + 1))
              ((one_le_norm_one R).trans (le_max_left _ _))
  · let _ : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    have hOne : (1 : R) = 0 := Subsingleton.elim _ _
    rw [Subsingleton.elim x 0]
    cases n <;> simp [hOne]

omit [CompleteSpace R] in
private theorem norm_insertion_le (x : R) {n i : ℕ} (hi : i < n + 1) :
    ‖x ^ (n - i) •> ContinuousLinearMap.id ℝ R <• x ^ i‖ ≤
      max ‖(1 : R)‖ ‖x‖ ^ (n + 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (pow_nonneg ((norm_nonneg (1 : R)).trans (le_max_left _ _)) (n + 2)) ?_
  intro y
  change ‖x ^ (n - i) * y * x ^ i‖ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n + 2) * ‖y‖
  calc
    ‖x ^ (n - i) * y * x ^ i‖ ≤ ‖x ^ (n - i)‖ * ‖y‖ * ‖x ^ i‖ := by
      exact (norm_mul_le _ _).trans <| by gcongr; exact norm_mul_le _ _
    _ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n - i + 1) * ‖y‖ *
        max ‖(1 : R)‖ ‖x‖ ^ (i + 1) := by
      gcongr <;> exact norm_pow_le_max_one x _
    _ = max ‖(1 : R)‖ ‖x‖ ^ (n + 2) * ‖y‖ := by
      rw [mul_assoc, mul_comm ‖y‖, ← mul_assoc, ← pow_add,
        show n - i + 1 + (i + 1) = n + 2 by omega]

omit [CompleteSpace R] in
private theorem norm_expFDerivTerm_le (x : R) (n : ℕ) :
    ‖expFDerivTerm x n‖ ≤ max ‖(1 : R)‖ ‖x‖ ^ (n + 2) / n.factorial := by
  rw [expFDerivTerm, norm_smul]
  calc
    ‖((n + 1).factorial⁻¹ : ℝ)‖ *
        ‖∑ i ∈ Finset.range (n + 1),
          x ^ (n - i) •> ContinuousLinearMap.id ℝ R <• x ^ i‖ ≤
      ((n + 1).factorial : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), max ‖(1 : R)‖ ‖x‖ ^ (n + 2) := by
          gcongr
          · simp
          · refine norm_sum_le_of_le _ fun i hi ↦ ?_
            exact norm_insertion_le x (Finset.mem_range.mp hi)
    _ = max ‖(1 : R)‖ ‖x‖ ^ (n + 2) / n.factorial := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

private theorem summable_expFDerivTerm (x : R) : Summable (expFDerivTerm x) :=
  ((Real.summable_pow_div_factorial (max ‖(1 : R)‖ ‖x‖)).mul_left
      (max ‖(1 : R)‖ ‖x‖ ^ 2)).of_norm_bounded fun n ↦ by
        simpa only [← mul_div_assoc, ← pow_add, add_comm] using
          norm_expFDerivTerm_le x n

/-- The derivative series takes a tangent vector to the corresponding convergent insertion
series. -/
theorem expFDerivSeries_apply (x y : R) :
    expFDerivSeries x y = ∑' n : ℕ, expFDerivTerm x n y := by
  exact (ContinuousLinearMap.apply ℝ R y).map_tsum (summable_expFDerivTerm x)

omit [CompleteSpace R] in
private theorem hasFDerivAt_expSeriesTerm (n : ℕ) (x : R) :
    HasFDerivAt (((n + 1).factorial⁻¹ : ℝ) • (fun y : R ↦ y ^ (n + 1)))
      (expFDerivTerm x n) x := by
  simpa only [expFDerivTerm, Nat.pred_succ] using
    (hasFDerivAt_pow' (𝕜 := ℝ) (n + 1) (x := x)).const_smul
      ((n + 1).factorial⁻¹ : ℝ)

private theorem exp_eq_one_add_tsum_succ (x : R) :
    exp x = 1 + ∑' n : ℕ, ((n + 1).factorial⁻¹ : ℝ) • x ^ (n + 1) := by
  rw [exp_eq_tsum ℝ]
  convert (expSeries_summable' (𝕂 := ℝ) x).tsum_eq_zero_add using 1
  · simp

/-- The exponential in a possibly noncommutative real Banach algebra has the convergent insertion
series `expFDerivSeries x` as its Fréchet derivative at `x`. -/
theorem hasFDerivAt_exp_noncomm (x : R) :
    HasFDerivAt exp (expFDerivSeries x) x := by
  let r : ℝ := ‖x‖ + 1
  let c : ℝ := max ‖(1 : R)‖ r
  let u : ℕ → ℝ := fun n ↦ c ^ (n + 2) / n.factorial
  have hu : Summable u := by
    have h := (Real.summable_pow_div_factorial c).mul_left (c ^ 2)
    simpa only [u, ← mul_div_assoc, ← pow_add, add_comm] using h
  have hr : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg x) zero_lt_one
  have hseries :
      HasFDerivAt
        (fun y : R ↦ ∑' n : ℕ, (((n + 1).factorial⁻¹ : ℝ) •
          (fun z : R ↦ z ^ (n + 1))) y)
        (∑' n : ℕ, expFDerivTerm x n) x := by
    refine hasFDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := ℝ) (E := R) (F := R)
      (u := u)
      (f := fun n ↦ ((n + 1).factorial⁻¹ : ℝ) • (fun z : R ↦ z ^ (n + 1)))
      (f' := fun n y ↦ expFDerivTerm y n) (s := Metric.ball 0 r) (x₀ := 0) (x := x)
      hu Metric.isOpen_ball (convex_ball (0 : R) r).isPreconnected ?_ ?_ ?_ ?_ ?_
    · intro n y _hy
      exact hasFDerivAt_expSeriesTerm n y
    · intro n y hy
      refine (norm_expFDerivTerm_le y n).trans ?_
      dsimp only [u, c]
      gcongr
      have hyr : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
      exact hyr.le
    · simp [Metric.mem_ball, hr]
    · simp
    · simp [Metric.mem_ball, r]
  have hadd := (hasFDerivAt_const (x := x) (c := (1 : R))).add hseries
  have hadd' :
      HasFDerivAt
        ((fun _y : R ↦ (1 : R)) + fun y : R ↦
          ∑' n : ℕ, (((n + 1).factorial⁻¹ : ℝ) • (fun z : R ↦ z ^ (n + 1))) y)
        (expFDerivSeries x) x := by
    exact hadd.congr_fderiv (by simp [expFDerivSeries])
  apply hadd'.congr_of_eventuallyEq
  filter_upwards [] with y
  rw [Pi.add_apply, exp_eq_one_add_tsum_succ]
  congr 1

/-- The Fréchet derivative of the exponential in a possibly noncommutative real Banach algebra is
the convergent insertion series. -/
theorem fderiv_exp_noncomm (x : R) : fderiv ℝ exp x = expFDerivSeries x :=
  (hasFDerivAt_exp_noncomm x).fderiv

/-- At zero, the derivative series is the identity continuous linear map. -/
@[simp]
theorem expFDerivSeries_zero : expFDerivSeries (0 : R) = 1 :=
  (hasFDerivAt_exp_noncomm (0 : R)).unique hasFDerivAt_exp_zero
