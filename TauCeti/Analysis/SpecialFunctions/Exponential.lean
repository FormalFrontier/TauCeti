/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Duhamel's formula for the Banach-algebra exponential

This file expresses a finite increment of the exponential in a possibly noncommutative real
Banach algebra as an integral. Unlike a first-order derivative formula, the identity is exact for
every increment.

## Main result

* `intervalIntegrable_exp_smul_mul_mul_exp_smul`: the Duhamel integrand is interval integrable.
* `exp_add_sub_exp_eq_integral`: `exp (x + h) - exp x` is the integral of
  `exp ((1 - t) (x + h)) * h * exp (t x)` over the unit interval.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
* R. M. Wilcox, *Exponential Operators and Parameter Differentiation in Quantum Physics*, Journal
  of Mathematical Physics 8 (1967), 962–982.
-/

public section

open NormedSpace MeasureTheory

noncomputable section

namespace TauCeti

section Duhamel

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

private theorem hasDerivAt_exp_smul_mul_exp_smul (x h : A) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ exp ((1 - s) • (x + h)) * exp (s • x))
      (-(exp ((1 - t) • (x + h)) * h * exp (t • x))) t := by
  have hleft : HasDerivAt
      (fun s : ℝ ↦ exp ((1 - s) • (x + h)))
      (-(exp ((1 - t) • (x + h)) * (x + h))) t := by
    exact (hasDerivAt_exp_smul_const (x + h) (1 - t)).comp_const_sub 1 t
  have hright : HasDerivAt
      (fun s : ℝ ↦ exp (s • x))
      (x * exp (t • x)) t :=
    hasDerivAt_exp_smul_const' x t
  exact (hleft.fun_mul hright).congr_deriv (by noncomm_ring)

/-- The integrand in Duhamel's finite-increment formula is interval integrable. -/
theorem intervalIntegrable_exp_smul_mul_mul_exp_smul (x h : A) :
    IntervalIntegrable
      (fun t : ℝ ↦ exp ((1 - t) • (x + h)) * h * exp (t • x)) volume 0 1 :=
  Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1

/-- Duhamel's exact finite-increment formula for the exponential in a possibly noncommutative real
Banach algebra. -/
theorem exp_add_sub_exp_eq_integral (x h : A) :
    exp (x + h) - exp x =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + h)) * h * exp (t • x) := by
  let F : ℝ → A := fun t ↦ exp ((1 - t) • (x + h)) * exp (t • x)
  let F' : ℝ → A := fun t ↦ -(exp ((1 - t) • (x + h)) * h * exp (t • x))
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F (F' t) t := by
    intro t _ht
    exact hasDerivAt_exp_smul_mul_exp_smul x h t
  have hint : IntervalIntegrable F' volume (0 : ℝ) 1 := by
    exact (intervalIntegrable_exp_smul_mul_mul_exp_smul x h).neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp only [F, F'] at hFTC
  simp only [one_smul, sub_self, sub_zero, zero_smul, exp_zero, mul_one, one_mul,
    intervalIntegral.integral_neg] at hFTC
  have hneg := congrArg Neg.neg hFTC
  simpa only [neg_neg, neg_sub] using hneg.symm

end Duhamel

/-!
## The Fréchet derivative series

The Fréchet derivative of the exponential in a possibly noncommutative Banach algebra over an
`RCLike` field is the convergent series whose `n`th homogeneous contribution inserts the tangent
vector in every position among `n` copies of the base point.

### Main definitions

* `TauCeti.expFDerivTerm`: the degree-`n` insertion term in the derivative series.
* `TauCeti.expFDeriv`: the sum of the derivative series as a continuous linear map.

### Main results

* `TauCeti.expFDerivTerm_apply`: the pointwise insertion formula for one term.
* `TauCeti.expFDeriv_eq_tsum`: the operator-valued defining series.
* `TauCeti.summable_expFDerivTerm`: summability of the operator-valued series.
* `TauCeti.summable_expFDerivTerm_apply`: pointwise summability of the insertion series.
* `TauCeti.expFDeriv_apply`: the pointwise formula for the summed operator.
* `TauCeti.hasStrictFDerivAt_exp`: the exponential has strict derivative `expFDeriv 𝕂 x` at `x`.
* `TauCeti.hasFDerivAt_exp`: the corresponding ordinary Fréchet derivative statement.
* `TauCeti.fderiv_exp`: the derivative expressed using `fderiv`.
* `TauCeti.expFDeriv_eq_smul_one`: the commutative-algebra specialization.
* `TauCeti.expFDeriv_zero`: at zero, the formal derivative-series operator is the identity.
-/

open scoped RightActions

variable {𝕂 R : Type*}

section Definitions

variable [NontriviallyNormedField 𝕂] [NormedRing R] [NormedAlgebra 𝕂 R]

/-- The degree-`n` contribution to the Fréchet derivative of the Banach-algebra exponential.
Applied to `y`, this is
`(n + 1)!⁻¹ • ∑ i < n + 1, x ^ (n - i) * y * x ^ i`. -/
noncomputable def expFDerivTerm (𝕂 : Type*) [NontriviallyNormedField 𝕂] {R : Type*} [NormedRing R]
    [NormedAlgebra 𝕂 R] (x : R) (n : ℕ) : R →L[𝕂] R :=
  ((n + 1).factorial⁻¹ : 𝕂) •
    ∑ i ∈ Finset.range (n + 1),
      x ^ (n - i) •> ContinuousLinearMap.id 𝕂 R <• x ^ i

/-- The sum of the Fréchet-derivative series of the Banach-algebra exponential. It converges when
`𝕂` is `RCLike` and the algebra is complete (see `summable_expFDerivTerm`); as usual for `tsum`, it
has the junk value zero when the series is not summable. -/
noncomputable def expFDeriv (𝕂 : Type*) [NontriviallyNormedField 𝕂] {R : Type*} [NormedRing R]
    [NormedAlgebra 𝕂 R] (x : R) : R →L[𝕂] R :=
  ∑' n : ℕ, expFDerivTerm 𝕂 x n

/-- Evaluating a homogeneous derivative term inserts the tangent vector in every possible
position. -/
@[simp]
theorem expFDerivTerm_apply (x y : R) (n : ℕ) :
    expFDerivTerm 𝕂 x n y = ((n + 1).factorial⁻¹ : 𝕂) •
      ∑ i ∈ Finset.range (n + 1), x ^ (n - i) * y * x ^ i := by
  simp [expFDerivTerm]

/-- The operator-valued defining series for `expFDeriv`. -/
theorem expFDeriv_eq_tsum (x : R) :
    expFDeriv 𝕂 x = ∑' n : ℕ, expFDerivTerm 𝕂 x n := by
  rfl

end Definitions

variable [RCLike 𝕂] [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R]

omit [NormedAlgebra 𝕂 R] [CompleteSpace R] in
private theorem norm_pow_le_growth_bound (x : R) (n : ℕ) :
    ‖x ^ n‖ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 1) := by
  have hc : 1 ≤ max 1 (max ‖(1 : R)‖ ‖x‖) := le_max_left _ _
  have hOne : ‖(1 : R)‖ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hx : ‖x‖ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) :=
    (le_max_right _ _).trans (le_max_right _ _)
  cases n with
  | zero => simpa only [pow_zero, zero_add, pow_one] using hOne
  | succ n =>
      calc
        ‖x ^ (n + 1)‖ ≤ ‖x‖ ^ (n + 1) := norm_pow_le' x (Nat.succ_pos n)
        _ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 1) := by gcongr
        _ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 1 + 1) :=
          pow_le_pow_right₀ hc (Nat.le_succ _)

omit [CompleteSpace R] in
private theorem norm_insertion_le (x : R) {n i : ℕ} (hi : i < n + 1) :
    ‖x ^ (n - i) •> ContinuousLinearMap.id 𝕂 R <• x ^ i‖ ≤
      max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 2) := by
  have hinsertion :
      x ^ (n - i) •> ContinuousLinearMap.id 𝕂 R <• x ^ i =
        ContinuousLinearMap.mulLeftRight 𝕂 R (x ^ (n - i)) (x ^ i) := by
    ext y
    simp
  rw [hinsertion]
  calc
    ‖ContinuousLinearMap.mulLeftRight 𝕂 R (x ^ (n - i)) (x ^ i)‖ ≤
        ‖x ^ (n - i)‖ * ‖x ^ i‖ :=
      ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le 𝕂 R _ _
    _ ≤ max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n - i + 1) *
        max 1 (max ‖(1 : R)‖ ‖x‖) ^ (i + 1) := by
      gcongr <;> exact norm_pow_le_growth_bound x _
    _ = max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 2) := by
      rw [← pow_add]
      congr 1
      omega

omit [CompleteSpace R] in
private theorem norm_expFDerivTerm_le (x : R) (n : ℕ) :
    ‖expFDerivTerm 𝕂 x n‖ ≤
      max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 2) / n.factorial := by
  rw [expFDerivTerm, norm_smul]
  have hfactorial : ‖((n + 1).factorial⁻¹ : 𝕂)‖ = ((n + 1).factorial : ℝ)⁻¹ := by
    simp
  calc
    ‖((n + 1).factorial⁻¹ : 𝕂)‖ *
        ‖∑ i ∈ Finset.range (n + 1),
          x ^ (n - i) •> ContinuousLinearMap.id 𝕂 R <• x ^ i‖ ≤
      ((n + 1).factorial : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 2) := by
          rw [hfactorial]
          gcongr
          refine norm_sum_le_of_le _ fun i hi ↦ ?_
          exact norm_insertion_le x (Finset.mem_range.mp hi)
    _ = max 1 (max ‖(1 : R)‖ ‖x‖) ^ (n + 2) / n.factorial := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp

private theorem summable_pow_succ_succ_div_factorial (c : ℝ) :
    Summable fun n : ℕ ↦ c ^ (n + 2) / n.factorial := by
  refine ((Real.summable_pow_div_factorial c).mul_left (c ^ 2)).congr fun n ↦ ?_
  rw [← mul_div_assoc, ← pow_add, add_comm]

/-- The operator-valued derivative series is summable. -/
theorem summable_expFDerivTerm (x : R) : Summable (expFDerivTerm 𝕂 x) :=
  Summable.of_norm_bounded
    (summable_pow_succ_succ_div_factorial (max 1 (max ‖(1 : R)‖ ‖x‖)))
    (norm_expFDerivTerm_le (𝕂 := 𝕂) x)

/-- Applying the derivative terms to a fixed tangent vector gives a summable series. -/
theorem summable_expFDerivTerm_apply (x y : R) :
    Summable (fun n : ℕ ↦ expFDerivTerm 𝕂 x n y) :=
  (summable_expFDerivTerm (𝕂 := 𝕂) x).mapL (ContinuousLinearMap.apply 𝕂 R y)

/-- The summed derivative operator takes a tangent vector to the corresponding insertion series. -/
@[simp]
theorem expFDeriv_apply (x y : R) :
    expFDeriv 𝕂 x y = ∑' n : ℕ, expFDerivTerm 𝕂 x n y := by
  exact (ContinuousLinearMap.apply 𝕂 R y).map_tsum (summable_expFDerivTerm x)

omit [CompleteSpace R] in
private theorem hasFDerivAt_inv_factorial_smul_pow_succ (n : ℕ) (x : R) :
    HasFDerivAt (((n + 1).factorial⁻¹ : 𝕂) • (fun y : R ↦ y ^ (n + 1)))
      (expFDerivTerm 𝕂 x n) x := by
  simpa only [expFDerivTerm, Nat.pred_succ] using
    (hasFDerivAt_pow' (𝕜 := 𝕂) (n + 1) (x := x)).const_smul
      ((n + 1).factorial⁻¹ : 𝕂)

private theorem exp_eq_one_add_tsum_succ (x : R) :
    exp x = 1 + ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕂) • x ^ (n + 1) := by
  simp only [exp_eq_tsum 𝕂]
  rw [(expSeries_summable' (𝕂 := 𝕂) x).tsum_eq_zero_add]
  simp

/-- The exponential in a possibly noncommutative Banach algebra has the convergent insertion sum
`expFDeriv 𝕂 x` as its Fréchet derivative at `x`. -/
theorem hasFDerivAt_exp (x : R) :
    HasFDerivAt exp (expFDeriv 𝕂 x) x := by
  -- The real restriction supplies the normed-space structure used by convexity of metric balls.
  let _ : NormedSpace ℝ R := NormedSpace.restrictScalars ℝ 𝕂 R
  let r : ℝ := ‖x‖ + 1
  let c : ℝ := max 1 (max ‖(1 : R)‖ r)
  let u : ℕ → ℝ := fun n ↦ c ^ (n + 2) / n.factorial
  have hu : Summable u := by
    simpa only [u] using summable_pow_succ_succ_div_factorial c
  have hr : 0 < r := add_pos_of_nonneg_of_pos (norm_nonneg x) zero_lt_one
  have hderiv : ∀ n y, y ∈ Metric.ball (0 : R) r →
      HasFDerivAt
        (((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1)))
        (expFDerivTerm 𝕂 y n) y := fun n y _hy ↦
    hasFDerivAt_inv_factorial_smul_pow_succ n y
  have hbound : ∀ n y, y ∈ Metric.ball (0 : R) r → ‖expFDerivTerm 𝕂 y n‖ ≤ u n := by
    intro n y hy
    refine (norm_expFDerivTerm_le y n).trans ?_
    dsimp only [u, c]
    gcongr
    have hyr : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact hyr.le
  have hx₀ : (0 : R) ∈ Metric.ball 0 r := by simp [Metric.mem_ball, hr]
  have hsummableAtZero : Summable fun n : ℕ ↦
      (((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1))) 0 := by simp
  have hx : x ∈ Metric.ball (0 : R) r := by simp [Metric.mem_ball, r]
  have hseries :
      HasFDerivAt
        (fun y : R ↦ ∑' n : ℕ, (((n + 1).factorial⁻¹ : 𝕂) •
          (fun z : R ↦ z ^ (n + 1))) y)
        (∑' n : ℕ, expFDerivTerm 𝕂 x n) x := by
    refine hasFDerivAt_tsum_of_isPreconnected (α := ℕ) (𝕜 := 𝕂) (E := R) (F := R)
      (u := u)
      (f := fun n ↦ ((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1)))
      (f' := fun n y ↦ expFDerivTerm 𝕂 y n) (s := Metric.ball 0 r) (x₀ := 0) (x := x)
      hu Metric.isOpen_ball (convex_ball (0 : R) r).isPreconnected hderiv hbound hx₀
        hsummableAtZero hx
  have hadd := (hasFDerivAt_const (x := x) (c := (1 : R))).add hseries
  have hadd' :
      HasFDerivAt
        ((fun _y : R ↦ (1 : R)) + fun y : R ↦
          ∑' n : ℕ, (((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1))) y)
        (expFDeriv 𝕂 x) x := by
    apply hadd.congr_fderiv
    rw [zero_add, expFDeriv]
  exact hadd'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by
    rw [Pi.add_apply, exp_eq_one_add_tsum_succ (𝕂 := 𝕂)]
    simp only [Pi.smul_apply])

/-- The strict Fréchet-derivative form of `hasFDerivAt_exp`. -/
theorem hasStrictFDerivAt_exp (x : R) :
    HasStrictFDerivAt exp (expFDeriv 𝕂 x) x :=
  (NormedSpace.exp_analytic (𝕂 := 𝕂) x).hasStrictFDerivAt.congr_fderiv
    (hasFDerivAt_exp (𝕂 := 𝕂) x).fderiv

/-- The Fréchet derivative of the exponential in a possibly noncommutative Banach algebra is the
convergent insertion sum. -/
@[simp]
theorem fderiv_exp (x : R) : fderiv 𝕂 exp x = expFDeriv 𝕂 x :=
  (hasFDerivAt_exp (𝕂 := 𝕂) x).fderiv

/-- In a commutative Banach algebra, the insertion sum agrees with scalar multiplication by the
exponential. -/
@[simp]
theorem expFDeriv_eq_smul_one {R : Type*} [NormedCommRing R] [NormedAlgebra 𝕂 R]
    [CompleteSpace R] (x : R) :
    expFDeriv 𝕂 x = exp x • (1 : R →L[𝕂] R) :=
  (hasFDerivAt_exp (𝕂 := 𝕂) x).unique _root_.hasFDerivAt_exp

/-- At zero, the formal derivative-series operator is the identity continuous linear map. -/
@[simp]
theorem expFDeriv_zero {𝕂 R : Type*} [NontriviallyNormedField 𝕂] [NormedRing R]
    [NormedAlgebra 𝕂 R] : expFDeriv 𝕂 (0 : R) = 1 := by
  rw [expFDeriv]
  rw [tsum_eq_single 0]
  · ext y
    simp [expFDerivTerm]
  · intro n hn
    cases n with
    | zero => exact (hn rfl).elim
    | succ n =>
        ext y
        rw [expFDerivTerm_apply]
        have hsum :
            ∑ i ∈ Finset.range (n + 1 + 1), (0 : R) ^ (n + 1 - i) * y * 0 ^ i = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          by_cases hi_zero : i = 0
          · subst i
            simp
          · simp [zero_pow hi_zero]
        rw [hsum, smul_zero]
        simp

end TauCeti
