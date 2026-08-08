/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.FDeriv.Pow
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

The Fréchet derivative of the exponential in a possibly noncommutative Banach algebra over a
normed characteristic-zero field is the convergent series whose `n`th homogeneous contribution
inserts the tangent vector in every position among `n` copies of the base point.

### Main definitions

* `TauCeti.expFDerivTerm`: the degree-`n` insertion term in the derivative series.
* `TauCeti.expFDeriv`: the sum of the derivative series as a continuous linear map.

### Main results

* `TauCeti.expFDerivTerm_apply`: the pointwise insertion formula for one term.
* `TauCeti.expFDerivTerm_eq_derivSeries`: the identification with Mathlib's formal derivative
  series.
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

/-- The sum of the Fréchet-derivative series of the Banach-algebra exponential. It converges under
the hypotheses of `summable_expFDerivTerm`; as usual for `tsum`, it has the junk value zero when
the series is not summable. -/
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

variable [NontriviallyNormedField 𝕂] [CharZero 𝕂] [ContinuousSMul ℚ 𝕂]
  [NormedRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R]

omit [CharZero 𝕂] [ContinuousSMul ℚ 𝕂] in
/-- The explicit insertion term is the corresponding term of Mathlib's derivative series for
the exponential formal multilinear series. -/
theorem expFDerivTerm_eq_derivSeries (x : R) (n : ℕ) :
    expFDerivTerm 𝕂 x n = (expSeries 𝕂 R).derivSeries n (fun _ ↦ x) := by
  let q : FormalMultilinearSeries 𝕂 R R := fun m ↦
    if m = n + 1 then expSeries 𝕂 R m else 0
  have hqzero : ∀ m, m ≠ n + 1 → q m = 0 := by
    intro m hm
    simp [q, hm]
  have hqrad : q.radius = ⊤ := by
    apply q.radius_eq_top_of_eventually_eq_zero
    filter_upwards [Filter.eventually_gt_atTop (n + 1)] with m hm
    exact hqzero m (Nat.ne_of_gt hm)
  have hqsum : q.sum = fun z : R ↦ ((n + 1).factorial⁻¹ : 𝕂) • z ^ (n + 1) := by
    funext z
    rw [FormalMultilinearSeries.sum, tsum_eq_single (n + 1)]
    · simp [q, expSeries, pow_succ']
    · intro m hm
      rw [hqzero m hm]
      simp
  have hqderiv : q.derivSeries.sum x = q.derivSeries n (fun _ ↦ x) := by
    rw [FormalMultilinearSeries.sum, tsum_eq_single n]
    intro m hm
    rw [q.derivSeries_eq_zero]
    · simp
    · apply hqzero
      omega
  have hqterm : q.derivSeries n = (expSeries 𝕂 R).derivSeries n := by
    ext v y
    simp [q, add_comm, FormalMultilinearSeries.derivSeries,
      FormalMultilinearSeries.changeOriginSeries,
      FormalMultilinearSeries.changeOriginSeriesTerm]
  have hx : ‖x‖ₑ < q.radius := by
    rw [hqrad]
    exact enorm_lt_top
  have hformal := q.hasFDerivAt_sum (x := x) hx
  rw [hqsum, hqderiv, hqterm] at hformal
  have hformal' : HasFDerivAt
      (((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1)))
      ((expSeries 𝕂 R).derivSeries n (fun _ ↦ x)) x :=
    hformal.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z ↦ by simp)
  have hexplicit : HasFDerivAt
      (((n + 1).factorial⁻¹ : 𝕂) • (fun z : R ↦ z ^ (n + 1)))
      (expFDerivTerm 𝕂 x n) x := by
    simpa only [expFDerivTerm, Nat.pred_succ] using
      (hasFDerivAt_pow' (𝕜 := 𝕂) (n + 1) (x := x)).const_smul
        ((n + 1).factorial⁻¹ : 𝕂)
  exact hexplicit.unique hformal'

/-- The operator-valued derivative series is summable. -/
theorem summable_expFDerivTerm (x : R) : Summable (expFDerivTerm 𝕂 x) :=
  ((expSeries 𝕂 R).derivSeries.summable (by
    have hr : (expSeries 𝕂 R).derivSeries.radius = ⊤ := by
      apply top_unique
      rw [← expSeries_radius_eq_top 𝕂 R]
      exact (expSeries 𝕂 R).radius_le_radius_derivSeries
    rw [hr]
    rw [Metric.mem_eball, edist_zero_right]
    exact enorm_lt_top)).congr
      fun n ↦ (expFDerivTerm_eq_derivSeries (𝕂 := 𝕂) x n).symm

/-- Applying the derivative terms to a fixed tangent vector gives a summable series. -/
theorem summable_expFDerivTerm_apply (x y : R) :
    Summable (fun n : ℕ ↦ expFDerivTerm 𝕂 x n y) :=
  (summable_expFDerivTerm (𝕂 := 𝕂) x).mapL (ContinuousLinearMap.apply 𝕂 R y)

/-- The summed derivative operator takes a tangent vector to the corresponding insertion series. -/
@[simp]
theorem expFDeriv_apply (x y : R) :
    expFDeriv 𝕂 x y = ∑' n : ℕ, expFDerivTerm 𝕂 x n y := by
  exact (ContinuousLinearMap.apply 𝕂 R y).map_tsum (summable_expFDerivTerm x)

/-- The exponential in a possibly noncommutative Banach algebra has the convergent insertion sum
`expFDeriv 𝕂 x` as its Fréchet derivative at `x`. -/
theorem hasFDerivAt_exp (x : R) :
    HasFDerivAt exp (expFDeriv 𝕂 x) x := by
  have hx : ‖x‖ₑ < (expSeries 𝕂 R).radius := by
    rw [expSeries_radius_eq_top]
    exact enorm_lt_top
  have h := (expSeries 𝕂 R).hasFDerivAt_sum hx
  have hderiv : (expSeries 𝕂 R).derivSeries.sum x = expFDeriv 𝕂 x := by
    rw [FormalMultilinearSeries.sum, expFDeriv]
    apply tsum_congr
    intro n
    exact (expFDerivTerm_eq_derivSeries (𝕂 := 𝕂) x n).symm
  rw [hderiv] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦
    (expSeries_hasSum_exp (𝕂 := 𝕂) y).tsum_eq.symm)

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
theorem expFDeriv_eq_smul_one {𝕂 R : Type*} [RCLike 𝕂] [NormedCommRing R] [NormedAlgebra 𝕂 R]
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
