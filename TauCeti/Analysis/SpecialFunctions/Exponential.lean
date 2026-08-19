/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Duhamel formulas for the Banach-algebra exponential

This file expresses a finite increment of the exponential in a possibly noncommutative real
Banach algebra as an integral. Unlike a first-order derivative formula, the identity is exact for
every increment. It also derives the corresponding integral formula for the Fréchet derivative.

## Main results

* `intervalIntegrable_exp_smul_mul_mul_exp_smul`: a three-factor exponential integrand is interval
  integrable.
* `exp_add_sub_exp_eq_integral`: `exp (x + h) - exp x` is the integral of
  `exp ((1 - t) (x + h)) * h * exp (t x)` over the unit interval.
* `TauCeti.expFDeriv_apply_eq_integral`: the Fréchet derivative is the corresponding Duhamel
  integral linear in the increment.

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

/-- The three-factor exponential integrand underlying Duhamel's formulas is interval integrable. -/
theorem intervalIntegrable_exp_smul_mul_mul_exp_smul (x y z : A) :
    IntervalIntegrable
      (fun t : ℝ ↦ exp ((1 - t) • x) * y * exp (t • z)) volume 0 1 :=
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
    exact (intervalIntegrable_exp_smul_mul_mul_exp_smul (x + h) h x).neg
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
normed characteristic-zero field with continuous rational scalar action is the convergent series
whose `n`th homogeneous contribution inserts the tangent vector in every position among `n` copies
of the base point.

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

omit [CharZero 𝕂] [ContinuousSMul ℚ 𝕂] [CompleteSpace R] in
/-- The explicit insertion term is the corresponding term of Mathlib's derivative series for
the exponential formal multilinear series. -/
theorem expFDerivTerm_eq_derivSeries (x : R) (n : ℕ) :
    expFDerivTerm 𝕂 x n = (expSeries 𝕂 R).derivSeries n (fun _ ↦ x) := by
  ext y
  rw [expFDerivTerm_apply]
  simp only [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    FormalMultilinearSeries.changeOriginSeries, _root_.sum_apply]
  -- Extensionality and the preceding unfoldings reduce the equality definitionally to evaluating
  -- the curried change-origin term at `y`.
  change _ = continuousMultilinearCurryFin1 𝕂 R R _ y
  rw [continuousMultilinearCurryFin1_apply, _root_.sum_apply, Fin.snoc_zero]
  simp_rw [FormalMultilinearSeries.changeOriginSeriesTerm_apply]
  let e : Fin (n + 1) ≃ Fin (1 + n) := finCongr (Nat.add_comm n 1)
  have hsum :
      (∑ s : {s : Finset (Fin (1 + n)) // s.card = n},
          expSeries 𝕂 R (1 + n) (s.1.piecewise (fun _ ↦ x) fun _ ↦ y)) =
        ∑ i : Fin (n + 1),
          expSeries 𝕂 R (1 + n) (Function.update (fun _ ↦ x) (e i) y) := by
    refine (Fintype.sum_bijective
      ((fun a : Fin (1 + n) ↦ ⟨{a}ᶜ, by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
        omega⟩) ∘ e) (.comp ?_ e.bijective) _ _ fun i ↦ ?_).symm
    · use fun _ _ ↦
        (Finset.singleton_injective <| compl_injective <| Subtype.ext_iff.mp ·)
      intro ⟨s, hs⟩
      have h : sᶜ.card = 1 := by
        rw [Finset.card_compl, hs, Fintype.card_fin]
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      exact ⟨a, Subtype.ext (compl_eq_comm.mp ha)⟩
    · rw [Function.comp_apply, Subtype.coe_mk, Finset.compl_singleton,
        Finset.piecewise_erase_univ]
  rw [hsum]
  simp only [mul_assoc, expSeries, finCongr_apply, smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_eq_map,
    (List.nodup_finRange (1 + n)).map_update, List.mem_finRange, ↓reduceIte,
    List.map_const', List.length_finRange, List.idxOf_finRange, Fin.val_cast, List.prod_set,
    List.take_replicate, List.prod_replicate, List.length_replicate, mul_ite, mul_one,
    List.drop_replicate, ite_mul, smul_ite, e]
  have hi (i : Fin (n + 1)) : (i : ℕ) < 1 + n := by omega
  simp_rw [ite_eq_left (hi _), Nat.min_eq_left (hi _).le]
  have hsub (i : Fin (n + 1)) : 1 + n - ((i : ℕ) + 1) = n - i := by omega
  simp_rw [hsub]
  rw [Nat.add_comm 1 n]
  -- After normalizing the cardinality, the `Fin`-indexed summand is definitionally displayed as
  -- the corresponding function of its coerced natural-number index.
  change _ = ∑ i : Fin (n + 1),
    (fun j : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (x ^ j * (y * x ^ (n - j)))) i
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ ↦ ((n + 1).factorial⁻¹ : 𝕂) • (x ^ j * (y * x ^ (n - j))))]
  rw [← Finset.smul_sum]
  congr 1
  rw [← Finset.sum_range_reflect (fun j ↦ x ^ j * (y * x ^ (n - j))) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_sub_self (by omega : i ≤ n)]

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
theorem expFDeriv_eq_smul_one {𝕂 R : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
    [ContinuousSMul ℚ 𝕂] [NormedCommRing R] [NormedAlgebra 𝕂 R] [CompleteSpace R] (x : R) :
    expFDeriv 𝕂 x = exp x • (1 : R →L[𝕂] R) :=
  (hasFDerivAt_exp (𝕂 := 𝕂) x).unique
    (_root_.hasFDerivAt_exp_of_mem_ball
      ((expSeries_radius_eq_top 𝕂 R).symm ▸ edist_lt_top _ _))

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

section IntegralFormula

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

private noncomputable def expDerivativeIntegral (x y : A) (s : ℝ) : A :=
  ∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + s • y)) * y * exp (t • x)

private theorem continuous_expDerivativeIntegral (x y : A) :
    Continuous (expDerivativeIntegral x y) := by
  unfold expDerivativeIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

private theorem hasDerivAt_exp_add_smul_integral (x y : A) :
    HasDerivAt (fun s : ℝ ↦ exp (x + s • y)) (expDerivativeIntegral x y 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hG : Filter.Tendsto (expDerivativeIntegral x y)
      (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
      (nhds (expDerivativeIntegral x y 0)) :=
    (continuous_expDerivativeIntegral x y).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hG.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs
  have hduhamel := exp_add_sub_exp_eq_integral x (s • y)
  have hintegral :
      (∫ t in (0 : ℝ)..1, exp ((1 - t) • (x + s • y)) * (s • y) * exp (t • x)) =
        s • expDerivativeIntegral x y s := by
    rw [expDerivativeIntegral, ← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro t _ht
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [slope_def_module, sub_zero, zero_smul, add_zero, hduhamel, hintegral,
    inv_smul_smul₀ hs0]

private theorem expFDeriv_real_apply_eq_integral (x y : A) :
    expFDeriv ℝ x y =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • x) * y * exp (t • x) := by
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • y) y 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const y |>.const_add x
  have hseries : HasDerivAt (fun s : ℝ ↦ exp (x + s • y)) (expFDeriv ℝ x y) 0 := by
    simpa only [Function.comp_apply, zero_smul, add_zero] using!
      (hasFDerivAt_exp (𝕂 := ℝ) x).comp_hasDerivAt_of_eq 0 hline (by simp)
  simpa only [expDerivativeIntegral, zero_smul, add_zero] using
    hseries.unique (hasDerivAt_exp_add_smul_integral x y)

/-- The Fréchet derivative of the noncommutative exponential, applied to `y`, is its Duhamel
integral. -/
theorem expFDeriv_apply_eq_integral {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    [NormedAlgebra ℝ 𝕂] [NormedAlgebra 𝕂 A]
    [IsScalarTower ℝ 𝕂 A] (x y : A) :
    expFDeriv 𝕂 x y =
      ∫ t in (0 : ℝ)..1, exp ((1 - t) • x) * y * exp (t • x) := by
  let _ : CharZero 𝕂 := Algebra.charZero_of_charZero ℝ 𝕂
  let _ : IsScalarTower ℚ ℝ 𝕂 := IsScalarTower.of_algebraMap_eq fun q ↦ by simp [map_ratCast]
  let _ : ContinuousSMul ℚ 𝕂 := IsScalarTower.continuousSMul ℝ
  have hscalar :
      (expFDeriv 𝕂 x).restrictScalars ℝ = expFDeriv ℝ x :=
    ((hasFDerivAt_exp (𝕂 := 𝕂) x).restrictScalars ℝ).unique
      (hasFDerivAt_exp (𝕂 := ℝ) x)
  calc
    expFDeriv 𝕂 x y = expFDeriv ℝ x y := by
      simpa using congrArg (fun f : A →L[ℝ] A ↦ f y) hscalar
    _ = ∫ t in (0 : ℝ)..1, exp ((1 - t) • x) * y * exp (t • x) :=
      expFDeriv_real_apply_eq_integral x y

end IntegralFormula

end TauCeti
