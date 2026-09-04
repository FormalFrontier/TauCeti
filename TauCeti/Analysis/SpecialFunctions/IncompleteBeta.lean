/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.Calculus.RealCharts

/-!
# The regularized incomplete beta function

For positive shape parameters `a` and `b` the *regularized incomplete beta function* is
`I_x(a, b) = (∫ t in 0..x, t ^ (a - 1) * (1 - t) ^ (b - 1)) / Β(a, b)`, where `Β` is Euler's beta
function `ProbabilityTheory.beta`. It is the cumulative distribution function of the beta law, and
it also expresses the cumulative distribution functions of Student's `t`, Fisher's `F` and the
negative binomial law, together with the binomial tail.

`TauCeti.regularizedIncompleteBeta` clamps its argument to `[0, 1]`, so it is defined — and equal
to the cdf of the beta law — on all of `ℝ`. Outside the positive parameter range it is zero, with
one deliberate exception: `regularizedIncompleteBeta 0 b x = 1` for `0 < b` and `0 ≤ x`. This
records the cdf of the weak limit `betaMeasure a b → Measure.dirac 0` as `a → 0⁺`, and it is what
makes the binomial-tail formula `(binomial n p).real {k | m ≤ k} = I_p(m, n - m + 1)` hold at
`m = 0` without a separate case.

The real-variable theory of Euler's beta integral that the construction rests on lives in
`TauCeti/Analysis/SpecialFunctions/Beta.lean`.

## Main results

* `TauCeti.regularizedIncompleteBeta` — the definition;
* `TauCeti.regularizedIncompleteBeta_def_of_pos` and
  `TauCeti.regularizedIncompleteBeta_def_of_mem_Icc` — the defining normalized integral, with the
  clamp displayed and with the clamp already discharged on `[0, 1]`;
* `TauCeti.regularizedIncompleteBeta_zero_left` — the value `1` at the boundary `a = 0`;
* `TauCeti.regularizedIncompleteBeta_eq_zero_of_nonpos`,
  `TauCeti.regularizedIncompleteBeta_eq_zero_of_neg` and
  `TauCeti.regularizedIncompleteBeta_eq_one_of_one_le` — the values `0` and `1` off `(0, 1)`;
* `TauCeti.regularizedIncompleteBeta_eq_zero_of_neg_left` and
  `TauCeti.regularizedIncompleteBeta_eq_zero_of_nonpos_right` — the default value `0` outside the
  parameter range;
* `TauCeti.regularizedIncompleteBeta_monotone` — monotonicity, for every choice of parameters;
* `TauCeti.regularizedIncompleteBeta_nonneg` and `TauCeti.regularizedIncompleteBeta_le_one` —
  the range `[0, 1]`, for every choice of parameters;
* `TauCeti.continuous_regularizedIncompleteBeta` — continuity on all of `ℝ`;
* `TauCeti.hasDerivAt_regularizedIncompleteBeta` — the derivative on `(0, 1)`;
* `TauCeti.integral_Ioi_rpow_one_add_rpow_eq_interval_tail` and
  `TauCeti.integral_Ioi_rpow_one_add_rpow_tail_eq` — the second-beta-integral upper tail,
  rewritten through the incomplete beta function;
* `TauCeti.regularizedIncompleteBeta_symm` — the reflection formula
  `I_x(a, b) = 1 - I_{1-x}(b, a)`;
* `TauCeti.regularizedIncompleteBeta_one_right` and
  `TauCeti.regularizedIncompleteBeta_one_left` — the elementary values `x ^ a` and
  `1 - (1 - x) ^ b` at a unit parameter;
* `TauCeti.regularizedIncompleteBeta_add_one_left` and
  `TauCeti.regularizedIncompleteBeta_add_one_right` — the unit-step recurrences
  `I_x(a + 1, b) = I_x(a, b) - x ^ a * (1 - x) ^ b / (a * Β(a, b))` and
  `I_x(a, b + 1) = I_x(a, b) + x ^ a * (1 - x) ^ b / (b * Β(a, b))`, for `0 ≤ x ≤ 1`;
* `TauCeti.regularizedIncompleteBeta_add_one_right_sub_add_one_left` — the step along the
  antidiagonal `a + b = const`, whose increment is a generalized binomial coefficient.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 2, "Regularized incomplete beta".
* [NIST Digital Library of Mathematical Functions, §8.17](https://dlmf.nist.gov/8.17); the
  recurrence is [8.17.20](https://dlmf.nist.gov/8.17.E20).
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Set

variable {a b x : ℝ}

/-- The regularized incomplete beta function `I_x(a, b)`, extended to all real arguments by
clamping `x` to `[0, 1]`. It is zero outside the positive parameter range, except that
`regularizedIncompleteBeta 0 b x = 1` for `0 < b` and `0 ≤ x`; that convention records the cdf of
the weak limit of `betaMeasure a b` as `a → 0⁺`. -/
noncomputable def regularizedIncompleteBeta (a b x : ℝ) : ℝ :=
  if a = 0 ∧ 0 < b ∧ 0 ≤ x then 1
  else if 0 < a ∧ 0 < b then
    (∫ t in (0 : ℝ)..min 1 (max x 0), t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b
  else 0

/-- The clamped argument of `TauCeti.regularizedIncompleteBeta` lies in `[0, 1]`. -/
private lemma clamp_mem_Icc (x : ℝ) : min 1 (max x 0) ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_right x 0), min_le_left _ _⟩

/-- On the positive parameter range the regularized incomplete beta function is the normalized
integral of the beta integrand up to the clamped argument. -/
theorem regularizedIncompleteBeta_def_of_pos (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    regularizedIncompleteBeta a b x =
      (∫ t in (0 : ℝ)..min 1 (max x 0), t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · exact absurd h₁.1 ha.ne'
  · rfl
  · exact absurd ⟨ha, hb⟩ h₂

/-- On the support `[0, 1]` the clamp is invisible: the regularized incomplete beta function is
the normalized integral of the beta integrand up to `x` itself. This is the form in which the
cumulative distribution functions built from `TauCeti.regularizedIncompleteBeta` are used. -/
theorem regularizedIncompleteBeta_def_of_mem_Icc (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regularizedIncompleteBeta a b x =
      (∫ t in (0 : ℝ)..x, t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b := by
  rw [regularizedIncompleteBeta_def_of_pos ha hb, max_eq_left hx.1, min_eq_right hx.2]

/-- The boundary convention at `a = 0`: the regularized incomplete beta function is the cdf of
`Measure.dirac 0`, the weak limit of `betaMeasure a b` as `a → 0⁺`. -/
@[simp]
theorem regularizedIncompleteBeta_zero_left (hb : 0 < b) (hx : 0 ≤ x) :
    regularizedIncompleteBeta 0 b x = 1 := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · rfl
  · exact absurd ⟨rfl, hb, hx⟩ h₁
  · exact absurd ⟨rfl, hb, hx⟩ h₁

/-- The regularized incomplete beta function vanishes when its first parameter is negative: no
beta law is attached to such parameters, and the definition takes its default value there. -/
@[simp]
theorem regularizedIncompleteBeta_eq_zero_of_neg_left (ha : a < 0) (b x : ℝ) :
    regularizedIncompleteBeta a b x = 0 := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · exact absurd h₁.1 ha.ne
  · exact absurd h₂.1 (not_lt.2 ha.le)
  · rfl

/-- The regularized incomplete beta function vanishes when its second parameter is nonpositive.
Unlike the first parameter, the second admits no exceptional value at `0`: the weak limit of
`betaMeasure a b` as `b → 0⁺` is `Measure.dirac 1`, whose cdf is not the constant `1`. -/
@[simp]
theorem regularizedIncompleteBeta_eq_zero_of_nonpos_right (hb : b ≤ 0) (a x : ℝ) :
    regularizedIncompleteBeta a b x = 0 := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · exact absurd h₁.2.1 (not_lt.2 hb)
  · exact absurd h₂.2 (not_lt.2 hb)
  · rfl

/-- The regularized incomplete beta function vanishes strictly below the support of the beta law,
for every choice of parameters: the exceptional value `1` at `a = 0` is taken from `0` onwards. -/
@[simp]
theorem regularizedIncompleteBeta_eq_zero_of_neg (a b : ℝ) (hx : x < 0) :
    regularizedIncompleteBeta a b x = 0 := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · exact absurd h₁.2.2 (not_le.2 hx)
  · rw [max_eq_right hx.le, min_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_same, zero_div]
  · rfl

/-- The regularized incomplete beta function vanishes below the support of the beta law. The
hypothesis `a ≠ 0` is needed only at `x = 0`, where the boundary convention gives the value `1`;
`TauCeti.regularizedIncompleteBeta_eq_zero_of_neg` is the unconditional statement strictly below
`0`. -/
@[simp]
theorem regularizedIncompleteBeta_eq_zero_of_nonpos (ha : a ≠ 0) (b : ℝ) (hx : x ≤ 0) :
    regularizedIncompleteBeta a b x = 0 := by
  rw [regularizedIncompleteBeta]
  split_ifs with h₁ h₂
  · exact absurd h₁.1 ha
  · rw [max_eq_right hx, min_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_same, zero_div]
  · rfl

/-- The regularized incomplete beta function is `1` above the support of the beta law, including
at the boundary parameter `a = 0`. -/
@[simp]
theorem regularizedIncompleteBeta_eq_one_of_one_le (ha : 0 ≤ a) (hb : 0 < b) (hx : 1 ≤ x) :
    regularizedIncompleteBeta a b x = 1 := by
  rcases ha.eq_or_lt with rfl | ha
  · exact regularizedIncompleteBeta_zero_left hb (by linarith)
  · rw [regularizedIncompleteBeta_def_of_pos ha hb, max_eq_left (by linarith : (0 : ℝ) ≤ x),
      min_eq_left hx, integral_rpow_mul_one_sub_rpow ha hb, div_self (beta_pos ha hb).ne']

/-- The beta integrand is nonnegative on `[0, 1]`. -/
private lemma beta_integrand_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ t ^ (a - 1) * (1 - t) ^ (b - 1) :=
  mul_nonneg (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (by linarith [ht.2]) _)

/-- The regularized incomplete beta function is monotone, for every choice of parameters: it is a
normalized integral of a nonnegative density when `0 < a` and `0 < b`, the unit step at `0` when
`a = 0 < b`, and the zero function for all remaining parameters. -/
theorem regularizedIncompleteBeta_monotone (a b : ℝ) :
    Monotone (regularizedIncompleteBeta a b) := by
  rcases le_or_gt b 0 with hb | hb
  · exact fun x y _ => (regularizedIncompleteBeta_eq_zero_of_nonpos_right hb a x).le.trans
      (regularizedIncompleteBeta_eq_zero_of_nonpos_right hb a y).ge
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · exact fun x y _ => (regularizedIncompleteBeta_eq_zero_of_neg_left ha b x).le.trans
      (regularizedIncompleteBeta_eq_zero_of_neg_left ha b y).ge
  -- the boundary parameter `a = 0`, where the function is the unit step at `0`
  · intro x y hxy
    rcases le_or_gt 0 x with hx | hx
    · exact ((regularizedIncompleteBeta_zero_left hb hx).trans
        (regularizedIncompleteBeta_zero_left hb (hx.trans hxy)).symm).le
    · refine (regularizedIncompleteBeta_eq_zero_of_neg 0 b hx).le.trans ?_
      rcases le_or_gt 0 y with hy | hy
      · exact zero_le_one.trans (regularizedIncompleteBeta_zero_left hb hy).ge
      · exact (regularizedIncompleteBeta_eq_zero_of_neg 0 b hy).ge
  -- the positive parameter range, where the integrand is nonnegative
  · intro x y hxy
    have hx := clamp_mem_Icc x
    have hy := clamp_mem_Icc y
    have hle : min 1 (max x 0) ≤ min 1 (max y 0) := min_le_min le_rfl (max_le_max hxy le_rfl)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (f := fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) (μ := volume)
      (intervalIntegrable_rpow_mul_one_sub_rpow ha hb (mem_Icc.2 ⟨le_rfl, zero_le_one⟩) hx)
      (intervalIntegrable_rpow_mul_one_sub_rpow ha hb hx hy)
    have hnonneg : 0 ≤ ∫ t in (min 1 (max x 0))..(min 1 (max y 0)),
        t ^ (a - 1) * (1 - t) ^ (b - 1) :=
      intervalIntegral.integral_nonneg hle fun t ht =>
        beta_integrand_nonneg ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    rw [regularizedIncompleteBeta_def_of_pos ha hb, regularizedIncompleteBeta_def_of_pos ha hb]
    gcongr
    · exact (beta_pos ha hb).le
    · linarith

/-- The regularized incomplete beta function is nonnegative. -/
theorem regularizedIncompleteBeta_nonneg (a b x : ℝ) :
    0 ≤ regularizedIncompleteBeta a b x :=
  (regularizedIncompleteBeta_eq_zero_of_neg a b
      ((min_le_right x (-1)).trans_lt (by norm_num))).symm.trans_le
    (regularizedIncompleteBeta_monotone a b (min_le_left x (-1)))

/-- The regularized incomplete beta function is at most `1`. -/
theorem regularizedIncompleteBeta_le_one (a b x : ℝ) :
    regularizedIncompleteBeta a b x ≤ 1 := by
  rcases le_or_gt b 0 with hb | hb
  · exact (regularizedIncompleteBeta_eq_zero_of_nonpos_right hb a x).trans_le zero_le_one
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · exact (regularizedIncompleteBeta_eq_zero_of_neg_left ha b x).trans_le zero_le_one
  · rcases le_or_gt 0 x with hx | hx
    · exact (regularizedIncompleteBeta_zero_left hb hx).le
    · exact (regularizedIncompleteBeta_eq_zero_of_neg 0 b hx).trans_le zero_le_one
  · exact (regularizedIncompleteBeta_monotone a b (le_max_left x 1)).trans_eq
      (regularizedIncompleteBeta_eq_one_of_one_le ha.le hb (le_max_right x 1))

/-- The regularized incomplete beta function is continuous on all of `ℝ`, including at the two
endpoints of the support, where the integrand may blow up. -/
theorem continuous_regularizedIncompleteBeta (ha : 0 < a) (hb : 0 < b) :
    Continuous (regularizedIncompleteBeta a b) := by
  have hII := intervalIntegrable_rpow_mul_one_sub_rpow ha hb
    (u := 0) (v := 1) (mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (mem_Icc.2 ⟨zero_le_one, le_rfl⟩)
  have hc : Continuous fun x : ℝ =>
      ∫ t in (0 : ℝ)..min 1 (max x 0), t ^ (a - 1) * (1 - t) ^ (b - 1) :=
    (intervalIntegral.continuousOn_primitive_interval' hII left_mem_uIcc).comp_continuous
      (by fun_prop) fun x => by
        rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]; exact clamp_mem_Icc x
  have hfun : regularizedIncompleteBeta a b =
      fun x : ℝ => (∫ t in (0 : ℝ)..min 1 (max x 0), t ^ (a - 1) * (1 - t) ^ (b - 1)) / beta a b :=
    funext (regularizedIncompleteBeta_def_of_pos ha hb)
  rw [hfun]
  exact hc.div_const (beta a b)

/-- The derivative of the regularized incomplete beta function on the open unit interval is the
normalized beta density. No differentiability is claimed at the endpoints: for `a < 1` or `b < 1`
the density is unbounded there. -/
theorem hasDerivAt_regularizedIncompleteBeta (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (regularizedIncompleteBeta a b)
      (x ^ (a - 1) * (1 - x) ^ (b - 1) / beta a b) x := by
  have hII := intervalIntegrable_rpow_mul_one_sub_rpow ha hb
    (u := 0) (v := x) (mem_Icc.2 ⟨le_rfl, zero_le_one⟩) (mem_Icc.2 ⟨hx0.le, hx1.le⟩)
  have hmble : Measurable fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1) := by fun_prop
  have hcont : ContinuousAt (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) x := by
    refine ContinuousAt.mul (Real.continuousAt_rpow_const x (a - 1) (Or.inl hx0.ne')) ?_
    exact ContinuousAt.rpow_const (by fun_prop) (Or.inl (sub_ne_zero_of_ne hx1.ne'))
  have hderiv := (intervalIntegral.integral_hasDerivAt_right hII
    hmble.stronglyMeasurable.stronglyMeasurableAtFilter hcont).div_const (beta a b)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx0 hx1] with y hy
  exact regularizedIncompleteBeta_def_of_mem_Icc ha hb ⟨hy.1.le, hy.2.le⟩

/-! ## Tails -/

/-- The upper tail of Euler's second beta integral, rewritten through the chart
`u ↦ u / (1 - u)`. -/
theorem integral_Ioi_rpow_one_add_rpow_eq_interval_tail {a b u0 : ℝ}
    (hu00 : 0 ≤ u0) (hu01 : u0 < 1) :
    ∫ w in Ioi (u0 / (1 - u0)), w ^ (a - 1) * (1 + w) ^ (-(a + b)) =
      ∫ u in Ioo u0 1, u ^ (a - 1) * (1 - u) ^ (b - 1) := by
  have hderiv : ∀ u ∈ Ioo u0 1,
      HasDerivWithinAt (fun u : ℝ => u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo u0 1) u :=
    fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt
  let k0 : ℝ → ℝ := fun w => w ^ (a - 1) * (1 + w) ^ (-(a + b))
  let k : ℝ → ℝ := fun u => u ^ (a - 1) * (1 - u) ^ (b - 1)
  have hsub : Ioo u0 1 ⊆ Ioo (0 : ℝ) 1 := fun u hu =>
    ⟨lt_of_le_of_lt hu00 hu.1, hu.2⟩
  have hcov : ∀ u ∈ Ioo u0 1, |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) = k u := by
    intro u hu
    simpa [k0, k] using abs_deriv_smul_one_add_rpow a b (hsub hu)
  have himg :
      (fun u : ℝ => u / (1 - u)) '' Ioo u0 1 = Ioi (u0 / (1 - u0)) := by
    rw [image_div_one_sub_Ioo hu01]
  have h21 : ∫ u in Ioo u0 1, |((1 - u) ^ 2)⁻¹| • k0 (u / (1 - u)) =
      ∫ w in Ioi (u0 / (1 - u0)), k0 w := by
    rw [← integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv
        (injOn_div_one_sub_Ioo (u0 := u0)) k0, himg]
  have h2 : ∫ w in Ioi (u0 / (1 - u0)), k0 w = ∫ u in Ioo u0 1, k u := by
    rw [← h21, setIntegral_congr_fun measurableSet_Ioo hcov]
  simpa [k0, k] using h2

/-- The upper tail of the first beta-integral kernel is the total beta mass minus the normalized
lower incomplete beta mass. -/
theorem integral_Ioo_rpow_one_sub_rpow_tail_eq {a b u0 : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu00 : 0 ≤ u0) (hu01 : u0 < 1) :
    ∫ u in Ioo u0 1, u ^ (a - 1) * (1 - u) ^ (b - 1) =
      beta a b * (1 - regularizedIncompleteBeta a b u0) := by
  let k : ℝ → ℝ := fun u => u ^ (a - 1) * (1 - u) ^ (b - 1)
  have hmem01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmemu0 : u0 ∈ Icc (0 : ℝ) 1 := ⟨hu00, by linarith⟩
  have hII : IntervalIntegrable k volume 0 1 :=
    intervalIntegrable_rpow_mul_one_sub_rpow ha hb hmem01 hmem11
  have hIIu : IntervalIntegrable k volume 0 u0 :=
    intervalIntegrable_rpow_mul_one_sub_rpow ha hb hmem01 hmemu0
  have hmemu0' : u0 ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hmemu0
  have hmem11' : (1 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact hmem11
  have hII1 : IntervalIntegrable k volume u0 1 :=
    hII.mono_set (Set.uIcc_subset_uIcc hmemu0' hmem11')
  have h41 : Ioo u0 1 =ᵐ[volume] Ioc u0 1 :=
    Ioo_ae_eq_Ioc' Real.volume_singleton
  have h4 : ∫ u in Ioo u0 1, k u = ∫ u in u0..(1 : ℝ), k u := by
    rw [setIntegral_congr_set h41, intervalIntegral.integral_of_le (by linarith : u0 ≤ 1)]
  have h5 := intervalIntegral.integral_add_adjacent_intervals hIIu hII1
  have h6 : ∫ t in (0 : ℝ)..(1 : ℝ), k t = beta a b :=
    integral_rpow_mul_one_sub_rpow ha hb
  have h3 : ∫ u in Ioo u0 1, k u = beta a b - ∫ u in (0 : ℝ)..u0, k u := by
    rw [h4]
    linarith [h5, h6]
  have h71 : regularizedIncompleteBeta a b u0 =
      (∫ t in (0 : ℝ)..u0, k t) / beta a b :=
    regularizedIncompleteBeta_def_of_mem_Icc ha hb hmemu0
  have hbetane : beta a b ≠ 0 := (beta_pos ha hb).ne'
  have h7 : ∫ t in (0 : ℝ)..u0, k t = beta a b * regularizedIncompleteBeta a b u0 := by
    have : regularizedIncompleteBeta a b u0 =
        (∫ t in (0 : ℝ)..u0, k t) / beta a b := h71
    rw [this]
    field_simp [hbetane]
  have htailval : beta a b - beta a b * regularizedIncompleteBeta a b u0 =
      beta a b * (1 - regularizedIncompleteBeta a b u0) := by ring
  rw [h3, h7, htailval]

/-- The upper tail of Euler's second beta integral, expressed by the regularized incomplete beta
function. -/
theorem integral_Ioi_rpow_one_add_rpow_tail_eq {a b u0 : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu00 : 0 ≤ u0) (hu01 : u0 < 1) :
    ∫ w in Ioi (u0 / (1 - u0)), w ^ (a - 1) * (1 + w) ^ (-(a + b)) =
      beta a b * (1 - regularizedIncompleteBeta a b u0) := by
  rw [integral_Ioi_rpow_one_add_rpow_eq_interval_tail hu00 hu01,
    integral_Ioo_rpow_one_sub_rpow_tail_eq ha hb hu00 hu01]

/-- The reflection formula `I_x(a, b) = 1 - I_{1-x}(b, a)`, valid at every real argument: the
clamping convention makes both sides constant outside `[0, 1]`, so no restriction on `x` is
needed. Positivity of both parameters is needed, however: at `a = 0 < b` and `x < 0` the left
side is `0` while the right side is `1`, because `regularizedIncompleteBeta b 0` vanishes
identically. -/
theorem regularizedIncompleteBeta_symm (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    regularizedIncompleteBeta a b x = 1 - regularizedIncompleteBeta b a (1 - x) := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · rw [regularizedIncompleteBeta_eq_zero_of_neg a b hx0,
      regularizedIncompleteBeta_eq_one_of_one_le hb.le ha (by linarith), sub_self]
  rcases lt_or_ge 1 x with hx1 | hx1
  · rw [regularizedIncompleteBeta_eq_one_of_one_le ha.le hb hx1.le,
      regularizedIncompleteBeta_eq_zero_of_neg b a (by linarith), sub_zero]
  have hmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hmem' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hflip : (fun t : ℝ => t ^ (b - 1) * (1 - t) ^ (a - 1)) =
      fun t : ℝ => (fun s : ℝ => s ^ (a - 1) * (1 - s) ^ (b - 1)) (1 - t) := by
    funext t
    simp only [sub_sub_cancel]
    rw [mul_comm]
  have hsub : ∫ t in (0 : ℝ)..(1 - x), t ^ (b - 1) * (1 - t) ^ (a - 1) =
      ∫ t in x..1, t ^ (a - 1) * (1 - t) ^ (b - 1) := by
    rw [hflip, intervalIntegral.integral_comp_sub_left
      (fun s : ℝ => s ^ (a - 1) * (1 - s) ^ (b - 1)) 1]
    norm_num
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (b - 1)) (μ := volume)
    (intervalIntegrable_rpow_mul_one_sub_rpow ha hb (mem_Icc.2 ⟨le_rfl, zero_le_one⟩) hmem)
    (intervalIntegrable_rpow_mul_one_sub_rpow ha hb hmem (mem_Icc.2 ⟨zero_le_one, le_rfl⟩))
  rw [integral_rpow_mul_one_sub_rpow ha hb] at hadd
  rw [regularizedIncompleteBeta_def_of_mem_Icc ha hb hmem,
    regularizedIncompleteBeta_def_of_mem_Icc hb ha hmem', hsub, beta_comm b a,
    eq_sub_iff_add_eq, ← add_div, hadd, div_self (beta_pos ha hb).ne']

/-! ## Boundary parameter values -/

/-- At second parameter `1` the beta integrand loses its second factor, and the regularized
incomplete beta function is the power `x ^ a`. -/
@[simp]
theorem regularizedIncompleteBeta_one_right (ha : 0 < a) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a 1 x = x ^ a := by
  have hexp : a - 1 + 1 = a := by ring
  rw [regularizedIncompleteBeta_def_of_mem_Icc ha one_pos ⟨hx0, hx1⟩, beta_one_right ha]
  simp only [sub_self, Real.rpow_zero, mul_one]
  rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < a - 1)), hexp, Real.zero_rpow ha.ne',
    sub_zero]
  field_simp

/-- At first parameter `1` the reflection formula turns
`TauCeti.regularizedIncompleteBeta_one_right` into the complementary power `1 - (1 - x) ^ b`. -/
@[simp]
theorem regularizedIncompleteBeta_one_left (hb : 0 < b) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta 1 b x = 1 - (1 - x) ^ b := by
  rw [regularizedIncompleteBeta_symm one_pos hb x,
    regularizedIncompleteBeta_one_right hb (by linarith) (by linarith)]

/-! ## The unit-step recurrence -/

/-- The unit-step recurrence in the first parameter,
`I_x(a + 1, b) = I_x(a, b) - x ^ a * (1 - x) ^ b / (a * Β(a, b))`, in the form of
[DLMF 8.17.20](https://dlmf.nist.gov/8.17.E20).

The argument is restricted to `0 ≤ x ≤ 1`: outside `[0, 1]` the clamping freezes both regularized
values at `0` or at `1` while the subtracted term keeps varying with `x`, so the displayed formula
fails there. -/
theorem regularizedIncompleteBeta_add_one_left (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta (a + 1) b x = regularizedIncompleteBeta a b x -
      x ^ a * (1 - x) ^ b / (a * beta a b) := by
  have ha1 : (0 : ℝ) < a + 1 := by linarith
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  have hab : (0 : ℝ) < a + b := by linarith
  have hmem : x ∈ Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  -- the two integrals produced by the derivative of `t ^ a * (1 - t) ^ b`
  have hJ : IntervalIntegrable (fun t : ℝ => t ^ a * (1 - t) ^ (b - 1)) volume 0 x := by
    simpa using intervalIntegrable_rpow_mul_one_sub_rpow ha1 hb hzero hmem
  have hA : IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ b) volume 0 x := by
    simpa using intervalIntegrable_rpow_mul_one_sub_rpow ha hb1 hzero hmem
  -- the fundamental theorem of calculus applied to `t ^ a * (1 - t) ^ b`, whose derivative is
  -- asked for only on the open interval, where neither endpoint singularity is met
  have hftc : ∫ t in (0 : ℝ)..x, (a * (t ^ (a - 1) * (1 - t) ^ b) -
      b * (t ^ a * (1 - t) ^ (b - 1))) = x ^ a * (1 - x) ^ b := by
    have hcontf : ContinuousOn (fun t : ℝ => t ^ a * (1 - t) ^ b) (Icc 0 x) :=
      ((Real.continuous_rpow_const ha.le).mul
        ((continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hb.le)).continuousOn
    have hderivf : ∀ t ∈ Ioo (0 : ℝ) x, HasDerivWithinAt (fun t : ℝ => t ^ a * (1 - t) ^ b)
        (a * (t ^ (a - 1) * (1 - t) ^ b) - b * (t ^ a * (1 - t) ^ (b - 1))) (Ioi t) t :=
      fun t ht => (hasDerivAt_rpow_mul_one_sub_rpow a b (Or.inl ht.1.ne')
        (Or.inl (ht.2.trans_le hx1).ne)).hasDerivWithinAt
    have hint : IntervalIntegrable (fun t : ℝ => a * (t ^ (a - 1) * (1 - t) ^ b) -
        b * (t ^ a * (1 - t) ^ (b - 1))) volume 0 x := (hA.const_mul a).sub (hJ.const_mul b)
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx0 hcontf hderivf hint,
      Real.zero_rpow ha.ne', zero_mul, sub_zero]
  -- expand the integral of the derivative, and split off one power of `1 - t`
  rw [intervalIntegral.integral_sub (hA.const_mul a) (hJ.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_rpow_mul_one_sub_rpow_add_one_right ha hb hx0 hx1] at hftc
  rw [regularizedIncompleteBeta_def_of_mem_Icc ha1 hb hmem,
    regularizedIncompleteBeta_def_of_mem_Icc ha hb hmem, add_sub_cancel_right,
    beta_add_one_left ha.ne' hab.ne']
  have hbeta := (beta_pos ha hb).ne'
  field_simp [hbeta, ha.ne', hab.ne']
  linear_combination -hftc

/-- The unit-step recurrence in the second parameter,
`I_x(a, b + 1) = I_x(a, b) + x ^ a * (1 - x) ^ b / (b * Β(a, b))`.

It is the reflection of `TauCeti.regularizedIncompleteBeta_add_one_left`, and carries the same
restriction `0 ≤ x ≤ 1` for the same reason. -/
theorem regularizedIncompleteBeta_add_one_right (ha : 0 < a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a (b + 1) x = regularizedIncompleteBeta a b x +
      x ^ a * (1 - x) ^ b / (b * beta a b) := by
  have hstep := regularizedIncompleteBeta_add_one_left hb ha (by linarith : (0 : ℝ) ≤ 1 - x)
    (by linarith : (1 : ℝ) - x ≤ 1)
  rw [sub_sub_cancel, beta_comm b a] at hstep
  rw [regularizedIncompleteBeta_symm ha (by linarith : (0 : ℝ) < b + 1) x, hstep,
    regularizedIncompleteBeta_symm ha hb x]
  ring

/-- The step along the antidiagonal `a + b = const`, which is the recurrence the binomial tail
runs on:
`I_x(a, b + 1) - I_x(a + 1, b) = Γ(a + b + 1) / (Γ(a + 1) * Γ(b + 1)) * (x ^ a * (1 - x) ^ b)`.

The coefficient is the generalized binomial coefficient `(a + b).choose a`, so at natural
parameters `a = m` and `b = n - m` the right-hand side is the `m`-th binomial weight
`(n.choose m) * x ^ m * (1 - x) ^ (n - m)`.

The first parameter is only assumed nonnegative. At `a = 0` the identity reads
`1 - I_x(1, b) = (1 - x) ^ b`, which holds precisely because
`TauCeti.regularizedIncompleteBeta` takes the value `1` at first parameter `0`: the boundary
convention is what makes the antidiagonal recurrence start at `a = 0`. -/
theorem regularizedIncompleteBeta_add_one_right_sub_add_one_left (ha : 0 ≤ a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a (b + 1) x - regularizedIncompleteBeta (a + 1) b x =
      Real.Gamma (a + b + 1) / (Real.Gamma (a + 1) * Real.Gamma (b + 1)) *
        (x ^ a * (1 - x) ^ b) := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_zero_left (by linarith) hx0, zero_add,
      regularizedIncompleteBeta_one_left hb hx0 hx1, Real.rpow_zero, Real.Gamma_one, one_mul,
      zero_add, one_mul]
    field_simp
    ring
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have hGb := (Real.Gamma_pos_of_pos hb).ne'
  have hGab := (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  have hkey : 1 / (b * beta a b) + 1 / (a * beta a b) =
      Real.Gamma (a + b + 1) / (Real.Gamma (a + 1) * Real.Gamma (b + 1)) := by
    rw [ProbabilityTheory.beta, Real.Gamma_add_one ha.ne', Real.Gamma_add_one hb.ne',
      Real.Gamma_add_one (add_pos ha hb).ne']
    field_simp
  rw [regularizedIncompleteBeta_add_one_right ha hb hx0 hx1,
    regularizedIncompleteBeta_add_one_left ha hb hx0 hx1]
  linear_combination (x ^ a * (1 - x) ^ b) * hkey

end TauCeti
