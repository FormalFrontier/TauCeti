/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.LevyKhintchine.Basic
import TauCeti.Analysis.CompletelyMonotone.Bernstein.OpenHalfLine
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Levy--Khintchine representation of Bernstein functions

This file proves the existence part of the converse Levy--Khintchine representation: every
Bernstein function is the sum of a nonnegative killing term, a nonnegative linear drift, and the
jump exponent of a Bernstein Levy measure. Uniqueness of the three parameters is proved in
`TauCeti.Analysis.CompletelyMonotone.Bernstein.LevyKhintchine.Uniqueness`.

The proof represents the completely monotone derivative by a measure `sigma`. The atom of
`sigma` at zero is the drift coefficient, while weighting `sigma` by `x⁻¹` away from zero gives
the Levy measure. Continuity of the Bernstein function at zero is exactly what makes the
truncated coordinate integrable against this weighted measure.

## Main declaration

* `TauCeti.IsBernsteinFunction.exists_eqOn_bernsteinLevyKhintchineExponent`: existence of a
  Levy--Khintchine triplet for a Bernstein function.
* `TauCeti.isBernsteinFunction_iff_exists_bernsteinLevyKhintchineExponent`: the resulting
  characterization of Bernstein functions.

## References

* R. Schilling, R. Song, Z. Vondracek, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 3.2.
* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Levy--Khintchine
  representation of Bernstein functions).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- `integratedLaplaceKernel a b x` is the integral of `exp (-t * x)` from `a` to `b`. -/
private noncomputable def integratedLaplaceKernel (a b : ℝ) (x : ℝ≥0) : ℝ :=
  ∫ t in a..b, Real.exp (-(t * (x : ℝ)))

private lemma integratedLaplaceKernel_nonneg {a b : ℝ} (hab : a ≤ b) (x : ℝ≥0) :
    0 ≤ integratedLaplaceKernel a b x := by
  exact intervalIntegral.integral_nonneg hab fun _ _ => Real.exp_nonneg _

private lemma continuous_integratedLaplaceKernel (a b : ℝ) :
    Continuous (integratedLaplaceKernel a b) := by
  unfold integratedLaplaceKernel
  fun_prop

private lemma integrable_uncurry_exp_neg_mul_restrict_uIoc
    {σ : Measure ℝ≥0} [SFinite σ] {a b : ℝ} (hab : a ≤ b)
    (hint : Integrable (fun x : ℝ≥0 => Real.exp (-(a * (x : ℝ)))) σ) :
    Integrable (Function.uncurry fun t (x : ℝ≥0) => Real.exp (-(t * (x : ℝ))))
      ((volume.restrict (uIoc a b)).prod σ) := by
  have hvol : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  refine ((integrable_const (1 : ℝ)).mul_prod hint).mono' (by fun_prop) ?_
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) (by fun_prop))]
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [uIoc_of_le hab] at ht
  filter_upwards with x
  simp only [Function.uncurry_apply_pair, one_mul]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right ht.1.le x.coe_nonneg))

private lemma integral_integratedLaplaceKernel_eq_sub
    {f : ℝ → ℝ} {σ : Measure ℝ≥0} (hσ : RepresentsLaplaceOnIoi σ (deriv f))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hf : IsBernsteinFunction f) :
    ∫ x, integratedLaplaceKernel a b x ∂σ = f b - f a := by
  let _ := hσ.sigmaFinite
  have hprod :=
    integrable_uncurry_exp_neg_mul_restrict_uIoc (b := b) hab (hσ.integrable ha)
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (deriv f t) t := by
    intro t ht
    exact (hf.differentiableOn.differentiableAt
      (isOpen_Ioi.mem_nhds (ha.trans ht.1))).hasDerivAt
  have hintDeriv : IntervalIntegrable (deriv f) volume a b :=
    (hf.deriv_isCompletelyMonotoneOnIoi.contDiffOn.continuousOn.mono
      (fun t ht => ha.trans_le ht.1)).intervalIntegrable_of_Icc hab
  calc
    ∫ x, integratedLaplaceKernel a b x ∂σ =
        ∫ t in a..b, ∫ x : ℝ≥0, Real.exp (-(t * (x : ℝ))) ∂σ := by
      unfold integratedLaplaceKernel
      exact (intervalIntegral_integral_swap hprod).symm
    _ = ∫ t in a..b, deriv f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      exact (laplaceTransform_apply σ t).symm.trans
        (hσ.eq_laplaceTransform (ha.trans_le ht.1)).symm
    _ = f b - f a := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hab (hf.continuousOn.mono (fun t ht => mem_Ici.mpr (ha.le.trans ht.1))) hderiv hintDeriv

private lemma integrable_integratedLaplaceKernel
    {f : ℝ → ℝ} {σ : Measure ℝ≥0} (hσ : RepresentsLaplaceOnIoi σ (deriv f))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (integratedLaplaceKernel a b) σ := by
  let _ := hσ.sigmaFinite
  have hprod :=
    integrable_uncurry_exp_neg_mul_restrict_uIoc (b := b) hab (hσ.integrable ha)
  have hright := hprod.integral_prod_right
  unfold integratedLaplaceKernel
  simpa only [intervalIntegral.integral_of_le hab, uIoc_of_le hab,
    Function.uncurry_apply_pair] using hright

private lemma integratedLaplaceKernel_self_add_one_eq_exp_mul (a : ℝ) (x : ℝ≥0) :
    integratedLaplaceKernel a (a + 1) x =
      Real.exp (-(a * (x : ℝ))) * integratedLaplaceKernel 0 1 x := by
  rw [integratedLaplaceKernel, integratedLaplaceKernel]
  have hshift := intervalIntegral.integral_comp_add_right
    (a := 0) (b := 1) (fun t : ℝ => Real.exp (-(t * (x : ℝ)))) a
  simp only [zero_add] at hshift
  rw [add_comm a 1, ← hshift]
  calc
    ∫ t in 0..1, Real.exp (-((t + a) * (x : ℝ))) =
        ∫ t in 0..1, Real.exp (-(a * (x : ℝ))) * Real.exp (-(t * (x : ℝ))) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      simp only
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-(a * (x : ℝ))) *
        ∫ t in 0..1, Real.exp (-(t * (x : ℝ))) :=
      intervalIntegral.integral_const_mul _ _

/-- A positive sequence `1 / (n + 1)` used to approach the endpoint zero. -/
private noncomputable def levyApproximationParameter (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

private lemma levyApproximationParameter_pos (n : ℕ) : 0 < levyApproximationParameter n := by
  exact one_div_pos.mpr (Nat.cast_add_one_pos n)

private lemma antitone_levyApproximationParameter : Antitone levyApproximationParameter := by
  apply antitone_nat_of_succ_le
  intro n
  unfold levyApproximationParameter
  gcongr
  omega

private lemma tendsto_levyApproximationParameter :
    Tendsto levyApproximationParameter atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private lemma tendsto_apply_levyApproximationParameter_add {f : ℝ → ℝ}
    (hf : IsBernsteinFunction f) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n => f (levyApproximationParameter n + c)) atTop (𝓝 (f c)) := by
  exact (hf.continuousOn.continuousWithinAt (mem_Ici.mpr hc)).tendsto.comp <|
    tendsto_nhdsWithin_iff.mpr
      ⟨by simpa using tendsto_levyApproximationParameter.add_const c,
        Eventually.of_forall fun n => mem_Ici.mpr
          (add_nonneg (levyApproximationParameter_pos n).le hc)⟩

private lemma integrable_integratedLaplaceKernel_zero_one
    {f : ℝ → ℝ} {σ : Measure ℝ≥0} (hf : IsBernsteinFunction f)
    (hσ : RepresentsLaplaceOnIoi σ (deriv f)) :
    Integrable (integratedLaplaceKernel 0 1) σ := by
  let q := integratedLaplaceKernel 0 1
  let G : ℕ → ℝ≥0 → ℝ := fun n x =>
    integratedLaplaceKernel (levyApproximationParameter n)
      (levyApproximationParameter n + 1) x
  have hG_int : ∀ n, Integrable (G n) σ := fun n =>
    integrable_integratedLaplaceKernel hσ (levyApproximationParameter_pos n)
      (by linarith : levyApproximationParameter n ≤ levyApproximationParameter n + 1)
  have hG_factor : ∀ n x, G n x =
      Real.exp (-(levyApproximationParameter n * (x : ℝ))) * q x :=
    fun n x => integratedLaplaceKernel_self_add_one_eq_exp_mul _ _
  have hq_nonneg : ∀ x, 0 ≤ q x :=
    integratedLaplaceKernel_nonneg zero_le_one
  have hG_nonneg : ∀ n x, 0 ≤ G n x := fun n x => by
    rw [hG_factor]
    exact mul_nonneg (Real.exp_nonneg _) (hq_nonneg x)
  -- Monotone convergence passes from the positive shifts to the endpoint kernel.
  have hG_mono : ∀ x, Monotone fun n => ENNReal.ofReal (G n x) := by
    intro x n m hnm
    apply ENNReal.ofReal_le_ofReal
    rw [hG_factor, hG_factor]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr <| neg_le_neg <| mul_le_mul_of_nonneg_right
        (antitone_levyApproximationParameter hnm) x.coe_nonneg)
      (hq_nonneg x)
  have hG_tendsto_real : ∀ x, Tendsto (fun n => G n x) atTop (𝓝 (q x)) := by
    intro x
    have hexp : Tendsto
        (fun n => Real.exp (-(levyApproximationParameter n * (x : ℝ)))) atTop (𝓝 1) := by
      have harg : Tendsto (fun n => -(levyApproximationParameter n * (x : ℝ))) atTop (𝓝 0) := by
        simpa [mul_comm] using
          tendsto_levyApproximationParameter.const_mul (-(x : ℝ))
      simpa only [Real.exp_zero] using harg.rexp
    simpa only [one_mul] using (hexp.mul_const (q x)).congr'
      (Eventually.of_forall fun n => hG_factor n x |>.symm)
  have hG_tendsto : ∀ x,
      Tendsto (fun n => ENNReal.ofReal (G n x)) atTop (𝓝 (ENNReal.ofReal (q x))) :=
    fun x => ENNReal.tendsto_ofReal (hG_tendsto_real x)
  have hlin_tendsto := lintegral_tendsto_of_tendsto_of_monotone
    (μ := σ) (f := fun n x => ENNReal.ofReal (G n x))
    (F := fun x => ENNReal.ofReal (q x))
    (fun n => (hG_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (ae_of_all _ hG_mono) (ae_of_all _ hG_tendsto)
  -- Continuity at zero identifies the limiting integral with `f 1 - f 0`.
  have hε_zero : Tendsto (fun n => f (levyApproximationParameter n)) atTop (𝓝 (f 0)) :=
    by simpa using tendsto_apply_levyApproximationParameter_add hf le_rfl
  have hε_one : Tendsto (fun n => f (levyApproximationParameter n + 1)) atTop (𝓝 (f 1)) :=
    tendsto_apply_levyApproximationParameter_add hf zero_le_one
  have hvalues : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂σ) atTop
      (𝓝 (ENNReal.ofReal (f 1 - f 0))) := by
    have hlim := ENNReal.tendsto_ofReal (hε_one.sub hε_zero)
    refine hlim.congr' ?_
    filter_upwards with n
    rw [← ofReal_integral_eq_lintegral_ofReal (hG_int n) (ae_of_all _ (hG_nonneg n)),
      integral_integratedLaplaceKernel_eq_sub hσ (levyApproximationParameter_pos n)
        (by linarith) hf]
  have hlintegral : ∫⁻ x, ENNReal.ofReal (q x) ∂σ = ENNReal.ofReal (f 1 - f 0) :=
    tendsto_nhds_unique hlin_tendsto hvalues
  refine ⟨continuous_integratedLaplaceKernel 0 1 |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hq_nonneg), hlintegral]
  exact ENNReal.ofReal_lt_top

private lemma integratedLaplaceKernel_zero_one_eq (x : ℝ≥0) :
    integratedLaplaceKernel 0 1 x =
      if x = 0 then 1 else (1 - Real.exp (-(x : ℝ))) / (x : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simp [integratedLaplaceKernel, intervalIntegral.integral_const]
  · simp only [hx, ↓reduceIte]
    have hx_real : (x : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hx
    -- Commute the product in the exponent to match the input shape of
    -- `intervalIntegral.integral_comp_mul_left`.
    rw [integratedLaplaceKernel, show (fun t : ℝ => Real.exp (-(t * (x : ℝ)))) =
      fun t => Real.exp (-(x : ℝ) * t) by funext t; congr 1; ring,
      intervalIntegral.integral_comp_mul_left (f := Real.exp) (c := -(x : ℝ))
        (neg_ne_zero.mpr hx_real), integral_exp]
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    field_simp
    ring

private lemma min_one_mul_inv_le_exp_mul_one_sub_exp_neg_mul_inv {x : ℝ} (hx : 0 ≤ x) :
    min 1 x * x⁻¹ ≤ Real.exp 1 * ((1 - Real.exp (-x)) * x⁻¹) := by
  by_cases hx_zero : x = 0
  · simp [hx_zero]
  have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx_zero)
  have hmain : min 1 x ≤ Real.exp 1 * (1 - Real.exp (-x)) := by
    by_cases hx_one : x ≤ 1
    · rw [min_eq_right hx_one]
      have hdiff : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
      have hfactor : 1 ≤ Real.exp (1 - x) := by
        calc
          1 = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (1 - x) := Real.exp_le_exp.mpr (by linarith)
      calc
        x ≤ Real.exp (1 - x) * x := by nlinarith
        _ ≤ Real.exp (1 - x) * (Real.exp x - 1) :=
          mul_le_mul_of_nonneg_left hdiff (Real.exp_nonneg _)
        _ = Real.exp 1 * (1 - Real.exp (-x)) := by
          rw [mul_sub, mul_one, ← Real.exp_add]
          have hsum : Real.exp (1 - x + x) = Real.exp 1 := by
            congr 1
            ring
          have hsplit : Real.exp (1 - x) = Real.exp 1 * Real.exp (-x) := by
            rw [← Real.exp_add]
            congr 1
          rw [hsum, hsplit]
          ring
    · rw [min_eq_left (le_of_not_ge hx_one)]
      have htwo : 2 ≤ Real.exp 1 := by
        linarith [Real.add_one_le_exp (1 : ℝ)]
      have hprod : Real.exp 1 * Real.exp (-x) ≤ 1 := by
        calc
          Real.exp 1 * Real.exp (-x) = Real.exp (1 - x) := by
            rw [← Real.exp_add]
            congr 1
          _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
          _ = 1 := Real.exp_zero
      nlinarith
  calc
    min 1 x * x⁻¹ ≤ (Real.exp 1 * (1 - Real.exp (-x))) * x⁻¹ :=
      mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hx)
    _ = Real.exp 1 * ((1 - Real.exp (-x)) * x⁻¹) := by ring

private lemma coe_inv_mul_min_le_exp_mul_integratedLaplaceKernel (x : ℝ≥0) :
    (x⁻¹ : ℝ) * min 1 (x : ℝ) ≤
      Real.exp 1 * integratedLaplaceKernel 0 1 x := by
  by_cases hx : x = 0
  · subst x
    simpa only [inv_zero, NNReal.coe_zero, zero_le_one, inf_of_le_right, mul_zero] using
      mul_nonneg (Real.exp_nonneg 1) (integratedLaplaceKernel_nonneg zero_le_one 0)
  rw [mul_comm, integratedLaplaceKernel_zero_one_eq]
  simp only [hx, ↓reduceIte, div_eq_mul_inv]
  exact min_one_mul_inv_le_exp_mul_one_sub_exp_neg_mul_inv x.coe_nonneg

/-- Weight a Laplace representing measure by `x⁻¹` to obtain its Bernstein Levy measure. -/
private noncomputable def bernsteinLevyMeasureOfLaplaceMeasure
    (σ : Measure ℝ≥0) : Measure ℝ≥0 :=
  σ.withDensity fun x => ((x⁻¹ : ℝ≥0) : ℝ≥0∞)

private lemma isBernsteinLevyMeasure_bernsteinLevyMeasureOfLaplaceMeasure
    {f : ℝ → ℝ} {σ : Measure ℝ≥0} (hf : IsBernsteinFunction f)
    (hσ : RepresentsLaplaceOnIoi σ (deriv f)) :
    IsBernsteinLevyMeasure (bernsteinLevyMeasureOfLaplaceMeasure σ) := by
  rw [isBernsteinLevyMeasure_iff]
  constructor
  · rw [bernsteinLevyMeasureOfLaplaceMeasure,
      withDensity_apply _ (measurableSet_singleton (0 : ℝ≥0))]
    simp
  · rw [bernsteinLevyMeasureOfLaplaceMeasure,
      integrable_withDensity_iff_integrable_smul measurable_inv]
    have hmeas : AEStronglyMeasurable
        (fun x : ℝ≥0 => (x⁻¹ : ℝ) * min 1 (x : ℝ)) σ := by
      exact ((measurable_inv.coe_nnreal_real).mul
        (by fun_prop)).aestronglyMeasurable
    refine ((integrable_integratedLaplaceKernel_zero_one hf hσ).const_mul (Real.exp 1)).mono'
      hmeas ?_
    filter_upwards with x
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (x⁻¹).coe_nonneg (le_min zero_le_one x.coe_nonneg))]
    exact coe_inv_mul_min_le_exp_mul_integratedLaplaceKernel x

private lemma singleton_zero_add_integral_withDensity_inv_eq_integral
    {σ : Measure ℝ≥0} {t : ℝ}
    (hint : Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ)))) σ) :
    (σ {0}).toReal +
        ∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ)))
          ∂bernsteinLevyMeasureOfLaplaceMeasure σ =
      ∫ x : ℝ≥0, Real.exp (-(t * (x : ℝ))) ∂σ := by
  have hweighted :
      (∫ x : ℝ≥0, (x : ℝ) * Real.exp (-(t * (x : ℝ)))
          ∂bernsteinLevyMeasureOfLaplaceMeasure σ) =
        ∫ x : ℝ≥0 in {0}ᶜ, Real.exp (-(t * (x : ℝ))) ∂σ := by
    rw [bernsteinLevyMeasureOfLaplaceMeasure,
      integral_withDensity_eq_integral_smul measurable_inv,
      ← integral_indicator (measurableSet_singleton (0 : ℝ≥0)).compl]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x = 0
    · subst x
      simp
    · simp only [Set.indicator_of_mem (mem_compl_singleton_iff.mpr hx), NNReal.smul_def,
        NNReal.coe_inv]
      rw [smul_eq_mul]
      field_simp
  have hsingleton :
      ∫ x : ℝ≥0 in {0}, Real.exp (-(t * (x : ℝ))) ∂σ = (σ {0}).toReal := by
    simp
  rw [hweighted, ← hsingleton]
  rw [← integral_add_measure
    (hint.mono_measure Measure.restrict_le_self)
    (hint.mono_measure Measure.restrict_le_self)]
  rw [Measure.restrict_add_restrict_compl (μ := σ) (measurableSet_singleton 0)]

/-- Every Bernstein function admits a Levy--Khintchine representation on the nonnegative
half-line. The witnesses are a killing coefficient, a drift coefficient, and a Levy measure;
this theorem asserts existence only. -/
theorem IsBernsteinFunction.exists_eqOn_bernsteinLevyKhintchineExponent {f : ℝ → ℝ}
    (hf : IsBernsteinFunction f) :
    ∃ a b : ℝ, ∃ μ : Measure ℝ≥0,
      0 ≤ a ∧ 0 ≤ b ∧ IsBernsteinLevyMeasure μ ∧
        Set.EqOn f (bernsteinLevyKhintchineExponent a b μ) (Ici 0) := by
  obtain ⟨σ, hσ⟩ :=
    exists_representsLaplaceOnIoi_of_isCompletelyMonotoneOnIoi
      hf.deriv_isCompletelyMonotoneOnIoi
  let _ := hσ.sigmaFinite
  set a := f 0 with ha_eq
  set b := (σ {0}).toReal with hb_eq
  set μ := bernsteinLevyMeasureOfLaplaceMeasure σ with hμ_eq
  have ha : 0 ≤ a := hf.nonneg le_rfl
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hμ : IsBernsteinLevyMeasure μ :=
    isBernsteinLevyMeasure_bernsteinLevyMeasureOfLaplaceMeasure hf hσ
  set g := bernsteinLevyKhintchineExponent a b μ with hg_eq
  have hg : IsBernsteinFunction g :=
    isBernsteinFunction_bernsteinLevyKhintchineExponent hμ ha hb
  have hderiv : Set.EqOn (deriv f) (deriv g) (Ioi 0) := by
    intro t ht
    rw [hg_eq, deriv_bernsteinLevyKhintchineExponent hμ.integrable_min_one a b ht]
    rw [hb_eq, hμ_eq,
      singleton_zero_add_integral_withDensity_inv_eq_integral (hσ.integrable ht)]
    exact (hσ.eq_laplaceTransform ht).trans (laplaceTransform_apply σ t)
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq
    ordConnected_Ioi.isPreconnected hf.differentiableOn hg.differentiableOn hderiv
  have hf_zero : Tendsto (fun n => f (levyApproximationParameter n)) atTop (𝓝 (f 0)) :=
    by simpa using tendsto_apply_levyApproximationParameter_add hf le_rfl
  have hg_zero : Tendsto (fun n => g (levyApproximationParameter n)) atTop (𝓝 (g 0)) :=
    by simpa using tendsto_apply_levyApproximationParameter_add hg le_rfl
  have hfc_zero : Tendsto (fun n => g (levyApproximationParameter n) + c) atTop
      (𝓝 (g 0 + c)) := hg_zero.add_const c
  have hendpoint : f 0 = g 0 + c := tendsto_nhds_unique hf_zero <|
    hfc_zero.congr' <| Eventually.of_forall fun n =>
      (hc (levyApproximationParameter_pos n)).symm
  have hc_zero : c = 0 := by
    rw [hg_eq, bernsteinLevyKhintchineExponent_zero, ha_eq] at hendpoint
    linarith
  refine ⟨a, b, μ, ha, hb, hμ, ?_⟩
  intro t ht
  by_cases ht_zero : t = 0
  · subst t
    simp only [bernsteinLevyKhintchineExponent_zero, ha_eq]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    simpa only [hg_eq, hc_zero, add_zero] using hc ht_pos

/-- A function is Bernstein exactly when it has a Levy--Khintchine representation on the
nonnegative half-line. -/
theorem isBernsteinFunction_iff_exists_bernsteinLevyKhintchineExponent {f : ℝ → ℝ} :
    IsBernsteinFunction f ↔
      ∃ a b : ℝ, ∃ μ : Measure ℝ≥0,
        0 ≤ a ∧ 0 ≤ b ∧ IsBernsteinLevyMeasure μ ∧
          Set.EqOn f (bernsteinLevyKhintchineExponent a b μ) (Ici 0) := by
  constructor
  · exact fun hf => hf.exists_eqOn_bernsteinLevyKhintchineExponent
  · rintro ⟨a, b, μ, ha, hb, hμ, heq⟩
    exact (isBernsteinFunction_bernsteinLevyKhintchineExponent hμ ha hb).congr heq

end TauCeti

end
