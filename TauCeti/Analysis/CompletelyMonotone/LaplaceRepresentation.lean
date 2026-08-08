/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Moments.Basic
public import TauCeti.Analysis.CompletelyMonotone.Basic
-- Non-public: the `mgf` derivative and analyticity calculus, consumed through the bridge
-- `laplaceTransform_eq_mgf` in proofs only.
import Mathlib.Probability.Moments.MGFAnalytic
-- Non-public: `Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq` supplies the
-- Laplace-determinacy step in the uniqueness proof.
import TauCeti.Probability.Moments.LaplaceDeterminacy

/-!
# Laplace representations for completely monotone functions

This file contains the Laplace-transform side of the finite-measure
Hausdorff--Bernstein--Widder theorem on `ℝ≥0`: helper lemmas for finite-measure Laplace
transforms and the predicate that a finite measure represents a function by its Laplace transform.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV. This file provides
the Laplace-transform API used by the finite-measure representation theorem.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Pointwise Topology

namespace TauCeti

/-! ## Laplace transforms of finite measures on `ℝ≥0` -/

/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
noncomputable def laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. Not `@[simp]`: simp should not unfold the
abstraction into a raw integral; the evaluation lemmas below are the simp normal forms. -/
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := by
  rw [laplaceTransform]

/-- The Laplace kernel `p ↦ e^{-tp}` is continuous in the coordinate variable. -/
lemma continuous_exp_neg_mul (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ x` the Laplace kernel is bounded by `1` on `ℝ≥0`. -/
lemma exp_neg_mul_le_one {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    Real.exp (-(x * (p : ℝ))) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hx p.2)

/-- The limiting Laplace kernel as a bundled bounded continuous test function of the
nonnegative variable `p`, for fixed nonnegative `x`. -/
noncomputable def laplaceKernelBoundedContinuous {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ where
  toFun := fun p => Real.exp (-(x * (p : ℝ)))
  continuous_toFun := Real.continuous_exp.comp ((continuous_const.mul continuous_subtype_val).neg)
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 < Real.exp (-(x * (p : ℝ))) := Real.exp_pos _
      have hp1 := exp_neg_mul_le_one hx p
      have hq0 : 0 < Real.exp (-(x * (q : ℝ))) := Real.exp_pos _
      have hq1 := exp_neg_mul_le_one hx q
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled limiting Laplace kernel evaluates to the usual exponential kernel on `ℝ≥0`. -/
@[simp]
lemma laplaceKernelBoundedContinuous_apply {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    laplaceKernelBoundedContinuous hx p = Real.exp (-(x * (p : ℝ))) := by
  rw [laplaceKernelBoundedContinuous]; rfl

/-- **The Laplace kernel is integrable against a finite measure.** For `0 ≤ x` the kernel
`p ↦ e^{-xp}` is bounded and continuous on `ℝ≥0`, hence integrable against any finite measure. -/
lemma integrable_exp_neg_mul (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(x * (p : ℝ)))) μ := by
  have h := (laplaceKernelBoundedContinuous hx).integrable μ
  rwa [funext (laplaceKernelBoundedContinuous_apply hx)] at h

/-- The Laplace transform is the moment-generating function of the coordinate negation
`p ↦ -p` on `ℝ≥0`. This bridge lets the transform consume Mathlib's `mgf` calculus. -/
lemma laplaceTransform_eq_mgf (μ : Measure ℝ≥0) :
    laplaceTransform μ = mgf (fun p : ℝ≥0 => -(p : ℝ)) μ := by
  ext t
  simp only [laplaceTransform, mgf, mul_neg]

/-- The nonnegative half-line lies in the `integrableExpSet` of the bridge variable `p ↦ -p`:
this is `integrable_exp_neg_mul` restated for the moment-generating-function calculus. -/
private lemma Ici_subset_integrableExpSet (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    Ici (0 : ℝ) ⊆ integrableExpSet (fun p : ℝ≥0 => -(p : ℝ)) μ := fun t ht => by
  simpa [integrableExpSet, mul_neg] using integrable_exp_neg_mul μ (mem_Ici.mp ht)

private lemma Ioi_subset_interior_integrableExpSet (μ : Measure ℝ≥0)
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) :
    Ioi (0 : ℝ) ⊆ interior (integrableExpSet (fun p : ℝ≥0 => -(p : ℝ)) μ) := by
  have hsub : Ioi (0 : ℝ) ⊆ integrableExpSet (fun p : ℝ≥0 => -(p : ℝ)) μ := fun u hu => by
    simpa [integrableExpSet, mul_neg] using hint u hu
  intro t ht
  exact interior_mono hsub (by rwa [interior_Ioi])

/-- The value of the Laplace transform at the parameter `0` is the total mass (under the
total Bochner-integral convention both sides are `0` for an infinite measure). -/
@[simp]
lemma laplaceTransform_zero (μ : Measure ℝ≥0) :
    laplaceTransform μ 0 = μ.real univ := by
  rw [laplaceTransform_eq_mgf, mgf_zero']

/-- The Laplace transform of the zero measure vanishes identically. -/
@[simp]
lemma laplaceTransform_zero_measure (t : ℝ) :
    laplaceTransform (0 : Measure ℝ≥0) t = 0 := by
  simp [laplaceTransform_eq_mgf, mgf_zero_measure]

/-- The Laplace transform of a positive measure is nonnegative. -/
lemma laplaceTransform_nonneg (μ : Measure ℝ≥0) (t : ℝ) :
    0 ≤ laplaceTransform μ t := by
  rw [laplaceTransform_eq_mgf]
  exact mgf_nonneg

/-- Additivity of the Laplace transform in the measure, on the nonnegative half-line where the
kernel is integrable. -/
lemma laplaceTransform_add_measure (μ ν : Measure ℝ≥0) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0 ≤ t) :
    laplaceTransform (μ + ν) t = laplaceTransform μ t + laplaceTransform ν t := by
  simp only [laplaceTransform_eq_mgf]
  exact mgf_add_measure (Ici_subset_integrableExpSet μ ht) (Ici_subset_integrableExpSet ν ht)

/-- Scaling the measure by a finite scalar `c : ℝ≥0` scales the Laplace transform by `c`.

Stated for `c : ℝ≥0` rather than `ℝ≥0∞`: at the infinite scalar `∞ • μ` (infinite mass) the
Bochner integral returns its junk value and `∞.toReal = 0`, so an `ℝ≥0∞` form would falsely read
"scaling by infinity gives `0`". -/
lemma laplaceTransform_smul_measure (c : ℝ≥0) (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform ((c : ℝ≥0∞) • μ) t = (c : ℝ) * laplaceTransform μ t := by
  simp only [laplaceTransform_eq_mgf, mgf_smul_measure, ENNReal.coe_toReal]

/-- The Laplace transform of the Dirac mass at `x₀` is the exponential kernel `exp (-(t · x₀))`;
the point masses are the building blocks of the representing mixtures. -/
@[simp]
lemma laplaceTransform_dirac (x₀ : ℝ≥0) (t : ℝ) :
    laplaceTransform (Measure.dirac x₀) t = Real.exp (-(t * (x₀ : ℝ))) := by
  rw [laplaceTransform_eq_mgf, mgf_dirac', mul_neg]

/-! ## Easy direction: finite measures give completely monotone Laplace transforms -/

/-- The Laplace transform of a finite measure on `ℝ≥0` is continuous on `[0, ∞)`. -/
theorem continuousOn_Ici_laplaceTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ContinuousOn (laplaceTransform μ) (Ici 0) := by
  -- Dominated convergence in the parameter `t`, with the constant `1` as an integrable
  -- dominating function on the half-line.
  refine (continuousOn_of_dominated (μ := μ)
      (F := fun (t : ℝ) (x : ℝ≥0) => Real.exp (-(t * (x : ℝ))))
      (bound := fun _ : ℝ≥0 => (1 : ℝ)) (s := Ici (0 : ℝ))
      (by
        intro t _ht
        exact (continuous_exp_neg_mul t).aestronglyMeasurable)
      (by
        intro t ht
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact exp_neg_mul_le_one ht x)
      (integrable_const (1 : ℝ))
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        exact (by fun_prop :
          Continuous fun t : ℝ => Real.exp (-(t * (x : ℝ)))).continuousOn)).congr ?_
  intro t _
  simp only [laplaceTransform_apply]

/-- The `n`-th signed moment kernel integral attached to a Laplace transform.

For `0 < t`, this is the `n`-th ordinary derivative of `laplaceTransform μ` at `t`. -/
private noncomputable def laplaceMomentTransform (μ : Measure ℝ≥0) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ≥0, (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ))) ∂μ

/-- The signed moment kernel is nonnegative after multiplying by the complete-monotonicity sign. -/
private lemma neg_one_pow_mul_laplaceMomentTransform_nonneg
    (μ : Measure ℝ≥0) (n : ℕ) (t : ℝ) :
    0 ≤ (-1 : ℝ) ^ n * laplaceMomentTransform μ n t := by
  rw [laplaceMomentTransform]
  rw [← integral_const_mul]
  refine integral_nonneg fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp : 0 ≤ Real.exp (-(t * (x : ℝ))) := Real.exp_nonneg _
  have heq : (-1 : ℝ) ^ n * ((-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) =
      (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  simpa [heq] using mul_nonneg hpow hexp

/-- Integrability of the zeroth moment makes the measure finite. -/
private lemma isFiniteMeasure_of_integrable_moments
    (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    IsFiniteMeasure μ := by
  have hconst : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) μ := by
    simpa using hmom 0
  exact (integrable_const_iff_isFiniteMeasure (μ := μ)
    (by norm_num : (1 : ℝ) ≠ 0)).mp hconst



/-- Moment integrability controls the signed Laplace moment kernel on the closed half-line. -/
private lemma integrable_neg_pow_mul_exp_neg_mul (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ := by
  refine (hmom n).mono' (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp_le : Real.exp (-(t * (x : ℝ))) ≤ 1 := exp_neg_mul_le_one ht x
  calc
    ‖(-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))‖
        = (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
          rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg hx,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ (x : ℝ) ^ n := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hpow



/-- Differentiation of the signed Laplace moment kernels on `(0, ∞)`, supplied by Mathlib's
moment-generating-function calculus through the bridge variable `p ↦ -p`. -/
private lemma hasDerivAt_laplaceMomentTransform (μ : Measure ℝ≥0)
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) t) t := by
  have h := hasDerivAt_integral_pow_mul_exp_real
    (Ioi_subset_interior_integrableExpSet μ hint (mem_Ioi.mpr ht)) n
  simp only [mul_neg] at h
  exact h

private lemma abs_exp_neg_sub_one_le {a : ℝ} (ha : 0 ≤ a) :
    |Real.exp (-a) - 1| ≤ a := by
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)))]
  linarith [Real.one_sub_le_exp_neg a]

private lemma norm_slope_neg_pow_mul_exp_neg_mul_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y)
    (x : ℝ≥0) :
    ‖slope (fun z : ℝ => (-(x : ℝ)) ^ n * Real.exp (-(z * (x : ℝ)))) 0 y‖ ≤
      (x : ℝ) ^ (n + 1) := by
  by_cases hy_zero : y = 0
  · subst y
    simp
  have hy_pos : 0 < y := lt_of_le_of_ne' hy hy_zero
  have hx : 0 ≤ (x : ℝ) := x.2
  have harg_nonneg : 0 ≤ y * (x : ℝ) := mul_nonneg hy hx
  have hpow_abs : |(-(x : ℝ)) ^ n| = (x : ℝ) ^ n := by
    rw [abs_pow, abs_neg, abs_of_nonneg hx]
  have hquot :
      |(Real.exp (-(y * (x : ℝ))) - 1) / y| ≤ (x : ℝ) := by
    rw [abs_div, abs_of_pos hy_pos]
    exact (div_le_iff₀ hy_pos).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using
        abs_exp_neg_sub_one_le harg_nonneg)
  have hpow_nonneg : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  calc
    ‖slope (fun z : ℝ => (-(x : ℝ)) ^ n * Real.exp (-(z * (x : ℝ)))) 0 y‖
        = |(-(x : ℝ)) ^ n| * |(Real.exp (-(y * (x : ℝ))) - 1) / y| := by
          have hslope_rewrite :
              (((-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))) -
                    (-(x : ℝ)) ^ n) / y) =
                (-(x : ℝ)) ^ n * ((Real.exp (-(y * (x : ℝ))) - 1) / y) := by
            ring
          rw [Real.norm_eq_abs, slope_def_field]
          simp only [sub_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
          rw [hslope_rewrite, abs_mul]
    _ ≤ (x : ℝ) ^ n * (x : ℝ) := by
          simpa [hpow_abs] using mul_le_mul_of_nonneg_left hquot hpow_nonneg
    _ = (x : ℝ) ^ (n + 1) := by rw [pow_succ]

/-- One-sided differentiation under the integral at the endpoint `t = 0`: within `[0, ∞)` the
`n`-th signed moment kernel integral has the `(n+1)`-st as derivative, provided all moments are
finite. Dominated convergence over the pointwise slopes supplies the limit; the slope of the
integral is first exchanged with the integral of the slopes. -/
private lemma hasDerivWithinAt_laplaceMomentTransform_zero (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) (n : ℕ) :
    HasDerivWithinAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) 0)
      (Ici 0) 0 := by
  -- Stage 1: dominated convergence of the pointwise slopes, with the `(n+1)`-st moment as bound.
  let l : Filter ℝ := 𝓝[Ici (0 : ℝ) \ {0}] (0 : ℝ)
  let K : ℝ → ℝ≥0 → ℝ := fun y x =>
    (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ)))
  have hlim :
      Tendsto (fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ) l
        (𝓝 (∫ x : ℝ≥0, (-(x : ℝ)) ^ (n + 1) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (bound := fun x : ℝ≥0 => (x : ℝ) ^ (n + 1))
      ?_ ?_ (hmom (n + 1)) ?_
    · exact Filter.Eventually.of_forall fun y => by
        simpa [slope_def_field] using
          (by fun_prop : AEStronglyMeasurable
            (fun x : ℝ≥0 => (K y x - K 0 x) / (y - 0)) μ)
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      refine Filter.Eventually.of_forall fun x => ?_
      exact norm_slope_neg_pow_mul_exp_neg_mul_le n hy.1 x
    · refine Filter.Eventually.of_forall fun x => ?_
      have hderiv :
          HasDerivWithinAt (fun y : ℝ => K y x) ((-(x : ℝ)) ^ (n + 1)) (Ici 0) 0 := by
        have hlin : HasDerivAt (fun y : ℝ => -(y * (x : ℝ))) (-(x : ℝ)) 0 := by
          exact (hasDerivAt_mul_const (x : ℝ)).neg
        have hder := hlin.exp.const_mul ((-(x : ℝ)) ^ n)
        simpa [K, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hder.hasDerivWithinAt
      exact (hasDerivWithinAt_iff_tendsto_slope.mp hderiv)
  -- Stage 2: the slope of the integral is the integral of the pointwise slopes.
  have hslope :
      (fun y : ℝ => slope (laplaceMomentTransform μ n) 0 y)
        =ᶠ[l] fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ := by
    filter_upwards [eventually_mem_nhdsWithin] with y hy
    have hy_nonneg : 0 ≤ y := hy.1
    have hKy : Integrable (fun x : ℝ≥0 => K y x) μ :=
      integrable_neg_pow_mul_exp_neg_mul μ hmom n hy_nonneg
    have hK0 : Integrable (fun x : ℝ≥0 => K 0 x) μ :=
      integrable_neg_pow_mul_exp_neg_mul μ hmom n le_rfl
    calc
      slope (laplaceMomentTransform μ n) 0 y
          = (y - 0)⁻¹ *
              ((∫ x : ℝ≥0, K y x ∂μ) - ∫ x : ℝ≥0, K 0 x ∂μ) := by
                simp [slope_def_field, laplaceMomentTransform, K, div_eq_inv_mul]
      _ = (y - 0)⁻¹ * (∫ x : ℝ≥0, K y x - K 0 x ∂μ) := by
            rw [integral_sub hKy hK0]
      _ = ∫ x : ℝ≥0, (y - 0)⁻¹ * (K y x - K 0 x) ∂μ := by
            rw [integral_const_mul]
      _ = ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ := by
            simp [slope_def_field, div_eq_inv_mul]
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hlim' :
      Tendsto (fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ) l
        (𝓝 (laplaceMomentTransform μ (n + 1) 0)) := by
    simpa [laplaceMomentTransform] using hlim
  simpa [l] using Tendsto.congr' hslope.symm hlim'

/-- Differentiation under the integral for signed Laplace moment kernels within `[0, ∞)`.

At positive parameters this is the existing open-neighbourhood differentiation theorem; at `0`
it is the one-sided dominated-convergence argument using the next moment as a bound. -/
private lemma hasDerivWithinAt_laplaceMomentTransform_Ici (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) t)
      (Ici 0) t := by
  by_cases ht_pos : 0 < t
  · exact (hasDerivAt_laplaceMomentTransform μ
      (fun u hu => integrable_exp_neg_mul μ hu.le) n ht_pos).hasDerivWithinAt
  have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_pos) ht
  subst t
  exact hasDerivWithinAt_laplaceMomentTransform_zero μ hmom n

/-- The derivative within `[0, ∞)` of the `n`-th signed Laplace moment kernel is the next
signed moment kernel. -/
private lemma derivWithin_laplaceMomentTransform_eq (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (laplaceMomentTransform μ n) (Ici 0) t =
      laplaceMomentTransform μ (n + 1) t := by
  exact (hasDerivWithinAt_laplaceMomentTransform_Ici μ hmom n ht).derivWithin
    ((uniqueDiffOn_Ici (0 : ℝ)) t (mem_Ici.mpr ht))

/-- On the closed half-line, the iterated within-derivatives of a finite-measure Laplace transform
with all moments finite are the signed moment kernel integrals. -/
private lemma iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin n (laplaceTransform μ) (Ici 0) t =
      laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      calc
        derivWithin (iteratedDerivWithin n (laplaceTransform μ) (Ici 0)) (Ici 0) t
            = derivWithin (laplaceMomentTransform μ n) (Ici 0) t := by
              exact derivWithin_congr (fun y hy => ih hy) (ih ht)
        _ = laplaceMomentTransform μ (n + 1) t :=
              derivWithin_laplaceMomentTransform_eq μ hmom n ht

/-- If all moments of the representing measure are finite, its Laplace transform is smooth on the
closed half-line in the existing `iteratedDerivWithin` sense. -/
lemma contDiffOn_Ici_laplaceTransform_of_moments
    (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceTransform μ) (Ici 0) := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_integrable_moments μ hmom
  refine contDiffOn_of_differentiableOn_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (s := Ici (0 : ℝ)) (f := laplaceTransform μ) ?_
  intro m _hm
  have hdiff_moment : DifferentiableOn ℝ (laplaceMomentTransform μ m) (Ici 0) := by
    intro t ht
    exact (hasDerivWithinAt_laplaceMomentTransform_Ici μ hmom m ht).differentiableWithinAt
  exact hdiff_moment.congr fun t ht =>
    iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici μ hmom m ht


/-- On the open half-line, the ordinary iterated derivatives of a finite-measure Laplace transform
are the signed moment kernel integrals; this is Mathlib's `iteratedDeriv_mgf` through the
bridge. -/
private lemma iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform
    (μ : Measure ℝ≥0)
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (laplaceTransform μ) t = laplaceMomentTransform μ n t := by
  rw [laplaceTransform_eq_mgf,
    iteratedDeriv_mgf (Ioi_subset_interior_integrableExpSet μ hint (mem_Ioi.mpr ht)) n]
  simp only [laplaceMomentTransform, mul_neg]

/-- A finite-measure Laplace transform is smooth on the open half-line: it is the
moment-generating function of `p ↦ -p`, which is analytic on the interior of its
integrability set. -/
lemma contDiffOn_Ioi_laplaceTransform (μ : Measure ℝ≥0)
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceTransform μ) (Ioi 0) := by
  rw [laplaceTransform_eq_mgf]
  exact (analyticOnNhd_mgf.mono (Ioi_subset_interior_integrableExpSet μ hint)).contDiffOn
    isOpen_Ioi.uniqueDiffOn

/-- Every finite-measure Laplace transform is completely monotone on `(0, ∞)`. -/
theorem isCompletelyMonotoneOnIoi_laplaceTransform
    (μ : Measure ℝ≥0)
    (hint : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) :
    IsCompletelyMonotoneOnIoi (laplaceTransform μ) := by
  refine ⟨contDiffOn_Ioi_laplaceTransform μ hint, fun n t ht => ?_⟩
  rw [iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform μ hint n ht]
  exact neg_one_pow_mul_laplaceMomentTransform_nonneg μ n t

/-- The Laplace transform of a finite measure is completely monotone in the closed-half-line
roadmap sense. -/
theorem isCompletelyMonotoneOnIci_laplaceTransform
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ] :
    IsCompletelyMonotoneOnIci (laplaceTransform μ) :=
  isCompletelyMonotoneOnIci_iff.mpr
    ⟨continuousOn_Ici_laplaceTransform μ,
      isCompletelyMonotoneOnIoi_laplaceTransform μ fun _ ht => integrable_exp_neg_mul μ ht.le⟩

/-- Strong easy direction: with all moments finite, the Laplace transform satisfies the existing
`IsCompletelyMonotone` predicate using derivatives within `[0, ∞)`. -/
theorem isCompletelyMonotone_laplaceTransform_of_moments
    (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    IsCompletelyMonotone (laplaceTransform μ) := by
  have : IsFiniteMeasure μ := isFiniteMeasure_of_integrable_moments μ hmom
  refine ⟨contDiffOn_Ici_laplaceTransform_of_moments μ hmom, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici μ hmom n ht]
  exact neg_one_pow_mul_laplaceMomentTransform_nonneg μ n t

/-! ## Representation predicate -/

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
def RepresentsLaplace (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

/-- `RepresentsLaplace f μ` unfolds to finiteness of `μ` and equality with the Laplace transform
on the nonnegative half-line. -/
lemma representsLaplace_iff {f : ℝ → ℝ} {μ : Measure ℝ≥0} :
    RepresentsLaplace μ f ↔
      IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplace

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A representing measure is finite. -/
@[grind →]
lemma isFiniteMeasure (h : RepresentsLaplace μ f) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace-transform values on `[0, ∞)`. -/
@[grind =>]
lemma eq_laplaceTransform (h : RepresentsLaplace μ f) {t : ℝ} (ht : 0 ≤ t) :
    f t = laplaceTransform μ t :=
  h.2 t ht

/-- A representation transports along agreement on the nonnegative half-line: the predicate
constrains `f` only there. -/
protected lemma congr {g : ℝ → ℝ} (hf : RepresentsLaplace μ f) (h : EqOn g f (Ici 0)) :
    RepresentsLaplace μ g :=
  ⟨hf.isFiniteMeasure, fun _ ht => (h (mem_Ici.mpr ht)).trans (hf.eq_laplaceTransform ht)⟩

/-- The sum of two representing measures represents the sum of the functions. -/
protected lemma add {f g : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hf : RepresentsLaplace μ f) (hg : RepresentsLaplace ν g) :
    RepresentsLaplace (μ + ν) (f + g) := by
  have := hf.isFiniteMeasure
  have := hg.isFiniteMeasure
  refine ⟨inferInstance, fun t ht => ?_⟩
  rw [Pi.add_apply, hf.eq_laplaceTransform ht, hg.eq_laplaceTransform ht,
    laplaceTransform_add_measure μ ν ht]

/-- Scaling a representing measure by `c : ℝ≥0` represents the scaled function. -/
protected lemma smul {f : ℝ → ℝ} {μ : Measure ℝ≥0} (c : ℝ≥0)
    (hf : RepresentsLaplace μ f) :
    RepresentsLaplace ((c : ℝ≥0∞) • μ) (fun t => (c : ℝ) * f t) := by
  have := hf.isFiniteMeasure
  have : IsFiniteMeasure ((c : ℝ≥0∞) • μ) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top μ univ)
  refine ⟨inferInstance, fun t ht => ?_⟩
  rw [laplaceTransform_smul_measure, ← hf.eq_laplaceTransform ht]

end RepresentsLaplace

/-- The zero measure represents the zero function. -/
lemma representsLaplace_zero : RepresentsLaplace (0 : Measure ℝ≥0) 0 :=
  ⟨inferInstance, fun t _ => by simp⟩

/-- The Dirac mass at `x₀` represents the exponential kernel `t ↦ exp (-(t · x₀))`. -/
lemma representsLaplace_dirac (x₀ : ℝ≥0) :
    RepresentsLaplace (Measure.dirac x₀) (fun t : ℝ => Real.exp (-(t * (x₀ : ℝ)))) := by
  refine ⟨inferInstance, fun t _ht => ?_⟩
  rw [laplaceTransform_dirac]

/-! ## Uniqueness: finite measures are determined by their Laplace transforms -/

/-- Finite measures on `ℝ≥0` are determined by the values of their Laplace transforms at the
natural numbers alone; this is the transform-level form of
`Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq`. -/
theorem Measure.ext_of_forall_laplaceTransform_natCast_eq
    {μ ν : Measure ℝ≥0} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ n : ℕ, laplaceTransform μ n = laplaceTransform ν n) :
    μ = ν := by
  refine Measure.ext_of_forall_integral_exp_neg_natCast_mul_eq fun n => ?_
  simpa [laplaceTransform_apply, neg_mul] using h n

/-- A function has at most one finite representing measure. -/
protected lemma RepresentsLaplace.unique
    {f : ℝ → ℝ} {μ ν : Measure ℝ≥0}
    (hμ : RepresentsLaplace μ f) (hν : RepresentsLaplace ν f) :
    μ = ν := by
  have := hμ.isFiniteMeasure
  have := hν.isFiniteMeasure
  exact Measure.ext_of_forall_laplaceTransform_natCast_eq fun n => by
    rw [← hμ.eq_laplaceTransform (Nat.cast_nonneg n), ← hν.eq_laplaceTransform (Nat.cast_nonneg n)]

end TauCeti
