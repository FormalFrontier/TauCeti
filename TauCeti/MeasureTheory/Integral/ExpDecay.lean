/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.Basic

/-!
# Exponential integrals on the real line

This file records integrability and evaluation of exponential integrands on a half-line or the
whole real line: natural powers multiplied by an exponentially decaying factor, the exact rate at
which a bare exponential is integrable on a right half-line, integrability of the two-sided
exponential, and general comparison criteria for tail lower bounds. It also carries a
measure-agnostic exponential-integrability criterion, stated for a random variable on an arbitrary
measurable space rather than for the line.

Mathlib supplies the *sufficient* direction of the right-half-line integrability criterion,
`integrableOn_exp_mul_Ioi`, for a negative rate.  `integrableOn_exp_mul_Ioi_iff` adds the converse,
which is what lets a caller describe an exponential-moment domain as an exact set rather than an
inclusion.

## Main results

* `TauCeti.integrableOn_pow_mul_exp_neg_mul_Ioi`: integrability on `(0, ∞)`.
* `TauCeti.integral_pow_mul_exp_neg_mul_Ioi`: evaluation in terms of a factorial.
* `TauCeti.integrableOn_exp_mul_Ioi_iff`: `exp (a * ·)` is integrable on `(c, ∞)` exactly when
  `a < 0`.
* `TauCeti.integrableOn_exp_mul_Iic_iff`: `exp (a * ·)` is integrable on `(-∞, c]` exactly when
  `0 < a`.
* `TauCeti.integrable_exp_neg_mul_abs`: `exp (-(a * |·|))` is integrable when `0 < a`.
* `TauCeti.integrable_exp_mul_of_ae_le_of_nonpos`: `exp (t * X ·)` is integrable for `t ≤ 0`
  whenever the random variable `X` is almost everywhere bounded below under a finite measure on
  any measurable space.
* `TauCeti.not_integrableOn_Ioi_of_eventually_one_le_norm`: a function whose norm is eventually
  at least one is not integrable on any right half-line, hence, in
  `TauCeti.not_integrable_of_eventually_one_le_norm_atTop` and
  `TauCeti.not_integrable_of_eventually_one_le_atTop`, not Lebesgue integrable.
-/

public section

noncomputable section

open Filter MeasureTheory Set

namespace TauCeti

/-- Under a finite measure, the exponential of a nonpositive multiple of an almost everywhere
bounded below random variable is integrable.

This is Mathlib's `ProbabilityTheory.integrable_exp_mul_of_le` reflected through `X ↦ -X`. -/
theorem integrable_exp_mul_of_ae_le_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (hX : AEMeasurable X μ)
    {b : ℝ} (hb : ∀ᵐ ω ∂μ, b ≤ X ω) {t : ℝ} (ht : t ≤ 0) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  simpa only [Pi.neg_apply, neg_mul_neg] using
    ProbabilityTheory.integrable_exp_mul_of_le (-t) (-b) (neg_nonneg.mpr ht) hX.neg
      (by filter_upwards [hb] with ω hω using neg_le_neg hω)

/-- A function whose norm is eventually at least one at `atTop` is not integrable on any right
half-line: it is bounded below in norm on a set of infinite measure. -/
theorem not_integrableOn_Ioi_of_eventually_one_le_norm {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (c : ℝ) (hf : ∀ᶠ x in atTop, 1 ≤ ‖f x‖) : ¬ IntegrableOn f (Ioi c) := by
  intro hint
  obtain ⟨a, ha⟩ := eventually_atTop.mp hf
  have htail : IntegrableOn f (Ioi (max a c)) := hint.mono_set (Ioi_subset_Ioi (le_max_right a c))
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi (max a c)) volume := by
    refine Integrable.mono' htail.norm (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [norm_one] using ha x ((le_max_left a c).trans hx.le)
  rw [integrableOn_const_iff] at hone
  simp [Real.volume_Ioi] at hone

/-- A function whose norm is eventually at least one at `atTop` is not Lebesgue integrable. -/
theorem not_integrable_of_eventually_one_le_norm_atTop {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : ∀ᶠ x in atTop, 1 ≤ ‖f x‖) : ¬ Integrable f volume := fun hint =>
  not_integrableOn_Ioi_of_eventually_one_le_norm 0 hf hint.integrableOn

/-- A real function that is eventually at least one at `atTop` is not Lebesgue integrable. -/
theorem not_integrable_of_eventually_one_le_atTop {f : ℝ → ℝ}
    (hf : ∀ᶠ x in atTop, 1 ≤ f x) : ¬ Integrable f volume :=
  not_integrable_of_eventually_one_le_norm_atTop
    (hf.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx.trans (le_abs_self _))

/-- Natural powers times an exponentially decaying factor are integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_mul_Ioi (n : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(b * t))) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := b)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos hb
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

/-- The integral of a natural power times an exponentially decaying factor on `(0, ∞)`. -/
theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) = n.factorial / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Real.Gamma_nat_eq_factorial] at h
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast] at h
  have h' : ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-(a * t)) =
      (1 / a) ^ (n + 1) * n.factorial := by
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp
    rw [Real.rpow_natCast t n]
  rw [h', one_div, div_eq_mul_inv, inv_pow]
  ring

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  have hIic : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun (fun x hx ↦ ?_) measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    ring_nf
  have hIoi : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun
      (fun x hx ↦ ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hx)]
    ring_nf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- **The exact integrability rate.**  `fun x => exp (a * x)` is integrable on `(c, ∞)` precisely
when the rate is negative.  Mathlib's `integrableOn_exp_mul_Ioi` is the `←` direction. -/
@[simp]
theorem integrableOn_exp_mul_Ioi_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) ↔ a < 0 := by
  refine ⟨fun h => ?_, fun ha => integrableOn_exp_mul_Ioi ha c⟩
  by_contra hne
  refine not_integrableOn_Ioi_of_eventually_one_le_norm c ?_ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.one_le_exp_iff]
  exact mul_nonneg (not_lt.mp hne) hx

/-- **The exact integrability rate on a left half-line.** `fun x => exp (a * x)` is integrable
on `(-∞, c]` precisely when the rate is positive. -/
@[simp]
theorem integrableOn_exp_mul_Iic_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Iic c) ↔ 0 < a := by
  rw [integrableOn_Iic_iff_integrableOn_Iio,
    ← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_neg, mul_neg, neg_mul,
    neg_lt_zero] using (integrableOn_exp_mul_Ioi_iff (a := -a) (c := -c))

end TauCeti
