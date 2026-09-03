/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exponential integrals on the real line

This file records integrability and evaluation of exponential integrands on a half-line or the
whole real line: natural powers multiplied by an exponentially decaying factor, the exact rate at
which a bare exponential is integrable on a right half-line, and integrability of the two-sided
exponential.

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
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

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


/-- At a nonnegative rate the integrand is bounded below by a positive constant on `(c, ∞)`, a set
of infinite measure, so it is not integrable there. -/
private theorem not_integrableOn_exp_mul_Ioi {a c : ℝ} (ha : 0 ≤ a) :
    ¬ IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) := by
  intro h
  have hsub : Set.Ioi c ⊆ {x : ℝ | Real.exp (a * c) ≤ Real.exp (a * x)} := by
    intro x hx
    exact Real.exp_le_exp.2 (by nlinarith [le_of_lt (Set.mem_Ioi.mp hx)])
  have h1 : (volume.restrict (Set.Ioi c)) (Set.Ioi c) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (h.measure_ge_lt_top (Real.exp_pos (a * c)))
  rw [Measure.restrict_apply_self, Real.volume_Ioi] at h1
  exact absurd h1 (by simp)

/-- **The exact integrability rate.**  `fun x => exp (a * x)` is integrable on `(c, ∞)` precisely
when the rate is negative.  Mathlib's `integrableOn_exp_mul_Ioi` is the `←` direction. -/
@[simp]
theorem integrableOn_exp_mul_Ioi_iff {a c : ℝ} :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Set.Ioi c) ↔ a < 0 := by
  refine ⟨fun h => ?_, fun ha => integrableOn_exp_mul_Ioi ha c⟩
  by_contra hne
  exact not_integrableOn_exp_mul_Ioi (not_lt.mp hne) h

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
