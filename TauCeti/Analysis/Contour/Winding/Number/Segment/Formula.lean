/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Affine
import TauCeti.Analysis.Contour.LogDerivFTC
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The winding number of a straight segment

The winding number of the straight segment `t ↦ v · t + z₀` about a point not on it is the
logarithmic increment `(2πi)⁻¹ (log (b - q) - log (a - q))`, valid whenever
`(t : ℂ) ≠ q` for `t ∈ [a, b]`.

This extends the segment winding API (`Segment/Basic.lean`) with the explicit formula for a
single straight piece. The formula is a building block for the winding decomposition of
HW Proposition 2.2 (ContourIntegration roadmap, Layer 1).

## Main results

* `TauCeti.Contour.windingNumber_segment` — **the winding number formula for a straight
  segment, under a slit-plane hypothesis.**
* `TauCeti.Contour.windingNumber_segment_of_im_ne_zero` — **specialization when the
  reference point has nonzero imaginary part.**
* `TauCeti.Contour.windingNumber_segment_of_ne` — **the formula under the natural
  avoidance hypothesis `(t : ℂ) ≠ q`**, covering real reference points on both sides.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.1.
-/

public section

open Complex Filter MeasureTheory Metric Set

open scoped Topology

namespace TauCeti.Contour

variable {v z₀ q : ℂ} {a b s : ℝ}

private theorem windingNumber_eq_integral_inv_sub (hv : v ≠ 0)
    (hne : ∀ t ∈ uIcc a b, (t : ℂ) - q ≠ 0) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ t in a..b, ((t : ℂ) - q)⁻¹ := by
  rw [windingNumber_affine (γ := fun t : ℝ => (t : ℂ)) (c := v) (d := z₀) (z₀ := q) hv]
  have h_cont : ContinuousOn (fun t : ℝ => (t : ℂ)) (uIcc a b) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ)).continuousOn
  have h_avoid : ∀ t ∈ uIcc a b, (t : ℂ) ≠ q := fun t ht => by
    intro h; exact hne t ht (by rw [h, sub_self])
  have h_integrand : ∀ t : ℝ,
      ((t : ℂ) - q)⁻¹ * deriv (fun t : ℝ => (t : ℂ)) t = ((t : ℂ) - q)⁻¹ := by
    intro t
    have : deriv (fun t : ℝ => (t : ℂ)) t = 1 := ofRealCLM.hasDerivAt.deriv
    rw [this, mul_one]
  have h_intble : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - q)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.inv₀ (by fun_prop) fun t ht => hne t ht
  have h_int : IntervalIntegrable
      (fun t : ℝ => ((t : ℂ) - q)⁻¹ * deriv (fun t : ℝ => (t : ℂ)) t)
      volume a b :=
    h_intble.congr fun t _ => (h_integrand t).symm
  rw [windingNumber_eq_integral_of_avoidance h_cont h_avoid h_int]
  congr 1
  exact intervalIntegral.integral_congr (fun t _ => h_integrand t)

/-- **The winding number of a straight segment about a point beside it** is the increment of the
principal logarithm, valid whenever `(t : ℂ) - q` lies in the slit plane throughout `[a, b]`.
This covers both the nonreal case (`q.im ≠ 0`) and real points below the segment
(`q.re < min a b`). -/
theorem windingNumber_segment (hv : v ≠ 0)
    (hslit : ∀ t ∈ uIcc a b, (t : ℂ) - q ∈ slitPlane) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - q) - log ((a : ℂ) - q)) := by
  have hne : ∀ t ∈ uIcc a b, (t : ℂ) - q ≠ 0 := fun t ht => slitPlane_ne_zero (hslit t ht)
  rw [windingNumber_eq_integral_inv_sub hv hne]
  congr 1
  have h_intble : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - q)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.inv₀ (by fun_prop) fun t ht => hne t ht
  have h_div : (fun t : ℝ => ((t : ℂ) - q)⁻¹) = fun t : ℝ => 1 / ((t : ℂ) - q) := by
    ext t; rw [one_div]
  rw [h_div]
  exact integral_deriv_div_eq_log_sub_log countable_empty
    (by fun_prop) (fun t _ => (ofRealCLM.hasDerivAt.sub_const q))
    (fun t ht => hslit t ht) (h_intble.congr fun t _ => by rw [one_div])

/-- **The winding number of a straight segment about a nonreal point.** Specialization of
`windingNumber_segment` when `q.im ≠ 0`, which guarantees the slit-plane condition. -/
theorem windingNumber_segment_of_im_ne_zero (hv : v ≠ 0) (hq : q.im ≠ 0) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - q) - log ((a : ℂ) - q)) :=
  windingNumber_segment hv (fun t _ => mem_slitPlane_iff.mpr (Or.inr (by simpa using hq)))

/-- For negative reals, the `Complex.log` difference reduces to the `Real.log` difference:
the shared `πi` branch offset cancels. -/
private theorem log_sub_log_ofReal_of_neg {c d : ℝ} (hc : c < 0) (hd : d < 0) :
    log (c : ℂ) - log (d : ℂ) = ((Real.log c - Real.log d : ℝ) : ℂ) := by
  have hmc : (0 : ℝ) < -c := neg_pos.mpr hc
  have hmd : (0 : ℝ) < -d := neg_pos.mpr hd
  have hc_eq : (c : ℂ) = (-c : ℝ) * (-1 : ℂ) := by push_cast; ring
  have hd_eq : (d : ℂ) = (-d : ℝ) * (-1 : ℂ) := by push_cast; ring
  rw [hc_eq, hd_eq,
      log_ofReal_mul hmc (by norm_num : (-1 : ℂ) ≠ 0),
      log_ofReal_mul hmd (by norm_num : (-1 : ℂ) ≠ 0)]
  simp only [Real.log_neg_eq_log, ofReal_sub]
  ring

/-- **The winding number formula for a real reference point beyond the far endpoint.** Both
`Complex.log` terms share the branch offset `πi`, which cancels in the difference, and the
integral is a real logarithmic integral. -/
private theorem windingNumber_segment_of_max_lt (hv : v ≠ 0) {r : ℝ} (hgt : max a b < r) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (r : ℂ) + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - r) - log ((a : ℂ) - r)) := by
  have hne_real : ∀ t ∈ uIcc a b, (t : ℝ) ≠ r := fun t ht h => by
    rcases Set.mem_uIcc.mp ht with ⟨-, h2⟩ | ⟨-, h2⟩ <;>
      linarith [le_max_left a b, le_max_right a b]
  have hne_sub : ∀ t ∈ uIcc a b, (t : ℂ) - (r : ℂ) ≠ 0 := by
    intro t ht
    simp only [ne_eq, sub_eq_zero]
    exact_mod_cast hne_real t ht
  rw [windingNumber_eq_integral_inv_sub hv hne_sub]
  congr 1
  have h_neg_b : (b : ℝ) - r < 0 := by linarith only [hgt, le_max_right a b]
  have h_neg_a : (a : ℝ) - r < 0 := by linarith only [hgt, le_max_left a b]
  have hb_cast : (b : ℂ) - (r : ℂ) = ((b - r : ℝ) : ℂ) := by push_cast; ring
  have ha_cast : (a : ℂ) - (r : ℂ) = ((a - r : ℝ) : ℂ) := by push_cast; ring
  rw [hb_cast, ha_cast, log_sub_log_ofReal_of_neg h_neg_b h_neg_a]
  have h_real_eq : ∀ t ∈ Set.uIcc a b,
      ((t : ℂ) - (r : ℂ))⁻¹ = ((((t - r)⁻¹ : ℝ) : ℂ)) := by
    intro t _
    push_cast
    ring
  rw [intervalIntegral.integral_congr h_real_eq, intervalIntegral.integral_ofReal]
  congr 1
  have hne_real' : ∀ t ∈ uIcc a b, t - r ≠ 0 := fun t ht =>
    sub_ne_zero.mpr (hne_real t ht)
  have h_deriv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => Real.log (s - r)) (t - r)⁻¹ t := by
    intro t ht
    have h1 : HasDerivAt (fun s => s - r) 1 t := (hasDerivAt_id t).sub_const r
    have h2 : HasDerivAt Real.log (t - r)⁻¹ (t - r) :=
      Real.hasDerivAt_log (hne_real' t ht)
    have h3 := h2.comp t h1
    simp only [mul_one] at h3
    exact h3
  have h_intble_real : IntervalIntegrable (fun t => (t - r)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) hne_real'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_intble_real

/-- **The winding number formula under the natural avoidance hypothesis.** The formula
`(2πi)⁻¹ (log (b - q) - log (a - q))` holds whenever the affine-parametrised reference point
avoids the segment, with no restriction to the slit plane. For nonreal `q` the slit-plane
condition is automatic; for real `q` beyond the far endpoint, both `Complex.log` terms share
the branch offset `πi`, which cancels in the difference. -/
theorem windingNumber_segment_of_ne (hv : v ≠ 0)
    (hne : ∀ t ∈ uIcc a b, (t : ℂ) ≠ q) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - q) - log ((a : ℂ) - q)) := by
  by_cases hq : q.im ≠ 0
  · exact windingNumber_segment_of_im_ne_zero hv hq
  simp only [not_not] at hq
  have hqr : q = (q.re : ℂ) := Complex.ext (by simp) (by simp [hq])
  rw [hqr] at hne ⊢
  have hne_real : ∀ t ∈ uIcc a b, (t : ℝ) ≠ q.re := by
    intro t ht h
    exact hne t ht (by exact_mod_cast congrArg ofReal h)
  by_cases hab : q.re < min a b
  · exact windingNumber_segment hv (fun t ht => by
      apply mem_slitPlane_iff.mpr; left
      simp only [sub_re, ofReal_re]
      have ht_lb : min a b ≤ t := ht.1
      linarith only [ht_lb, hab])
  · simp only [not_lt] at hab
    have hgt : max a b < q.re := by
      rcases le_or_gt q.re (max a b) with h | h
      · exact absurd (hne_real q.re ⟨hab, h⟩) (not_not.mpr rfl)
      · exact h
    exact windingNumber_segment_of_max_lt hv hgt

end TauCeti.Contour
