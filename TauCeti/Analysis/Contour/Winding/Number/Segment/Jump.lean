/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Affine
import TauCeti.Analysis.Contour.LogDerivFTC
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The winding number of a straight segment and its one-sided limits

The winding number of the straight segment `t ↦ v · t + z₀` about a point beside it is the
logarithmic increment `(2πi)⁻¹ (log (b - q) - log (a - q))`, valid whenever the differences
`(t : ℂ) - q` stay in the slit plane over `[a, b]`. Its one-sided limits at an interior
point differ by exactly `1`.

This extends the segment winding API (`Segment/Basic.lean`) with the explicit formula for a
single straight piece and the one-sided limit behaviour. The jump formula is the analytic input
to the winding decomposition of HW Proposition 2.2 (ContourIntegration roadmap, Layer 1).

## Main results

* `TauCeti.Contour.windingNumber_segment` — **the winding number formula for a straight
  segment, under a slit-plane hypothesis.**
* `TauCeti.Contour.windingNumber_segment_of_im_ne_zero` — **specialization when the
  reference point has nonzero imaginary part.**
* `TauCeti.Contour.tendsto_windingNumber_segment_add_mul_I` and
  `TauCeti.Contour.tendsto_windingNumber_segment_sub_mul_I` — **one-sided limits at an interior
  point, from the left and from the right.**
* `TauCeti.Contour.tendsto_windingNumber_segment_sub_windingNumber_segment` — **the jump of the
  segment's winding number across the segment is `1`.**

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.1.
-/

public section

open Complex Filter MeasureTheory Metric Set

open scoped Topology

namespace TauCeti.Contour

variable {v z₀ q : ℂ} {a b s : ℝ}

/-- **The winding number of a straight segment about a point beside it** is the increment of the
principal logarithm, valid whenever `(t : ℂ) - q` lies in the slit plane throughout `[a, b]`.
This covers both the nonreal case (`q.im ≠ 0`) and real points before the segment
(`q.re < a`). -/
theorem windingNumber_segment (hv : v ≠ 0)
    (hslit : ∀ t ∈ uIcc a b, (t : ℂ) - q ∈ slitPlane) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - q) - log ((a : ℂ) - q)) := by
  rw [windingNumber_affine (γ := fun t : ℝ => (t : ℂ)) (c := v) (d := z₀) (z₀ := q) hv]
  have hne : ∀ t ∈ uIcc a b, (t : ℂ) - q ≠ 0 := fun t ht => slitPlane_ne_zero (hslit t ht)
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
  rw [intervalIntegral.integral_congr (fun t _ => h_integrand t)]
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

/-- The difference `(r : ℂ) - (s + σ h I)` tends to `(r : ℂ) - s` as `h → 0⁺`. -/
private theorem tendsto_ofReal_sub_add_mul_I (r s : ℝ) (σ : ℝ) :
    Tendsto (fun h : ℝ => (r : ℂ) - (s + (σ * h : ℝ) * I)) (𝓝[>] 0) (𝓝 ((r : ℂ) - s)) := by
  have : Tendsto (fun h : ℝ => (r : ℂ) - (s + (σ * h : ℝ) * I)) (𝓝 0)
      (𝓝 ((r : ℂ) - (s + (σ * (0 : ℝ) : ℝ) * I))) := by
    apply Continuous.tendsto
    fun_prop
  simpa using this.mono_left nhdsWithin_le_nhds

/-- The far endpoint term: `log (b - (s ± h i)) → log (b - s)`, the limit point being a positive
real and so in the slit plane. -/
private theorem tendsto_log_far (hs : s < b) (σ : ℝ) :
    Tendsto (fun h : ℝ => log ((b : ℂ) - (s + (σ * h : ℝ) * I))) (𝓝[>] 0)
      (𝓝 (log ((b : ℂ) - s))) := by
  have hmem : (b : ℂ) - s ∈ slitPlane :=
    mem_slitPlane_iff.mpr (Or.inl (by simp only [sub_re, ofReal_re]; linarith only [hs]))
  exact (continuousAt_clog hmem).tendsto.comp (tendsto_ofReal_sub_add_mul_I b s σ)

private theorem re_neg_of_mem_Ioo (hs : s ∈ Ioo a b) : ((a : ℂ) - s).re < 0 := by
  simp only [sub_re, ofReal_re]; linarith only [hs.1]

private theorem norm_ofReal_sub_of_mem_Ioo (hs : s ∈ Ioo a b) : ‖(a : ℂ) - s‖ = s - a := by
  simp only [← ofReal_sub, norm_real, Real.norm_eq_abs]
  rw [abs_sub_comm, abs_of_pos (by linarith only [hs.1])]

/-- **The winding number of a segment about a point approaching from the left.** The near endpoint
term approaches the negative real axis from below. -/
theorem tendsto_windingNumber_segment_add_mul_I (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀))
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (log ((b : ℂ) - s) - (Real.log (s - a) - Real.pi * I)))) := by
  have h_eq : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          (log ((b : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)) -
            log ((a : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)))
        = windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have him : ((s : ℂ) + h * I).im ≠ 0 := by simpa using hh.ne'
    rw [windingNumber_segment_of_im_ne_zero hv him]
    simp
  refine Tendsto.congr' h_eq (Tendsto.const_mul _ (Tendsto.sub (tendsto_log_far hs.2 1) ?_))
  have h1 : Tendsto (fun h : ℝ => (a : ℂ) - (s + ((1 : ℝ) * h : ℝ) * I)) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] ((a : ℂ) - s)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_ofReal_sub_add_mul_I a s 1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh
  have h2 := (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (re_neg_of_mem_Ioo hs) (by simp)).comp h1
  simpa [Function.comp_def, norm_ofReal_sub_of_mem_Ioo hs] using h2

/-- **The winding number of a segment about a point approaching from the right.** The near endpoint
term approaches the negative real axis from above. -/
theorem tendsto_windingNumber_segment_sub_mul_I (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀))
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.pi : ℂ) * I)⁻¹ *
        (log ((b : ℂ) - s) - (Real.log (s - a) + Real.pi * I)))) := by
  have h_eq : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
          (log ((b : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)) -
            log ((a : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)))
        = windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have him : ((s : ℂ) - h * I).im ≠ 0 := by simpa using hh.ne'
    rw [windingNumber_segment_of_im_ne_zero hv him]
    simp [sub_eq_add_neg]
  refine Tendsto.congr' h_eq (Tendsto.const_mul _ (Tendsto.sub (tendsto_log_far hs.2 (-1)) ?_))
  have h1 : Tendsto (fun h : ℝ => (a : ℂ) - (s + ((-1 : ℝ) * h : ℝ) * I)) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((a : ℂ) - s)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_ofReal_sub_add_mul_I a s (-1), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa using hh.le
  have h2 := (tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (re_neg_of_mem_Ioo hs) (by simp)).comp h1
  simpa [Function.comp_def, norm_ofReal_sub_of_mem_Ioo hs] using h2

/-- **The jump of the winding number across a straight segment is `1`.** The left-side minus
right-side difference tends to `1` as the probing points approach the segment. -/
theorem tendsto_windingNumber_segment_sub_windingNumber_segment (hv : v ≠ 0) (hs : s ∈ Ioo a b) :
    Tendsto (fun h : ℝ =>
        windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s + h * I) + z₀) -
          windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * (s - h * I) + z₀))
      (𝓝[>] 0) (𝓝 1) := by
  have h := (tendsto_windingNumber_segment_add_mul_I (z₀ := z₀) hv hs).sub
    (tendsto_windingNumber_segment_sub_mul_I (z₀ := z₀) hv hs)
  convert h using 2
  have hπ : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  field_simp
  ring

end TauCeti.Contour
