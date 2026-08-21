/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The winding number of a straight segment and its one-sided limits

The winding number of the straight segment `t ↦ v · t + z₀` about a point beside it is the
logarithmic increment `(2πi)⁻¹ (log (b - q) - log (a - q))`. Its one-sided limits at an interior
point differ by exactly `1`.

This is a prerequisite of the planar-separation step of the `ConformalMapping` roadmap (L5).

## Main results

* `TauCeti.Contour.windingNumber_segment_of_im_ne_zero` — **the winding number formula for a
  straight segment.**
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

/-- The straight segment `t ↦ v · t + z₀` has derivative `v` everywhere. -/
theorem hasDerivAt_segment (v z₀ : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => v * (t : ℂ) + z₀) v t := by
  simpa using ((hasDerivAt_id t).ofReal_comp.const_mul v).add_const z₀

/-- The straight segment `t ↦ v · t + z₀` avoids `v · q + z₀` when `q` is not real. -/
theorem segment_ne_of_im_ne_zero (hv : v ≠ 0) (hq : q.im ≠ 0) (t : ℝ) :
    v * (t : ℂ) + z₀ ≠ v * q + z₀ := by
  intro h
  have h' : v * ((t : ℂ) - q) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact hv h''
  · apply hq
    have := congrArg Complex.im h''
    simpa using this.symm

/-- **The winding number of a straight segment about a point beside it** is the increment of the
principal logarithm. -/
theorem windingNumber_segment_of_im_ne_zero (hv : v ≠ 0) (hq : q.im ≠ 0) (a b : ℝ) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) a b (v * q + z₀)
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (log ((b : ℂ) - q) - log ((a : ℂ) - q)) := by
  have hne : ∀ t : ℝ, (t : ℂ) - q ≠ 0 := by
    intro t h
    apply hq
    have := congrArg Complex.im h
    simpa using this.symm
  have hslit : ∀ t : ℝ, (t : ℂ) - q ∈ slitPlane := fun t =>
    mem_slitPlane_iff.mpr (Or.inr (by simpa using hq))
  have h_cont : ContinuousOn (fun t : ℝ => v * (t : ℂ) + z₀) (uIcc a b) :=
    (by fun_prop : Continuous fun t : ℝ => v * (t : ℂ) + z₀).continuousOn
  have h_avoid : ∀ t ∈ uIcc a b, v * (t : ℂ) + z₀ ≠ v * q + z₀ := fun t _ =>
    segment_ne_of_im_ne_zero hv hq t
  have h_integrand : ∀ t : ℝ,
      (v * (t : ℂ) + z₀ - (v * q + z₀))⁻¹ * deriv (fun t : ℝ => v * (t : ℂ) + z₀) t
        = ((t : ℂ) - q)⁻¹ := by
    intro t
    rw [(hasDerivAt_segment v z₀ t).deriv]
    have : v * (t : ℂ) + z₀ - (v * q + z₀) = v * ((t : ℂ) - q) := by ring
    rw [this]; field_simp
  have h_log : ∀ t : ℝ, HasDerivAt (fun t : ℝ => log ((t : ℂ) - q)) (((t : ℂ) - q)⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) - q) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp.sub_const q
    simpa using h1.clog_real (hslit t)
  have h_intble : IntervalIntegrable (fun t : ℝ => ((t : ℂ) - q)⁻¹) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    exact ContinuousOn.inv₀ (by fun_prop) fun t _ => hne t
  have h_int : IntervalIntegrable
      (fun t : ℝ => (v * (t : ℂ) + z₀ - (v * q + z₀))⁻¹ * deriv (fun t : ℝ => v * (t : ℂ) + z₀) t)
      volume a b := by
    exact h_intble.congr fun t _ => (h_integrand t).symm
  rw [windingNumber_eq_integral_of_avoidance h_cont h_avoid h_int]
  congr 1
  rw [intervalIntegral.integral_congr (fun t _ => h_integrand t)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h_log t) h_intble

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
    mem_slitPlane_iff.mpr (Or.inl (by simp only [sub_re, ofReal_re]; linarith))
  exact (continuousAt_clog hmem).tendsto.comp (tendsto_ofReal_sub_add_mul_I b s σ)

private theorem re_neg_of_mem_Ioo (hs : s ∈ Ioo a b) : ((a : ℂ) - s).re < 0 := by
  simp only [sub_re, ofReal_re]; linarith [hs.1]

private theorem norm_ofReal_sub_of_mem_Ioo (hs : s ∈ Ioo a b) : ‖(a : ℂ) - s‖ = s - a := by
  simp only [← ofReal_sub, norm_real, Real.norm_eq_abs]
  rw [abs_sub_comm, abs_of_pos (by linarith [hs.1])]

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
    rw [windingNumber_segment_of_im_ne_zero hv him a b]
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
    rw [windingNumber_segment_of_im_ne_zero hv him a b]
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
