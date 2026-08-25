/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.Basic
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.Analysis.Contour.Winding.UnboundedComponent

/-!
# The winding numbers of the half-disc contour

`WorkedExamples/HalfDisc/Basic.lean` builds the boundary of the upper half-disc of radius `R`
about the origin and computes its generalized winding number at the one point of the contour that
the Hungerbühler–Wasem half-residue theorem needs: the origin, where the value is `½`. This file
computes the winding number at every point *off the contour*, which is what turns the contour
from the carrier of a single worked example into a general tool:

* `1` at every point of the **open upper half-disc**, the classical interior value, so a
  singularity there contributes its full residue;
* `0` below the real axis and outside the closed disc, so a singularity there contributes nothing.

The interior value is obtained with no homotopy or Jordan-curve input. Write `Λ` for the diameter
piece, `A` for the upper arc and `B` for the lower arc of the same circle. The full circle gives
`n(A) + n(B) = 1`, and `Λ` and `B` are evaluated by the *same* logarithmic FTC: about a point `s`
strictly above the real axis, neither `Λ t - s` nor `B θ - s` ever leaves the open lower
half-plane, hence never leaves `Complex.slitPlane`, so the principal branch of `Complex.log` is a
single-valued primitive along each and both integrals telescope to the same value
`log (R - s) - log (-R - s)`. Hence `n(Λ) + n(A) = n(B) + n(A) = 1`.

The vanishing statements go through `IsPiecewiseC1On.windingNumber_eq_zero_of_ray`: a point below
the axis escapes to infinity straight downwards, and a point outside the closed disc escapes
radially, in both cases without meeting the contour.

Together with `windingNumber_halfDiscBoundary`, this settles every point except those *on* the
contour other than the origin -- a real `t` with `|t| < R`, or a point of the upper semicircle.
There the winding number is a genuine principal value rather than an ordinary integral, and the
diameter's contribution is the principal value of a segment crossed away from its midpoint, which
the segment API does not yet evaluate.

## Main results

* `TauCeti.Contour.windingNumber_halfDiscBoundary_eq_one` — the winding number is `1` at every
  point of the open upper half-disc.
* `TauCeti.Contour.windingNumber_halfDiscBoundary_eq_zero_of_im_neg` and
  `TauCeti.Contour.windingNumber_halfDiscBoundary_eq_zero_of_lt_norm` — it is `0` below the real
  axis and outside the closed disc.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {R : ℝ}

/-! ### A logarithmic evaluation of an index integral -/

/-- **Slit-plane evaluation of an index integral.** If `γ` agrees on the open interval and at both
endpoints with a comparison curve `h` whose difference `h · - s` stays in `Complex.slitPlane`, the
index integral of `γ` about `s` telescopes through the principal branch of the logarithm.

The comparison shape is what makes this usable at a corner: the half-disc contour is not
differentiable at its junction, but it agrees with a smooth piece on each side of it. -/
private theorem integral_index_eq_log_sub_log {γ h : ℝ → ℂ} {a b : ℝ} {s : ℂ} (hab : a ≤ b)
    (hcont : ContinuousOn h (Icc a b)) (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hderiv : ContinuousOn (deriv h) (Icc a b))
    (hslit : ∀ t ∈ Icc a b, h t - s ∈ slitPlane)
    (heq : EqOn γ h (Ioo a b)) (ha : γ a = h a) (hb : γ b = h b) :
    (∫ t in a..b, (γ t - s)⁻¹ * deriv γ t)
      = Complex.log (γ b - s) - Complex.log (γ a - s) := by
  have hd : (deriv fun t => h t - s) = deriv h := funext fun t => deriv_sub_const s
  have hkey :=
    intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_mem_slitPlane_of_le
      (g := fun t => γ t - s) (h := fun t => h t - s) hab (hcont.sub continuousOn_const)
      (fun t ht => (hdiff t ht).sub_const s) (by rw [hd]; exact hderiv) hslit
      (fun t ht => by simp only [heq ht]) (by simp only [ha]) (by simp only [hb])
  simpa only [deriv_sub_const, div_eq_inv_mul] using hkey.2

/-! ### The interior value -/

/-- **The half-disc contour has winding number `1` about every point of the open upper half-disc.**

The diameter and the *lower* semicircle both telescope, through the principal logarithm, to
`log (R - s) - log (-R - s)`: about a point `s` above the real axis, neither `t - s` (for real `t`)
nor `B θ - s` (for `B` the lower semicircle) ever leaves the open lower half-plane, which is
contained in `Complex.slitPlane`. Since the whole circle has winding number `1`, the upper
semicircle contributes `1` minus the lower one, and the two occurrences of that common
logarithmic value cancel. -/
theorem windingNumber_halfDiscBoundary_eq_one {s : ℂ} (him : 0 < s.im) (hs : ‖s‖ < R) :
    windingNumber (halfDiscBoundary R) (-R) (R + Real.pi) s = 1 := by
  have hR : 0 < R := (norm_nonneg s).trans_lt hs
  have hpi := Real.pi_pos
  -- The index integral of the contour, as an ordinary integral.
  have havoid : ∀ t ∈ uIcc (-R) (R + Real.pi), halfDiscBoundary R t ≠ s :=
    fun t _ => halfDiscBoundary_ne_of_im_pos_of_norm_lt him hs t
  have hcont : ContinuousOn (halfDiscBoundary R) (uIcc (-R) (R + Real.pi)) :=
    (continuous_halfDiscBoundary R).continuousOn
  have hint : IntervalIntegrable
      (fun t => (halfDiscBoundary R t - s)⁻¹ * deriv (halfDiscBoundary R) t) volume
      (-R) (R + Real.pi) :=
    intervalIntegrable_inv_sub_mul_deriv hcont havoid
      (isPwC1ImmersionOn_halfDiscBoundary hR).isPiecewiseC1On.intervalIntegrable_deriv
  rw [windingNumber_eq_integral_of_avoidance hcont havoid hint]
  -- Split the contour integral at the junction.
  have hsub₁ : uIcc (-R) R ⊆ uIcc (-R) (R + Real.pi) := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hsub₂ : uIcc R (R + Real.pi) ⊆ uIcc (-R) (R + Real.pi) := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hsplit :
      (∫ t in (-R)..R, (halfDiscBoundary R t - s)⁻¹ * deriv (halfDiscBoundary R) t) +
          (∫ t in R..(R + Real.pi),
            (halfDiscBoundary R t - s)⁻¹ * deriv (halfDiscBoundary R) t)
        = ∫ t in (-R)..(R + Real.pi),
            (halfDiscBoundary R t - s)⁻¹ * deriv (halfDiscBoundary R) t :=
    intervalIntegral.integral_add_adjacent_intervals (hint.mono_set hsub₁) (hint.mono_set hsub₂)
  -- The circle map and its two half-arcs.
  have hderivC : (deriv (circleMap 0 R)) = fun θ => circleMap 0 R θ * Complex.I :=
    funext (deriv_circleMap 0 R)
  have hderivC_cont : Continuous (deriv (circleMap 0 R)) := by
    rw [hderivC]; exact (continuous_circleMap 0 R).mul continuous_const
  have havoidC : ∀ θ : ℝ, circleMap 0 R θ ≠ s := by
    intro θ h
    exact hs.ne (by rw [← h, norm_circleMap_zero, abs_of_nonneg hR.le])
  have hintC : IntervalIntegrable
      (fun θ => (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ) volume 0 (2 * Real.pi) :=
    intervalIntegrable_inv_sub_mul_deriv (continuous_circleMap 0 R).continuousOn
      (fun t _ => havoidC t) (hderivC_cont.intervalIntegrable _ _)
  have hcircle : (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ) = 2 * (Real.pi : ℂ) * Complex.I := by
    have hw := windingNumber_circleMap_eq_one_of_dist_lt (c := 0) (w := s) (R := R)
      (by simpa using hs)
    rw [windingNumber_eq_integral_of_avoidance (continuous_circleMap 0 R).continuousOn
      (fun t _ => havoidC t) hintC] at hw
    calc (∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ)
        = 2 * (Real.pi : ℂ) * Complex.I * ((2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi), (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ) := by
          rw [← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
      _ = 2 * (Real.pi : ℂ) * Complex.I := by rw [hw, mul_one]
  have hsubC₁ : uIcc (0 : ℝ) Real.pi ⊆ uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [uIcc_of_le hpi.le, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have hsubC₂ : uIcc Real.pi (2 * Real.pi) ⊆ uIcc (0 : ℝ) (2 * Real.pi) := by
    rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hpi.le le_rfl
  have hsplitC :
      (∫ θ in (0 : ℝ)..Real.pi, (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ) +
          (∫ θ in Real.pi..(2 * Real.pi),
            (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ)
        = ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ :=
    intervalIntegral.integral_add_adjacent_intervals (hintC.mono_set hsubC₁)
      (hintC.mono_set hsubC₂)
  -- The two logarithmic evaluations, which produce the same value.
  have hslit : ∀ z : ℂ, z.im ≤ 0 → z - s ∈ slitPlane := by
    intro z hz
    refine Or.inr ?_
    simp only [Complex.sub_im, ne_eq, sub_eq_zero]
    exact fun h => absurd (h ▸ hz) (not_le.mpr him)
  have hRC : circleMap 0 R (2 * Real.pi) = (R : ℂ) := by
    simp [circleMap, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
  have hnRC : circleMap 0 R Real.pi = -(R : ℂ) := by
    simp [circleMap, Complex.exp_pi_mul_I]
  have hlower : (∫ θ in Real.pi..(2 * Real.pi),
      (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ)
      = Complex.log ((R : ℂ) - s) - Complex.log (-(R : ℂ) - s) := by
    rw [integral_index_eq_log_sub_log (h := circleMap 0 R) (by linarith)
      (continuous_circleMap 0 R).continuousOn
      (fun t _ => (differentiable_circleMap 0 R) t) hderivC_cont.continuousOn
      (fun θ hθ => hslit _ ?_) (fun _ _ => rfl) rfl rfl, hRC, hnRC]
    rw [circleMap_zero_im]
    have hsin : Real.sin θ ≤ 0 := by
      rw [← Real.sin_sub_two_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hθ.2]) (by linarith [hθ.1])
    exact mul_nonpos_of_nonneg_of_nonpos hR.le hsin
  have hdiam : (∫ t in (-R)..R, (halfDiscBoundary R t - s)⁻¹ * deriv (halfDiscBoundary R) t)
      = Complex.log ((R : ℂ) - s) - Complex.log (-(R : ℂ) - s) := by
    have hofReal : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := fun t => by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hderivR : (deriv fun u : ℝ => (u : ℂ)) = fun _ : ℝ => (1 : ℂ) :=
      funext fun t => (hofReal t).deriv
    have hnR_le_R : -R ≤ R := by linarith
    rw [integral_index_eq_log_sub_log (h := fun u : ℝ => (u : ℂ)) (by linarith)
      (by fun_prop) (fun t _ => (hofReal t).differentiableAt)
      (by rw [hderivR]; exact continuousOn_const)
      (fun t _ => hslit _ (by simp)) (fun t ht => halfDiscBoundary_of_le ht.2.le)
      (halfDiscBoundary_of_le (by linarith)) (halfDiscBoundary_of_le le_rfl),
      halfDiscBoundary_of_le le_rfl, halfDiscBoundary_of_le hnR_le_R]
    push_cast
    ring_nf
  -- Assemble: the diameter and the lower arc cancel, leaving the full circle.
  rw [← hsplit, hdiam, integral_halfDiscBoundary_arc (fun z => (z - s)⁻¹) R]
  have harc : (∫ θ in (0 : ℝ)..Real.pi, (circleMap 0 R θ - s)⁻¹ * deriv (circleMap 0 R) θ)
      = 2 * (Real.pi : ℂ) * Complex.I -
        (Complex.log ((R : ℂ) - s) - Complex.log (-(R : ℂ) - s)) := by
    rw [← hlower, ← hcircle, ← hsplitC]; ring
  have hcancel : Complex.log ((R : ℂ) - s) - Complex.log (-(R : ℂ) - s) +
      (2 * (Real.pi : ℂ) * Complex.I -
        (Complex.log ((R : ℂ) - s) - Complex.log (-(R : ℂ) - s)))
      = 2 * (Real.pi : ℂ) * Complex.I := by ring
  rw [harc, hcancel]
  exact inv_mul_cancel₀ Complex.two_pi_I_ne_zero

/-! ### The exterior values -/

/-- The half-disc contour is closed: both endpoints are `-R`. -/
private theorem halfDiscBoundary_closed (hR : 0 ≤ R) :
    halfDiscBoundary R (-R) = halfDiscBoundary R (R + Real.pi) :=
  (halfDiscBoundary_left hR).trans (halfDiscBoundary_right R).symm

/-- **The half-disc contour has winding number `0` below the real axis.** The contour lies in the
closed upper half-plane, so a point beneath the axis escapes to infinity straight downwards
without meeting it. -/
theorem windingNumber_halfDiscBoundary_eq_zero_of_im_neg (hR : 0 < R) {s : ℂ} (him : s.im < 0) :
    windingNumber (halfDiscBoundary R) (-R) (R + Real.pi) s = 0 := by
  have hpi := Real.pi_pos
  refine (isPwC1ImmersionOn_halfDiscBoundary hR).isPiecewiseC1On.windingNumber_eq_zero_of_ray
    (halfDiscBoundary_closed hR.le) (v := -Complex.I) (by simp) ?_
  rintro c hc ⟨t, ht, hteq⟩
  rw [uIcc_of_le (by linarith)] at ht
  have him' : 0 ≤ (halfDiscBoundary R t).im := im_halfDiscBoundary_nonneg hR.le ht.2
  rw [hteq] at him'
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_im, Complex.neg_re, Complex.I_im, Complex.I_re] at him'
  nlinarith [him']

/-- **The half-disc contour has winding number `0` outside the closed disc.** The contour lies in
the closed disc of radius `R`, so a point beyond it escapes to infinity radially without meeting
the contour. -/
theorem windingNumber_halfDiscBoundary_eq_zero_of_lt_norm (hR : 0 < R) {s : ℂ} (hs : R < ‖s‖) :
    windingNumber (halfDiscBoundary R) (-R) (R + Real.pi) s = 0 := by
  have hpi := Real.pi_pos
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  refine (isPwC1ImmersionOn_halfDiscBoundary hR).isPiecewiseC1On.windingNumber_eq_zero_of_ray
    (halfDiscBoundary_closed hR.le) (v := s) hs0 ?_
  rintro c hc ⟨t, ht, hteq⟩
  rw [uIcc_of_le (by linarith)] at ht
  have hle : ‖halfDiscBoundary R t‖ ≤ R := norm_halfDiscBoundary_le hR.le ht.1
  rw [hteq] at hle
  have hfactor : s + (c : ℂ) * s = ((1 + c : ℝ) : ℂ) * s := by
    push_cast
    ring
  have hnorm : ‖s + (c : ℂ) * s‖ = (1 + c) * ‖s‖ := by
    rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hnorm] at hle
  nlinarith [norm_nonneg s]

end TauCeti.Contour

end

end
