/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The two-ray corner and its vanishing index principal value

The Hungerbühler–Wasem model sector (HW (2.4)) is the closed curve made of a radial segment into
its centre, a circular arc of opening angle `α`, and a radial segment back out. The arc's
contribution is `α / 2π` (`indexIntegral_arc`); this file supplies the other half, that the
two radial segments contribute nothing.

The two segments cannot be treated separately: for nonzero ray directions and `R > 0` each
excised integral diverges logarithmically as `ε → 0`. Taken together they cancel *exactly*, at
every `ε`, so the pair is packaged here as a single curve through the centre.

## Main definitions

* `TauCeti.Contour.twoRayCorner` — the corner `z₀` approached along direction `u` and left along
  direction `v`, with the corner at `t = 0`.

## Main results

* `TauCeti.Contour.deriv_twoRayCorner_of_ne` and `TauCeti.Contour.norm_twoRayCorner_sub` — the
  derivative and the distance from the corner, off the corner itself.
* `TauCeti.Contour.hasCauchyPVAt_inv_sub_twoRayCorner` — the index principal value along a two-ray
  corner with `‖u‖ = ‖v‖`, over `[-R, R]`, is `0`; `cauchyPVExistsAt_inv_sub_twoRayCorner` is its
  existence form.
* `TauCeti.Contour.windingNumber_eq_zero_twoRayCorner` — its generalized winding number vanishes.

This is Layer 1 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — (2.4).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The two-ray corner at `z₀`.** For `t < 0` the curve sits at distance `|t| ‖u‖` from `z₀`
along `u`, and for `t ≥ 0` at distance `t ‖v‖` along `v`; it meets `z₀` at `t = 0`. If both
directions are nonzero that is the only such parameter; if one of them vanishes the corresponding
ray is constant at `z₀`.

On `[-R, R]` with `‖u‖ = ‖v‖` the two endpoints lie on the circle of radius `|R| ‖v‖` about `z₀`,
so concatenating with the arc between them gives the Hungerbühler–Wasem model sector, parametrised
from the far end of one radius rather than from the corner. For unequal norms it is simply a
two-ray curve. -/
def twoRayCorner (z₀ u v : ℂ) : ℝ → ℂ :=
  fun t => if t < 0 then z₀ - (t : ℂ) * u else z₀ + (t : ℂ) * v

/-- Evaluation of the corner curve on the incoming ray. -/
@[simp]
theorem twoRayCorner_of_neg {z₀ u v : ℂ} {t : ℝ} (ht : t < 0) :
    twoRayCorner z₀ u v t = z₀ - (t : ℂ) * u := if_pos ht

/-- Evaluation of the corner curve on the outgoing ray, including the corner itself. -/
@[simp]
theorem twoRayCorner_of_nonneg {z₀ u v : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    twoRayCorner z₀ u v t = z₀ + (t : ℂ) * v := if_neg (not_lt.mpr ht)

/-- On the negative ray the corner curve is the affine map `t ↦ z₀ - t u`. -/
private theorem twoRayCorner_eventuallyEq_neg {z₀ u v : ℂ} {t : ℝ} (ht : t < 0) :
    twoRayCorner z₀ u v =ᶠ[𝓝 t] fun s : ℝ => z₀ - (s : ℂ) * u := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  simp [twoRayCorner, if_pos (mem_Iio.mp hs)]

/-- On the positive ray the corner curve is the affine map `t ↦ z₀ + t v`. -/
private theorem twoRayCorner_eventuallyEq_pos {z₀ u v : ℂ} {t : ℝ} (ht : 0 < t) :
    twoRayCorner z₀ u v =ᶠ[𝓝 t] fun s : ℝ => z₀ + (s : ℂ) * v := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp [twoRayCorner, if_neg (not_lt.mpr (mem_Ioi.mp hs).le)]

/-- The derivative of the corner curve off the corner: `-u` on the negative ray, `v` on the
positive ray. -/
theorem deriv_twoRayCorner_of_ne {z₀ u v : ℂ} {t : ℝ} (ht : t ≠ 0) :
    deriv (twoRayCorner z₀ u v) t = if t < 0 then -u else v := by
  have hofReal : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp (z := t)
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Filter.EventuallyEq.deriv_eq (twoRayCorner_eventuallyEq_neg (v := v) h), if_pos h]
    have hd : HasDerivAt (fun s : ℝ => z₀ - (s : ℂ) * u) (-u) t := by
      have h1 := _root_.HasDerivAt.mul_const hofReal u
      simpa using _root_.HasDerivAt.const_sub z₀ h1
    exact hd.deriv
  · rw [Filter.EventuallyEq.deriv_eq (twoRayCorner_eventuallyEq_pos (u := u) h),
      if_neg (not_lt.mpr h.le)]
    have hd : HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * v) v t := by
      have h1 := _root_.HasDerivAt.mul_const hofReal v
      simpa using _root_.HasDerivAt.const_add z₀ h1
    exact hd.deriv

/-- **The index integrand along a two-ray corner is `1 / t`,** on both rays: the direction cancels
against itself, leaving the same real function on either side of the corner. -/
private theorem integrand_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) {t : ℝ}
    (ht : t ≠ 0) :
    (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t = ((t : ℂ))⁻¹ := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [deriv_twoRayCorner_of_ne (z₀ := z₀) (u := u) (v := v) ht]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [if_pos h]
    simp only [twoRayCorner, if_pos h, sub_sub_cancel_left]
    field_simp
  · rw [if_neg (not_lt.mpr h.le)]
    simp only [twoRayCorner, if_neg (not_lt.mpr h.le), add_sub_cancel_left]
    field_simp

/-- The distance from the corner is `|t|` times the common ray length. -/
theorem norm_twoRayCorner_sub {z₀ u v : ℂ} (huv : ‖u‖ = ‖v‖) (t : ℝ) :
    ‖twoRayCorner z₀ u v t - z₀‖ = |t| * ‖v‖ := by
  rcases lt_or_ge t 0 with h | h
  · simp only [twoRayCorner, if_pos h, sub_sub_cancel_left]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, huv]
  · simp only [twoRayCorner, if_neg (not_lt.mpr h), add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The `ε`-truncated index integrand of a two-ray corner is odd. -/
private theorem truncated_inv_twoRayCorner_odd {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (ε : ℝ) :
    Function.Odd (fun t : ℝ =>
      if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
        (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t else 0) := by
  intro t
  simp only [norm_twoRayCorner_sub huv, abs_neg]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [twoRayCorner]
  · rw [integrand_twoRayCorner hu hv ht, integrand_twoRayCorner hu hv (neg_ne_zero.mpr ht)]
    split_ifs <;> simp

/-- Every `ε`-truncated index integral along a two-ray corner over `[-R, R]` vanishes. -/
private theorem integral_truncated_inv_twoRayCorner {z₀ u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : ‖u‖ = ‖v‖) (R ε : ℝ) :
    ∫ t in (-R)..R, (if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
      (twoRayCorner z₀ u v t - z₀)⁻¹ * deriv (twoRayCorner z₀ u v) t else 0) = 0 :=
  intervalIntegral.integral_eq_zero_of_odd (truncated_inv_twoRayCorner_odd hu hv huv ε) R


/-- The corner curve is measurable: it is affine on each ray. -/
private theorem measurable_twoRayCorner (z₀ u v : ℂ) : Measurable (twoRayCorner z₀ u v) := by
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_ <;> fun_prop

/-- Off the corner the derivative is the step function `-u` / `v`. -/
private theorem deriv_twoRayCorner_ae (z₀ u v : ℂ) (R : ℝ) :
    deriv (twoRayCorner z₀ u v) =ᵐ[volume.restrict (uIoc (-R) R)]
      fun t : ℝ => if t < 0 then -u else v := by
  refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
    (MeasureTheory.measure_singleton (0 : ℝ))] with t ht _
  exact deriv_twoRayCorner_of_ne ht

/-- The derivative of the corner curve is interval integrable: a bounded step function. -/
private theorem intervalIntegrable_deriv_twoRayCorner (z₀ u v : ℂ) (R : ℝ) :
    IntervalIntegrable (deriv (twoRayCorner z₀ u v)) volume (-R) R := by
  refine (intervalIntegrable_congr_ae (deriv_twoRayCorner_ae z₀ u v R)).mpr ?_
  have hmeas : Measurable (fun t : ℝ => if t < 0 then -u else v) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  refine (intervalIntegrable_const (c := max ‖u‖ ‖v‖)).mono_fun' hmeas.aestronglyMeasurable ?_
  filter_upwards with t
  rcases lt_or_ge t 0 with h | h
  · rw [if_pos h, norm_neg]
    exact le_max_left _ _
  · rw [if_neg (not_lt.mpr h)]
    exact le_max_right _ _

/-- **The index principal value along a two-ray corner vanishes.** For nonzero rays of equal
length the excision `‖γ t - z₀‖ > ε` is the symmetric condition `|t| ‖v‖ > ε`, and the integrand is
the odd function `1 / t` on both rays, so *every* truncated integral is `0` — not merely its limit.
Equal norms also permit `u = v = 0`, where the curve is constant at `z₀` and the integrand vanishes
identically; that case is immediate. -/
theorem hasCauchyPVAt_inv_sub_twoRayCorner {z₀ u v : ℂ} (huv : ‖u‖ = ‖v‖) (R : ℝ) :
    HasCauchyPVAt (twoRayCorner z₀ u v) (-R) R (fun z => (z - z₀)⁻¹) z₀ 0 := by
  rcases eq_or_ne u 0 with rfl | hu
  · -- Equal lengths force the other ray to vanish too, leaving the constant curve at `z₀`.
    have hv : v = 0 := by simpa [eq_comm] using huv
    subst hv
    refine HasCauchyPVAt.intro ?_ ?_ <;> simp [twoRayCorner]
  · have hv : v ≠ 0 := fun h => hu (by rw [← norm_eq_zero, huv, h, norm_zero])
    refine HasCauchyPVAt.intro ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine intervalIntegrable_truncated_mul_deriv (γ := twoRayCorner z₀ u v)
        (f := fun z : ℂ => (z - z₀)⁻¹) (z₀ := z₀) (M := ε⁻¹)
        (intervalIntegrable_deriv_twoRayCorner z₀ u v R) ?_ ?_
      · have hstep : Measurable (fun t : ℝ => if t < 0 then -u else v) :=
          Measurable.ite (measurableSet_lt measurable_id measurable_const)
            measurable_const measurable_const
        refine MeasureTheory.AEStronglyMeasurable.congr
          (f := fun t : ℝ => if ‖twoRayCorner z₀ u v t - z₀‖ > ε then
            (twoRayCorner z₀ u v t - z₀)⁻¹ * (if t < 0 then -u else v) else 0) ?_ ?_
        · refine (Measurable.ite ?_ ?_ measurable_const).aestronglyMeasurable
          · exact measurableSet_lt measurable_const
              (((measurable_twoRayCorner z₀ u v).sub measurable_const).norm)
          · exact (((measurable_twoRayCorner z₀ u v).sub measurable_const).inv).mul hstep
        · filter_upwards [deriv_twoRayCorner_ae z₀ u v R] with s hs
          rw [hs]
      · intro s hs
        rw [norm_inv]
        simpa using one_div_le_one_div_of_le hε (le_of_lt hs)
    · simp_rw [integral_truncated_inv_twoRayCorner hu hv huv R]
      exact tendsto_const_nhds

/-- Existence form of `hasCauchyPVAt_inv_sub_twoRayCorner`, matching the existence-form API that
the winding-number composition lemmas consume. -/
theorem cauchyPVExistsAt_inv_sub_twoRayCorner {z₀ u v : ℂ} (huv : ‖u‖ = ‖v‖) (R : ℝ) :
    CauchyPVExistsAt (twoRayCorner z₀ u v) (-R) R (fun z => (z - z₀)⁻¹) z₀ :=
  CauchyPVExistsAt.intro (hasCauchyPVAt_inv_sub_twoRayCorner huv R)

/-- **The generalized winding number of a two-ray corner vanishes.** The radial approach and
departure contribute nothing to the model sector's index; all of it comes from the arc. -/
@[simp]
theorem windingNumber_eq_zero_twoRayCorner {z₀ u v : ℂ} (huv : ‖u‖ = ‖v‖) (R : ℝ) :
    windingNumber (twoRayCorner z₀ u v) (-R) R z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_twoRayCorner huv R)]
  ring

end TauCeti.Contour

end

end
