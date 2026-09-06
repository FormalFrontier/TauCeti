/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Negative powers of the distance to a point, integrated along a segment

A function with an algebraic singularity at a point `p` is still integrable along a segment
passing arbitrarily close to `p`, provided the exponent is larger than `-1`.  This file proves
the quantitative form of that statement in `ℂ`.

The geometric input is that on the segment from `w` to `z`, parametrized by `[0, 1]`, the
distance to `p` is at least the length of the segment times the distance of the parameter to a
fixed parameter `c`, namely the foot of the perpendicular from `p` clamped to `[0, 1]`.  Both
pieces of the parameter interval then compare with a power of the distance to `c`, whose integral
Mathlib computes, and the singularity contributes only the finite constant `2 / (u + 1)`.

## Main results

* `TauCeti.exists_mem_Icc_mul_abs_sub_le_dist` -- the lower bound for the distance to `p` along
  a segment.
* `TauCeti.integral_dist_rpow_segment_le` -- the arclength integral of `dist ⬝ p ^ u` along a
  segment of length `L` is at most `2 / (u + 1) * L ^ (u + 1)` when `-1 < u ≤ 0`.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- On the segment from `w` to `z`, the distance to a point `p` is bounded below by the length of
the segment times the distance of the parameter to a fixed parameter `c ∈ [0, 1]`.  Geometrically
`c` is the foot of the perpendicular from `p`, clamped to the parameter interval. -/
theorem exists_mem_Icc_mul_abs_sub_le_dist (p z w : ℂ) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖z - w‖ * |s - c| ≤ dist (w + (s : ℂ) * (z - w)) p := by
  rcases eq_or_ne z w with rfl | hzw
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, fun s _ => by simp⟩
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  set A : ℂ := w - p with hA
  set B : ℂ := z - w with hB
  set q : ℝ := A.re * B.re + A.im * B.im with hq
  set s₀ : ℝ := -q / ‖B‖ ^ 2 with hs₀
  have key : ∀ t : ℝ, ‖B‖ * |t - s₀| ≤ ‖A + (t : ℂ) * B‖ := by
    intro t
    have hB2 : ‖B‖ ^ 2 = B.re * B.re + B.im * B.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have hA2 : ‖A‖ ^ 2 = A.re * A.re + A.im * A.im := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    have hnorm : ‖A + (t : ℂ) * B‖ ^ 2 =
        (A.re + t * B.re) * (A.re + t * B.re) + (A.im + t * B.im) * (A.im + t * B.im) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp
    have hdiv : q ^ 2 / ‖B‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      rw [div_le_iff₀ (pow_pos hL 2), hA2, hB2, hq]
      nlinarith [sq_nonneg (A.re * B.im - A.im * B.re)]
    have hsq : (‖B‖ * |t - s₀|) ^ 2 ≤ ‖A + (t : ℂ) * B‖ ^ 2 := by
      have hexp : (‖B‖ * |t - s₀|) ^ 2 =
          ‖B‖ ^ 2 * t ^ 2 + 2 * t * q + q ^ 2 / ‖B‖ ^ 2 := by
        rw [mul_pow, sq_abs, hs₀]
        field_simp
        ring
      rw [hexp, hnorm]
      nlinarith [hdiv, hA2, hB2]
    have := abs_le_of_sq_le_sq' hsq (norm_nonneg _)
    exact this.2
  refine ⟨max 0 (min 1 s₀), ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, ?_⟩
  intro s hs
  have hclamp : |s - max 0 (min 1 s₀)| ≤ |s - s₀| := by
    rcases le_or_gt s₀ 0 with h | h
    · rw [min_eq_right (h.trans zero_le_one), max_eq_left h, sub_zero,
        abs_of_nonneg hs.1, abs_of_nonneg (by linarith [hs.1] : (0 : ℝ) ≤ s - s₀)]
      linarith
    rcases le_or_gt s₀ 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h.le]
    · rw [min_eq_left h'.le, max_eq_right zero_le_one]
      rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos (by linarith [hs.2])]
      linarith
  have hseg : w + (s : ℂ) * (z - w) - p = A + (s : ℂ) * B := by
    rw [hA, hB]; ring
  calc ‖z - w‖ * |s - max 0 (min 1 s₀)| ≤ ‖B‖ * |s - s₀| := by
        rw [hB]
        exact mul_le_mul_of_nonneg_left hclamp (norm_nonneg _)
    _ ≤ ‖A + (s : ℂ) * B‖ := key s
    _ = dist (w + (s : ℂ) * (z - w)) p := by rw [dist_eq_norm, hseg]

/-- The arclength integral of a negative power of the distance to `p` along the segment from `w`
to `z`: the parameter integral over `[0, 1]` is multiplied by the length `‖z - w‖` of the segment.
The exponent range `-1 < u ≤ 0` is exactly the one in which the singularity of `dist ⬝ p ^ u` is
integrable, and the bound `2 / (u + 1) * ‖z - w‖ ^ (u + 1)` is uniform in the position of `p`. -/
theorem integral_dist_rpow_segment_le {p : ℂ} {u : ℝ} (hu : -1 < u) (hu0 : u ≤ 0)
    {z w : ℂ} (hne : ∀ s ∈ Icc (0 : ℝ) 1, w + (s : ℂ) * (z - w) ≠ p) :
    (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖
      ≤ 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  have hcontγ : Continuous fun s : ℝ => w + (s : ℂ) * (z - w) := by fun_prop
  have hcontd : Continuous fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p :=
    hcontγ.dist continuous_const
  have hcont : ContinuousOn (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) (Icc 0 1) :=
    hcontd.continuousOn.rpow_const fun s hs =>
      Or.inl (fun h => hne s hs (by rwa [dist_eq_zero] at h))
  rcases eq_or_ne z w with rfl | hzw
  · rw [sub_self, norm_zero, mul_zero, Real.zero_rpow hu1.ne', mul_zero]
  have hL : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hzw)
  obtain ⟨c, hc, hclamp⟩ := exists_mem_Icc_mul_abs_sub_le_dist p z w
  have hi1 : IntervalIntegrable (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) volume 0 c :=
    (hcont.mono (by rw [uIcc_of_le hc.1]; exact Icc_subset_Icc le_rfl hc.2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s : ℝ => dist (w + (s : ℂ) * (z - w)) p ^ u) volume c 1 :=
    (hcont.mono (by rw [uIcc_of_le hc.2]; exact Icc_subset_Icc hc.1 le_rfl)).intervalIntegrable
  have hae : ∀ (b : ℝ), ∀ᵐ s ∂(volume.restrict (Icc c b)), s ≠ c := by
    intro b
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  have hae' : ∀ (b : ℝ), ∀ᵐ s ∂(volume.restrict (Icc b c)), s ≠ c := by
    intro b
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  -- the piece to the right of the foot of the perpendicular
  have hb2 : (∫ s in c..(1 : ℝ), dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * ((1 - c) ^ (u + 1) / (u + 1)) := by
    have hint2 : IntervalIntegrable
        (fun s : ℝ => ‖z - w‖ ^ u * (s - c) ^ u) volume c 1 := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1 - c) hu).comp_sub_right
        c
      simpa using h.const_mul (‖z - w‖ ^ u)
    have hmono := intervalIntegral.integral_mono_ae_restrict hc.2 hi2 hint2 ?_
    · refine hmono.trans_eq ?_
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ u) c, sub_self,
        integral_rpow (Or.inl hu), Real.zero_rpow hu1.ne']
      ring
    · filter_upwards [hae 1, self_mem_ae_restrict (measurableSet_Icc (a := c) (b := 1))]
        with s hsne hsmem
      have hcs : c < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hc.1.trans hsmem.1, hsmem.2⟩
      have hpos : 0 < ‖z - w‖ * (s - c) := by positivity
      have hle : ‖z - w‖ * (s - c) ≤ dist (w + (s : ℂ) * (z - w)) p := by
        have := hclamp s hs01
        rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - c)] at this
      calc dist (w + (s : ℂ) * (z - w)) p ^ u ≤ (‖z - w‖ * (s - c)) ^ u :=
            Real.rpow_le_rpow_of_nonpos hpos hle hu0
        _ = ‖z - w‖ ^ u * (s - c) ^ u :=
            Real.mul_rpow (norm_nonneg _) (by linarith)
  -- the piece to the left of the foot of the perpendicular
  have hb1 : (∫ s in (0 : ℝ)..c, dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * (c ^ (u + 1) / (u + 1)) := by
    have hint1 : IntervalIntegrable
        (fun s : ℝ => ‖z - w‖ ^ u * (c - s) ^ u) volume 0 c := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) hu).comp_sub_left c
      simpa using (h.const_mul (‖z - w‖ ^ u)).symm
    have hmono := intervalIntegral.integral_mono_ae_restrict hc.1 hi1 hint1 ?_
    · refine hmono.trans_eq ?_
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ u) c, sub_self, sub_zero,
        integral_rpow (Or.inl hu), Real.zero_rpow hu1.ne']
      ring
    · filter_upwards [hae' 0, self_mem_ae_restrict (measurableSet_Icc (a := 0) (b := c))]
        with s hsne hsmem
      have hsc : s < c := lt_of_le_of_ne hsmem.2 hsne
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hsmem.1, hsmem.2.trans hc.2⟩
      have hpos : 0 < ‖z - w‖ * (c - s) := by positivity
      have hle : ‖z - w‖ * (c - s) ≤ dist (w + (s : ℂ) * (z - w)) p := by
        have := hclamp s hs01
        rwa [abs_of_nonpos (by linarith : s - c ≤ (0 : ℝ)), neg_sub] at this
      calc dist (w + (s : ℂ) * (z - w)) p ^ u ≤ (‖z - w‖ * (c - s)) ^ u :=
            Real.rpow_le_rpow_of_nonpos hpos hle hu0
        _ = ‖z - w‖ ^ u * (c - s) ^ u :=
            Real.mul_rpow (norm_nonneg _) (by linarith)
  have hsplit : (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u)
      = (∫ s in (0 : ℝ)..c, dist (w + (s : ℂ) * (z - w)) p ^ u)
        + ∫ s in c..(1 : ℝ), dist (w + (s : ℂ) * (z - w)) p ^ u :=
    (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hc1 : c ^ (u + 1) ≤ 1 := Real.rpow_le_one hc.1 hc.2 hu1.le
  have hc2 : (1 - c) ^ (u + 1) ≤ 1 :=
    Real.rpow_le_one (by linarith [hc.2]) (by linarith [hc.1]) hu1.le
  have hbound : (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u)
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) := by
    rw [hsplit]
    have hnn : (0 : ℝ) ≤ ‖z - w‖ ^ u := Real.rpow_nonneg (norm_nonneg _) u
    calc _ ≤ ‖z - w‖ ^ u * (c ^ (u + 1) / (u + 1))
            + ‖z - w‖ ^ u * ((1 - c) ^ (u + 1) / (u + 1)) := add_le_add hb1 hb2
      _ ≤ ‖z - w‖ ^ u * (1 / (u + 1)) + ‖z - w‖ ^ u * (1 / (u + 1)) := by
          gcongr
      _ = ‖z - w‖ ^ u * (2 / (u + 1)) := by ring
  calc (∫ s in (0 : ℝ)..1, dist (w + (s : ℂ) * (z - w)) p ^ u) * ‖z - w‖
      ≤ ‖z - w‖ ^ u * (2 / (u + 1)) * ‖z - w‖ :=
        mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
    _ = 2 / (u + 1) * ‖z - w‖ ^ (u + 1) := by
        rw [Real.rpow_add hL, Real.rpow_one]
        ring

end TauCeti
