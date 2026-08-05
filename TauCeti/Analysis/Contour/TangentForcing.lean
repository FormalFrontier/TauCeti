/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Chord.TangentBound
public import TauCeti.Analysis.Contour.RegularityConditions
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Tangent forcing: flatness bounds the deviation against the tangent

`Contour.FlatOfOrder γ t₀ n` bounds the perpendicular deviation of the curve against **some**
non-zero one-sided witness directions. This file shows the witnesses are forced onto the actual
one-sided tangents: if `γ` has one-sided derivative `L ≠ 0` and is flat of order `n ≥ 1`, the
flatness direction is a real multiple of `L`, so the deviation bound transfers to `L` itself —
the exact hypothesis the higher-order antiderivative asymptotics
(`Contour.antiderivative_diff_at_tangent_target_tendsto_zero_right` / `_left`) consume.

## Main results

* `Contour.FlatOfOrder.tangentDeviation_isLittleO_right` — from flatness of order `n ≥ 1` and a
  right derivative `L ≠ 0`, the deviation against `L` is `o(‖γ t - γ t₀‖ ^ n)` from the right.
* `Contour.FlatOfOrder.tangentDeviation_isLittleO_left` — the left counterpart.

## Provenance

New to the raw-curve development: the AINTLIB `LeanModularForms` flatness structure
(`IsFlatOfOrder`) is indexed by the tangent, so no forcing step was needed there; the roadmap's
`Contour.FlatOfOrder` quantifies its witness directions existentially, and this file supplies
the bridge. The forcing argument is the standard one: the curve leaves `t₀` tangent to `L`, so a
line it hugs to first order can only be `ℝ • L`. See N. Hungerbühler, M. Wasem, *Non-integer
valued winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Filter Set Topology

/-- Near `t₀`, the curve's displacement grows at most linearly along the right derivative:
for `n ≥ 1`, if `γ` has right derivative `L` at `t₀`, then there is a constant `C > 0` such that
eventually as `t → t₀⁺` one has `‖γ t - γ t₀‖ ^ n ≤ C * (t - t₀)`. -/
private theorem eventually_norm_sub_pow_le_of_hasDerivWithinAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hn : 1 ≤ n) (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t in 𝓝[>] t₀, ‖γ t - γ t₀‖ ^ n ≤ C * (t - t₀) := by
  obtain ⟨c, hc, hbound⟩ := (h_deriv.hasFDerivWithinAt.isBigO_sub).exists_pos
  refine ⟨c ^ n, by positivity, ?_⟩
  have h_small : ∀ᶠ t in 𝓝[>] t₀, t - t₀ ≤ 1 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (by linarith : t₀ < t₀ + 1))] with t ht
    linarith
  filter_upwards [hbound.bound, h_small, self_mem_nhdsWithin] with t hb hs ht
  have ht' : 0 < t - t₀ := sub_pos.mpr ht
  rw [Real.norm_of_nonneg ht'.le] at hb
  calc ‖γ t - γ t₀‖ ^ n ≤ (c * (t - t₀)) ^ n := by gcongr
    _ = c ^ n * (t - t₀) ^ n := by rw [mul_pow]
    _ ≤ c ^ n * (t - t₀) := by
        gcongr
        exact pow_le_of_le_one ht'.le hs (by omega : n ≠ 0)

/-- The seminorm-triangle estimate behind the forcing bound: writing the tangent step
`(t - t₀) • L` as the chord `γ t - γ t₀` minus the first-order error, the tangent's
`|Im(· * conj v)| / ‖v‖` value is bounded by the chord's plus the error norm. -/
private theorem abs_im_mul_conj_div_mul_le_of_sub_smul {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {t : ℝ}
    (hv : v ≠ 0) (ht' : 0 < t - t₀) :
    |(L * starRingEnd ℂ v).im| / ‖v‖ * (t - t₀) ≤
      |((γ t - γ t₀) * star v).im| / ‖v‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
  rw [Complex.star_def, ← norm_tangentDeviation hv, ← norm_tangentDeviation hv]
  have hstep : ‖tangentDeviation L v‖ * (t - t₀) =
      ‖tangentDeviation ((t - t₀) • L) v‖ := by
    rw [tangentDeviation_real_smul, norm_smul, Real.norm_of_nonneg ht'.le]; ring
  have hdev : tangentDeviation ((t - t₀) • L) v =
      tangentDeviation (γ t - γ t₀) v - tangentDeviation (γ t - γ t₀ - (t - t₀) • L) v :=
    (congrArg (tangentDeviation · v) (by abel : ((t - t₀) • L : ℂ) =
      (γ t - γ t₀) - (γ t - γ t₀ - (t - t₀) • L))).trans (tangentDeviation_sub _ _ _)
  rw [hstep, hdev]
  refine (norm_sub_le _ _).trans ?_
  gcongr
  exact norm_tangentDeviation_le hv _

/-- The ε-bound at the heart of the forcing argument: under the little-o flatness deviation
`o(‖γ t - γ t₀‖ ^ n)` and a right derivative `L`, the normalized tangent value
`|Im(L * conj v)| / ‖v‖` is bounded by the given positive `ε`. (The zero-forcing conclusion
`Im(L · conj v) = 0` is drawn by the caller `im_mul_conj_eq_zero_of_flat_right`.) -/
private theorem abs_im_mul_conj_div_le_of_isLittleO {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) {ε : ℝ} (hε : 0 < ε) :
    |(L * starRingEnd ℂ v).im| / ‖v‖ ≤ ε := by
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with hc_def
  have herr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[𝓝[>] t₀] (fun t => t - t₀) :=
    hasDerivWithinAt_iff_isLittleO.mp h_deriv
  obtain ⟨C, hC, h_pow⟩ := eventually_norm_sub_pow_le_of_hasDerivWithinAt hn h_deriv
  set ε' : ℝ := ε / (2 * C) with hε'_def
  have hε' : 0 < ε' := by positivity
  have h_dev_bound := (isLittleO_iff.mp h_dev) hε'
  have h_err_bound := (isLittleO_iff.mp herr) (c := ε / 2) (by positivity)
  have h_all : ∀ᶠ t in 𝓝[>] t₀, c * (t - t₀) ≤ ε * (t - t₀) := by
    filter_upwards [h_dev_bound, h_err_bound, h_pow, self_mem_nhdsWithin] with t hd he hp ht
    have ht' : 0 < t - t₀ := sub_pos.mpr ht
    have h_tri := abs_im_mul_conj_div_mul_le_of_sub_smul (γ := γ) (L := L) hv ht'
    rw [Real.norm_eq_abs, abs_of_pos ht'] at he
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hd
    have hd' : |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * (C * (t - t₀)) := by
      calc |((γ t - γ t₀) * star v).im| / ‖v‖ ≤ ε' * ‖γ t - γ t₀‖ ^ n := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) n)] using hd
        _ ≤ ε' * (C * (t - t₀)) := by gcongr
    have hε'_eq : ε' * C = ε / 2 := by
      rw [hε'_def]
      field_simp
    calc c * (t - t₀) ≤ |((γ t - γ t₀) * star v).im| / ‖v‖ +
          ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
      _ ≤ ε' * (C * (t - t₀)) + ε / 2 * (t - t₀) := by
          gcongr
      _ = ε * (t - t₀) := by rw [← mul_assoc, hε'_eq]; ring
  obtain ⟨t, hct, ht⟩ := (h_all.and self_mem_nhdsWithin).exists
  exact le_of_mul_le_mul_right hct (sub_pos.mpr ht)

/-- The forcing core (right side): a flatness deviation bound of order `n ≥ 1` against `v ≠ 0`,
together with a right derivative `L`, forces `Im(L · conj v) = 0` — the flatness direction and
the tangent are colinear. -/
private theorem im_mul_conj_eq_zero_of_flat_right {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := |(L * starRingEnd ℂ v).im| / ‖v‖ with hc_def
  have hc_nonneg : 0 ≤ c := by positivity
  have hc_le : ∀ ε : ℝ, 0 < ε → c ≤ ε :=
    fun ε hε => abs_im_mul_conj_div_le_of_isLittleO hv hn h_dev h_deriv hε
  rcases eq_or_lt_of_le hc_nonneg with h0 | hpos
  · have h' : |(L * starRingEnd ℂ v).im| / ‖v‖ = 0 := by rw [← hc_def, ← h0]
    exact abs_eq_zero.mp ((div_eq_zero_iff.mp h').resolve_right hv_pos.ne')
  · exact absurd (hc_le (c / 2) (by linarith)) (by linarith)

/-- The forcing core (left side): derived from `im_mul_conj_eq_zero_of_flat_right` by the
reflection `t ↦ 2t₀ - t`, which carries the left data of `γ` to right data of the reflected
curve with tangent `-L` — and `Im((-L) · conj v) = 0` iff `Im(L · conj v) = 0`. -/
private theorem im_mul_conj_eq_zero_of_flat_left {γ : ℝ → ℂ} {t₀ : ℝ} {v L : ℂ} {n : ℕ}
    (hv : v ≠ 0) (hn : 1 ≤ n) (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (L * starRingEnd ℂ v).im = 0 := by
  have ht₀ : 2 * t₀ - t₀ = t₀ := by ring
  have hσ : Tendsto (fun t => 2 * t₀ - t) (𝓝[>] t₀) (𝓝[<] t₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun t : ℝ => 2 * t₀ - t) (𝓝 t₀) (𝓝 (2 * t₀ - t₀)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [ht₀] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_Iio]
      linarith [mem_Ioi.mp ht]
  have h_dev' : (fun t => |((γ (2 * t₀ - t) - γ (2 * t₀ - t₀)) * star v).im| / ‖v‖)
      =o[𝓝[>] t₀] fun t => ‖γ (2 * t₀ - t) - γ (2 * t₀ - t₀)‖ ^ n := by
    rw [ht₀]
    exact h_dev.comp_tendsto hσ
  have h_deriv' : HasDerivWithinAt (fun t => γ (2 * t₀ - t)) (-L) (Ioi t₀) t₀ := by
    have hg : HasDerivWithinAt γ L (Iio t₀) (2 * t₀ - t₀) := by
      rw [ht₀]
      exact h_deriv
    have hh : HasDerivWithinAt (fun t : ℝ => 2 * t₀ - t) (-1) (Ioi t₀) t₀ :=
      (hasDerivWithinAt_id t₀ (Ioi t₀)).const_sub (2 * t₀)
    have h := hg.scomp t₀ hh fun t ht => by
      simp only [mem_Iio]
      linarith [mem_Ioi.mp ht]
    rw [neg_one_smul] at h
    exact h
  have h_im := im_mul_conj_eq_zero_of_flat_right hv hn h_dev' h_deriv'
  rw [neg_mul, Complex.neg_im, neg_eq_zero] at h_im
  exact h_im

/-- Shared transfer step: once the flatness direction `v` is forced onto the tangent
(`Im(L · conj v) = 0`, so `L ∈ ℝ • v`), the deviation bound against `v` becomes a deviation
bound against `L` by line-invariance of the deviation norm. -/
private theorem tangentDeviation_isLittleO_of_im_mul_conj_eq_zero {γ : ℝ → ℂ} {t₀ : ℝ}
    {v L : ℂ} {n : ℕ} {l : Filter ℝ} (hv : v ≠ 0) (hL : L ≠ 0) (h_im : (L * starRingEnd ℂ v).im = 0)
    (h_dev : (fun t => |((γ t - γ t₀) * star v).im| / ‖v‖) =o[l]
      fun t => ‖γ t - γ t₀‖ ^ n) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[l]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨cc, hcc⟩ := exists_real_smul_of_im_mul_conj_eq_zero hv h_im
  have hcc_ne : cc ≠ 0 := fun h0 => hL (by rw [hcc, h0, zero_smul])
  have hkey : ∀ t, ‖tangentDeviation (γ t - γ t₀) L‖ =
      |((γ t - γ t₀) * star v).im| / ‖v‖ := fun t => by
    rw [hcc, norm_tangentDeviation_smul_real hcc_ne hv, norm_tangentDeviation hv,
      Complex.star_def]
  exact h_dev.congr' (Filter.Eventually.of_forall fun t => (hkey t).symm) Filter.EventuallyEq.rfl

/-- **Flatness bounds the deviation against the right tangent**: from `FlatOfOrder γ t₀ n`
(`n ≥ 1`) and a right derivative `L ≠ 0`, the perpendicular deviation against `L` itself is
`o(‖γ t - γ t₀‖ ^ n)` from the right — the hypothesis the higher-order antiderivative
asymptotics consume. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_right {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, hvp, hvm, hr, -⟩ := flatOfOrder_iff.mp hflat
  exact tangentDeviation_isLittleO_of_im_mul_conj_eq_zero hvp hL
    (im_mul_conj_eq_zero_of_flat_right hvp hn hr h_deriv) hr

/-- **Flatness bounds the deviation against the left tangent**: the counterpart of
`FlatOfOrder.tangentDeviation_isLittleO_right` from the left. -/
theorem FlatOfOrder.tangentDeviation_isLittleO_left {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {n : ℕ}
    (hflat : FlatOfOrder γ t₀ n) (hn : 1 ≤ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - γ t₀‖ ^ n := by
  obtain ⟨vp, vm, hvp, hvm, -, hl⟩ := flatOfOrder_iff.mp hflat
  exact tangentDeviation_isLittleO_of_im_mul_conj_eq_zero hvm hL
    (im_mul_conj_eq_zero_of_flat_left hvm hn hl h_deriv) hl

end TauCeti.Contour

end
