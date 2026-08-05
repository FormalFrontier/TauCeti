/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Strict monotonicity of the distance to a crossed point

Near a transverse crossing — `γ t₀ = s` with non-zero one-sided derivative limit `L`, for a
curve `γ : ℝ → F` into a real inner product space — the distance `‖γ t - s‖` is strictly
monotone on a one-sided closed interval at `t₀`: increasing to
the right, decreasing to the left. Consequently the curve exits each small disc around `s`
exactly once on each side, which is what lets the crossing analysis of the generalized residue
theorem invert `ε ↦ exit time` and build the excision cutoffs of the principal value.

The mechanism: `(d/dt)‖γ t - s‖² = 2⟪γ t - s, deriv γ t⟫_ℝ`, whose leading term
`(t - t₀)‖L‖²` dominates the differentiation errors on a small one-sided interval.

## Main results

* `Contour.exists_strictMonoOn_norm_sub_right` — `‖γ t - s‖` is strictly increasing on
  `[t₀, t₀ + r]` for some `r > 0`.
* `Contour.exists_strictAntiOn_norm_sub_left` — `‖γ t - s‖` is strictly decreasing on
  `[t₀ - r, t₀]` for some `r > 0`.

## Provenance

Migrated from `norm_sub_strictMonoOn_right` and `norm_sub_strictAntiOn_left` of
`CrossingDataBuilder.lean` in the AINTLIB `LeanModularForms` development, restated for a raw
curve (there the eventual differentiability comes from a bundled `ClosedPwC1Immersion`); the
left lemma is derived from the right one by the reflection `t ↦ 2t₀ - t` instead of repeating
the argument. See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a
generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Two-sided inner-product expansion bound.** Near a one-sided derivative limit `L`, the
derivative of `‖γ t - s‖²` (up to the factor `2`) deviates from its leading term
`(t - t₀)‖L‖²` by at most `|t - t₀|‖L‖²/2`. Both one-sided strict-monotonicity statements read
off their sign from this single bound. -/
private theorem abs_inner_chord_deriv_sub_le {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) {u : Set ℝ} (h_deriv : HasDerivWithinAt γ L u t₀)
    (hL_tendsto : Tendsto (deriv γ) (𝓝[u] t₀) (𝓝 L)) :
    ∀ᶠ t in 𝓝[u] t₀,
      |inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2| ≤ |t - t₀| * ‖L‖ ^ 2 / 2 := by
  have hr := hasDerivWithinAt_iff_isLittleO.mp h_deriv
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_deriv_close : ∀ᶠ t in 𝓝[u] t₀, ‖deriv γ t - L‖ < η := by
    filter_upwards [(Metric.tendsto_nhds.mp hL_tendsto) η hη_pos] with t ht
    rwa [dist_eq_norm] at ht
  filter_upwards [hr.def hη_pos, h_deriv_close] with t h_chord_t h_dclose_t
  set R : F := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : F := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * |t - t₀| := by rwa [Real.norm_eq_abs] at h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  have h_err_LD : |inner ℝ L D| ≤ ‖L‖ * η :=
    (abs_real_inner_le_norm L D).trans
      (mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _))
  have h_err_RL : |inner ℝ R L| ≤ η * |t - t₀| * ‖L‖ :=
    (abs_real_inner_le_norm R L).trans
      (mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _))
  have h_err_RD : |inner ℝ R D| ≤ η * |t - t₀| * η :=
    (abs_real_inner_le_norm R D).trans
      (mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity))
  have h_err_tLD : |(t - t₀) * inner ℝ L D| ≤ |t - t₀| * (‖L‖ * η) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h_err_LD (abs_nonneg _)
  have h_expand : inner ℝ (γ t - s) (deriv γ t) - (t - t₀) * ‖L‖ ^ 2 =
      (t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D := by
    rw [show γ t - s = (t - t₀) • L + R by rw [hR_def, h_at]; abel,
      show deriv γ t = L + D by rw [hD_def]; abel,
      inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have h_eta_bound : 2 * η * ‖L‖ + η ^ 2 ≤ ‖L‖ ^ 2 / 2 := by
    rw [hη_def]
    nlinarith [hL_pos]
  rw [h_expand]
  calc |(t - t₀) * inner ℝ L D + inner ℝ R L + inner ℝ R D|
      ≤ |(t - t₀) * inner ℝ L D| + |inner ℝ R L| + |inner ℝ R D| := abs_add_three _ _ _
    _ ≤ |t - t₀| * (‖L‖ * η) + η * |t - t₀| * ‖L‖ + η * |t - t₀| * η := by gcongr
    _ ≤ |t - t₀| * ‖L‖ ^ 2 / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h_eta_bound (abs_nonneg (t - t₀))]

/-- **The distance to a crossed point is strictly increasing to the right of the crossing**:
for a curve through `s = γ t₀` with non-zero right derivative limit `L`, continuity at `t₀`,
and eventual differentiability on the right, `‖γ t - s‖` is strictly monotone on `[t₀, t₀ + r]`
for some `r > 0` — the curve exits each small disc around `s` exactly once. -/
theorem exists_strictMonoOn_norm_sub_right {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + r)) := by
  have h_combined : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t ∧
      (t - t₀) * ‖L‖ ^ 2 / 2 ≤ inner ℝ (γ t - s) (deriv γ t) := by
    filter_upwards [hγ_diff,
      abs_inner_chord_deriv_sub_le h_at hL
        (hasDerivWithinAt_Ioi_of_tendsto_deriv hγ_cont hγ_diff hL_right) hL_right,
      self_mem_nhdsWithin] with t h_diff h_abs ht
    rw [abs_of_pos (show (0 : ℝ) < t - t₀ from sub_pos.mpr ht)] at h_abs
    exact ⟨h_diff, by linarith [(abs_le.mp h_abs).1]⟩
  obtain ⟨c, hc, hr_data⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp h_combined
  refine ⟨c - t₀, sub_pos.mpr hc, ?_⟩
  rw [show t₀ + (c - t₀) = c from by ring]
  have h_γ_continuousOn : ContinuousOn γ (Icc t₀ c) := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h_eq | h_gt
    · rw [← h_eq]
      exact hγ_cont.continuousWithinAt
    · exact (hr_data ⟨h_gt, ht.2⟩).1.continuousAt.continuousWithinAt
  have h_f_strictMono : StrictMonoOn (fun t => ‖γ t - s‖ ^ 2) (Icc t₀ c) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun t => 2 * inner ℝ (γ t - s) (deriv γ t))
      (fun t ht => (((h_γ_continuousOn t ht).sub continuousWithinAt_const).norm).pow 2)
    · intro t ht
      rw [interior_Icc] at ht
      exact (((hr_data ⟨ht.1, ht.2.le⟩).1.hasDerivAt.sub_const s).norm_sq).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hL_sq_pos : 0 < ‖L‖ ^ 2 := by positivity
      linarith [(hr_data ⟨ht.1, ht.2.le⟩).2, mul_pos (sub_pos.mpr ht.1) hL_sq_pos]
  exact fun a ha b hb hab =>
    lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) (h_f_strictMono ha hb hab)

/-- The reflection `t ↦ 2t₀ - t` carries the right-sided neighbourhood filter at `t₀` to the
left-sided one. -/
private theorem tendsto_reflection_nhdsGT (t₀ : ℝ) :
    Tendsto (fun t => 2 * t₀ - t) (𝓝[>] t₀) (𝓝[<] t₀) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun t : ℝ => 2 * t₀ - t) (𝓝 t₀) (𝓝 (2 * t₀ - t₀)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [show 2 * t₀ - t₀ = t₀ from by ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_Iio]
    linarith [mem_Ioi.mp ht]

/-- **The distance to a crossed point is strictly decreasing to the left of the crossing**: the
counterpart of `exists_strictMonoOn_norm_sub_right`, derived from it by the reflection
`t ↦ 2t₀ - t` (which carries the left data of `γ` to right data of the reflected curve with
derivative limit `-L`). -/
theorem exists_strictAntiOn_norm_sub_left {γ : ℝ → F} {t₀ : ℝ} {s : F} (h_at : γ t₀ = s)
    {L : F} (hL : L ≠ 0) (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - r) t₀) := by
  have ht₀ : 2 * t₀ - t₀ = t₀ := by ring
  have hσ := tendsto_reflection_nhdsGT t₀
  -- the reflected curve is pinned as a lambda so that `exists_strictMonoOn_norm_sub_right`
  -- instantiates against it (not against `γ` at the point `2 * t₀ - t₀`)
  have h_at' : (fun t => γ (2 * t₀ - t)) t₀ = s := by
    change γ (2 * t₀ - t₀) = s
    rw [ht₀]
    exact h_at
  have hL_right' : Tendsto (deriv fun t => γ (2 * t₀ - t)) (𝓝[>] t₀) (𝓝 (-L)) := by
    refine Tendsto.congr (fun t => (deriv_comp_const_sub γ (2 * t₀) t).symm) ?_
    exact (hL_left.comp hσ).neg
  have hγ_cont' : ContinuousAt (fun t => γ (2 * t₀ - t)) t₀ := by
    refine ContinuousAt.comp ?_ ((continuous_const.sub continuous_id).continuousAt)
    rw [ht₀]
    exact hγ_cont
  have hγ_diff' : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ (fun t => γ (2 * t₀ - t)) t := by
    filter_upwards [hσ.eventually hγ_diff] with t ht
    exact differentiableAt_comp_const_sub.mpr ht
  obtain ⟨r, hr, hmono⟩ := exists_strictMonoOn_norm_sub_right
    (γ := fun t => γ (2 * t₀ - t)) (t₀ := t₀) h_at' (neg_ne_zero.mpr hL)
    hL_right' hγ_cont' hγ_diff'
  refine ⟨r, hr, fun a ha b hb hab => ?_⟩
  have h := hmono (a := 2 * t₀ - b) (b := 2 * t₀ - a)
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
    ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  simpa [show 2 * t₀ - (2 * t₀ - b) = b from by ring,
    show 2 * t₀ - (2 * t₀ - a) = a from by ring] using h

end TauCeti.Contour

end
