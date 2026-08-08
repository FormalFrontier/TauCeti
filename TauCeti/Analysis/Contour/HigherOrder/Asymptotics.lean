/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Chord.TangentBound
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Higher-order antiderivative asymptotics at an on-curve pole

For the higher-order pole integrand `1/(z-s)^k` (`k ≥ 2`) with single-valued antiderivative
`F(z) = -1/[(k-1)(z-s)^(k-1)]`, this file proves the asymptotics the sector-cancellation
argument of the generalized residue theorem consumes: along a branch of a curve leaving `s`
with one-sided tangent `L` and perpendicular deviation `o(‖γ t - s‖ ^ n)` (`n ≥ k`), the
difference `F(γ t) - F(tangent target)` tends to `0`, where the tangent target is the point of
the tangent ray at the same distance from `s`. Combined with the fundamental theorem of calculus
on each smooth piece, this replaces the curve by its tangent rays in the excised principal
value, up to a vanishing error.

## Main results

* `Contour.hasDerivAt_antiderivative_pow_inv` — the antiderivative of `1/(z-s)^k`.
* `Contour.norm_antiderivative_diff_le_segment_bound` — the mean-value bound for the
  antiderivative along a segment avoiding
  the pole.
* `Contour.chord_to_tangent_isLittleO` — the chord to the tangent target is `o(‖γ t - s‖ ^ n)`
  given the deviation bound, in the tangent hemisphere.
* `Contour.antiderivative_diff_at_tangent_target_tendsto_zero` — the parametrised core: the
  antiderivative difference to the
  tangent target tends to `0` for `2 ≤ k ≤ n`.
* `Contour.antiderivative_diff_at_tangent_target_tendsto_zero_right` / `_left` — the
  one-sided forms, from a
  one-sided derivative and the deviation bound against the tangent (`+L` ray on the right, `-L`
  ray on the left).

The one-sided forms take the deviation bound `‖tangentDeviation (γ t - s) L‖ = o(‖γ t - s‖ ^ n)`
as a hypothesis; producing it from `Contour.FlatOfOrder` (whose witness directions are
existential) is the tangent-forcing bridge, a separate step.

## Provenance

Migrated from `HungerbuhlerWasem/HigherOrderAsymptotics.lean` of the AINTLIB `LeanModularForms`
development, restated for the raw curve: the flatness hypotheses carried there by the
`IsFlatOfOrder` structure become explicit deviation bounds against the one-sided tangent. See
N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3 (eq. 3.4).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Complex Filter Set Topology

/-- **The antiderivative of `1/(z-s)^k`** (`k ≥ 2`): the function
`F(z) = -1/[(k-1)(z-s)^(k-1)]` has complex derivative `1/(z-s)^k` at any `z ≠ s`. -/
theorem hasDerivAt_antiderivative_pow_inv {s : ℂ} {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ s) :
    HasDerivAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
      (1 / (z - s) ^ k) z := by
  have h_pow : HasDerivAt (fun w : ℂ => (w - s) ^ (k - 1))
      (↑(k - 1) * (z - s) ^ (k - 1 - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const s).pow (k - 1)
  rw [show k - 1 - 1 = k - 2 from by omega] at h_pow
  have h_const := (h_pow.inv (pow_ne_zero _ (sub_ne_zero.mpr hz))).const_mul
    (-(↑(k - 1) : ℂ)⁻¹)
  have hk1 : (↑(k - 1) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 0 < k - 1).ne'
  have h_pow_k2_ne : (z - s) ^ (k - 2) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have h_pow2 : ((z - s) ^ (k - 1)) ^ 2 = (z - s) ^ k * (z - s) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  have hval : -(↑(k - 1) : ℂ)⁻¹ *
      (-(↑(k - 1) * (z - s) ^ (k - 2) * 1) / ((z - s) ^ (k - 1)) ^ 2) = 1 / (z - s) ^ k := by
    rw [h_pow2]
    field_simp
  exact hval ▸ h_const

/-- **Mean-value bound for the antiderivative along a segment.** When the segment from `z₁` to
`z₂` stays at distance `≥ ε` from `s`, the antiderivative difference satisfies
`‖F(z₂) - F(z₁)‖ ≤ ‖z₂ - z₁‖ / ε^k`. -/
theorem norm_antiderivative_diff_le_segment_bound
    {z₁ z₂ s : ℂ} {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (hε : 0 < ε)
    (h_seg_avoids : ∀ z ∈ segment ℝ z₁ z₂, ε ≤ ‖z - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((z₂ - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((z₁ - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / ε ^ k) * ‖z₂ - z₁‖ := by
  have h_deriv : ∀ z ∈ segment ℝ z₁ z₂,
      HasDerivWithinAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
        (1 / (z - s) ^ k) (segment ℝ z₁ z₂) z := by
    intro z hz
    have h_ne : z ≠ s := fun heq => by
      have := h_seg_avoids z hz; rw [heq, sub_self, norm_zero] at this; linarith
    exact (hasDerivAt_antiderivative_pow_inv hk h_ne).hasDerivWithinAt
  have h_bound : ∀ z ∈ segment ℝ z₁ z₂, ‖1 / (z - s) ^ k‖ ≤ 1 / ε ^ k := by
    intro z hz
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (pow_pos hε k)
      (pow_le_pow_left₀ hε.le (h_seg_avoids z hz) k)
  exact (convex_segment z₁ z₂).norm_image_sub_le_of_norm_hasDerivWithin_le h_deriv h_bound
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)

/-- **Eventual hemisphere condition.** If `T` is the outgoing tangent direction on `u` — i.e.
`(t - t₀) • L = |t - t₀| • T` for `t ∈ u` and `‖T‖ = ‖L‖` — then for `t` close to `t₀` within
`u`, the chord `γ t - s` lies in the `+T` hemisphere (`Re((γ t - s) · conj T) ≥ 0`). On
`Ioi t₀` this holds with `T = L`, on `Iio t₀` with `T = -L`. -/
private theorem eventually_re_mul_conj_nonneg
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {u : Set ℝ} {T : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_s : γ t₀ = s)
    (hT : ∀ t ∈ u, (t - t₀) • L = |t - t₀| • T) (hTL : ‖T‖ = ‖L‖) :
    ∀ᶠ t in 𝓝[u] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ T).re := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  rw [Real.norm_eq_abs] at h_b
  rw [show (γ t - s) = |t - t₀| • T + (γ t - γ t₀ - (t - t₀) • L) by
      rw [← hT t ht, h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((|t - t₀| : ℝ) • T * starRingEnd ℂ T).re = |t - t₀| * ‖T‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, hTL]
  have h2 : -(‖L‖ / 2 * |t - t₀|) * ‖L‖ ≤
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ T).re := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ T)
    rw [norm_mul, RCLike.norm_conj, hTL] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [abs_nonneg (t - t₀), sq_nonneg ‖L‖]

/-- With one-sided derivative `L ≠ 0` at `t₀` within `u ∌ t₀`, the curve cannot return to
`s = γ t₀` near `t₀` within `u`. -/
private theorem eventually_ne_of_hasDerivWithinAt
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {u : Set ℝ} (hu : t₀ ∉ u) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[u] t₀, γ t ≠ s := by
  filter_upwards [((hasDerivWithinAt_iff_tendsto_slope' hu).mp h_deriv).eventually_ne hL]
    with t ht h_eq
  exact ht (by rw [slope_def_module, h_eq, h_s, sub_self, smul_zero])

/-- **Chord-to-tangent-target `o`-bound (parametrised core).** In the `+T` hemisphere and off
`s`, the chord from `γ t` to the tangent target at the same distance is dominated by the
perpendicular deviation, hence `o(‖γ t - s‖ ^ n)` whenever the deviation is. The right side
instantiates `T = L`, `l = 𝓝[>] t₀`; the left side `T = -L`, `l = 𝓝[<] t₀`. -/
theorem chord_to_tangent_isLittleO {γ : ℝ → ℂ} {s : ℂ} {l : Filter ℝ} {T : ℂ} {n : ℕ} (hT : T ≠ 0)
    (h_re : ∀ᶠ t in l, 0 ≤ ((γ t - s) * starRingEnd ℂ T).re) (h_ne : ∀ᶠ t in l, γ t ≠ s)
    (h_dev : (fun t => ‖tangentDeviation (γ t - s) T‖) =o[l]
      fun t => ‖γ t - s‖ ^ n) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖) =o[l]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h_eventually_bound : ∀ᶠ t in l,
      ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ ≤ 2 * ‖tangentDeviation (γ t - s) T‖ := by
    filter_upwards [h_re, h_ne] with t h_pos h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)
    have h_chord := norm_chord_to_tangent_target_le hT hw_pos h_pos
    have h_div_bound : ‖tangentDeviation (γ t - s) T‖ ^ 2 / ‖γ t - s‖ ≤
        ‖tangentDeviation (γ t - s) T‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) T‖ / ‖γ t - s‖ ≤ 1 := by
        rw [div_le_one hw_pos]; exact norm_tangentDeviation_le hT _
      nlinarith [norm_nonneg (tangentDeviation (γ t - s) T)]
    linarith [h_chord]
  refine IsBigO.trans_isLittleO ?_ h_dev
  refine IsBigO.of_bound 2 ?_
  filter_upwards [h_eventually_bound] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact ht

/-- On the segment between two points equidistant (distance `d`) from `s`, every point satisfies
`‖z - s‖² ≥ d² - ‖z₁ - z₂‖²/4`. -/
private theorem norm_sq_segment_to_pole_lower_bound {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d ^ 2 - ‖z₁ - z₂‖ ^ 2 / 4 ≤ ‖z - s‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, h_sum, rfl⟩ := hz
  rw [show α • z₁ + β • z₂ - s = α • (z₁ - s) + β • (z₂ - s) by
    rw [show β = 1 - α by linarith]; module]
  have h_expand : ‖α • (z₁ - s) + β • (z₂ - s)‖ ^ 2 =
      α ^ 2 * ‖z₁ - s‖ ^ 2 +
        2 * α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re +
        β ^ 2 * ‖z₂ - s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.real_smul]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal,
      show (((α : ℂ) * (z₁ - s)) * starRingEnd ℂ ((β : ℂ) * (z₂ - s))) =
          ((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s)) by
        rw [map_mul, Complex.conj_ofReal]; push_cast; ring,
      show (((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s))).re =
          α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re by
        rw [Complex.mul_re]; simp]
    ring
  have h_cross : ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re =
      (‖z₁ - s‖ ^ 2 + ‖z₂ - s‖ ^ 2 - ‖z₁ - z₂‖ ^ 2) / 2 := by
    have h_ns := Complex.normSq_sub (z₁ - s) (z₂ - s)
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm,
      show (z₁ - s) - (z₂ - s) = z₁ - z₂ by ring] at h_ns
    linarith
  rw [h_expand, h_cross, h₁, h₂]
  have h_ab_le : α * β ≤ 1 / 4 := by nlinarith [sq_nonneg (α - β)]
  have h_quad : α ^ 2 + 2 * α * β + β ^ 2 = 1 := by nlinarith [h_sum]
  nlinarith [h_quad, h_ab_le, sq_nonneg (‖z₁ - z₂‖)]

/-- When the chord between two points at distance `d` from `s` is at most `d`, their segment
stays at distance `≥ d/2` from `s`. -/
private theorem norm_segment_to_pole_lower_bound_half {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) (h_chord : ‖z₁ - z₂‖ ≤ d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d / 2 ≤ ‖z - s‖ := by
  have h_le_sq : (d / 2) ^ 2 ≤ ‖z - s‖ ^ 2 := by
    nlinarith [norm_sq_segment_to_pole_lower_bound h₁ h₂ hz,
      mul_self_le_mul_self (norm_nonneg _) h_chord]
  exact (abs_le_of_sq_le_sq' h_le_sq (norm_nonneg _)).2

/-- For `w ≠ s` with the chord to the tangent target at most `‖w - s‖`, the antiderivative
difference between `w` and the tangent target `s + (‖w - s‖/‖L‖) • L` is bounded by
`(1/(‖w - s‖/2)^k) · chord`. -/
private theorem norm_antiderivative_diff_at_tangent_target_le {w s L : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hL : L ≠ 0) (hw_ne : w ≠ s) (h_chord_le : ‖w - (s + (‖w - s‖ / ‖L‖ : ℝ) • L)‖ ≤ ‖w - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * (((s + (‖w - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / (‖w - s‖ / 2) ^ k) * ‖w - (s + (‖w - s‖ / ‖L‖ : ℝ) • L)‖ := by
  have hd_pos : 0 < ‖w - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne)
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  set d := ‖w - s‖
  set tgt := s + (d / ‖L‖ : ℝ) • L with htgt_def
  have h_tgt : ‖tgt - s‖ = d := by
    rw [show tgt - s = (d / ‖L‖ : ℝ) • L by simp [htgt_def], norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    field_simp
  have h_F_diff := norm_antiderivative_diff_le_segment_bound (z₁ := w) (z₂ := tgt) (s := s) hk
    (by linarith : 0 < d / 2)
    (fun z hz => norm_segment_to_pole_lower_bound_half rfl h_tgt h_chord_le hz)
  rw [show (-(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) =
      -((-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)) by ring,
    norm_neg, show ‖w - tgt‖ = ‖tgt - w‖ from norm_sub_rev _ _]
  exact h_F_diff

/-- If `chord = o(d^n)`, `d → 0` with `d > 0` eventually, and `k ≤ n`, then `chord/d^k → 0`. -/
private theorem tendsto_div_pow_zero_of_isLittleO {chord d : ℝ → ℝ} {l : Filter ℝ} {n k : ℕ}
    (h_chord : chord =o[l] (fun t => d t ^ n)) (h_d : Tendsto d l (𝓝 0))
    (h_d_pos : ∀ᶠ t in l, 0 < d t) (hkn : k ≤ n) :
    Tendsto (fun t => chord t / d t ^ k) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h_chord.bound (by linarith : 0 < ε / 2),
    h_d.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), h_d_pos] with t hb hd hdp
  have hd_n_pos : 0 < d t ^ n := pow_pos hdp n
  have hd_k_pos : 0 < d t ^ k := pow_pos hdp k
  rw [Real.dist_eq, sub_zero]
  have h_pow : d t ^ n = d t ^ k * d t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hd_n_pos.le] at hb
  rw [abs_div, abs_of_pos hd_k_pos]
  have h_pow_le : d t ^ (n - k) ≤ 1 := pow_le_one₀ hdp.le hd.le
  calc |chord t| / d t ^ k
      ≤ ε / 2 * d t ^ (n - k) := by
        rw [div_le_iff₀ hd_k_pos]
        nlinarith [hb, h_pow]
    _ ≤ ε / 2 * 1 := by gcongr
    _ < ε := by linarith

/-- **The antiderivative difference to the tangent target vanishes (parametrised core).** If the
chord to the `+T` tangent target is `o(‖γ t - s‖ ^ n)` along `l`, `γ → s` off `s` along `l`, and
`2 ≤ k ≤ n`, then `F(γ t) - F(target)` tends to `0` along `l`, for the antiderivative `F` of the
order-`k` pole integrand. -/
theorem antiderivative_diff_at_tangent_target_tendsto_zero
    {γ : ℝ → ℂ} {s : ℂ} {l : Filter ℝ} {T : ℂ} {n k : ℕ} (hT : T ≠ 0) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_chord : (fun t => ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖) =o[l]
      fun t => ‖γ t - s‖ ^ n)
    (h_ne : ∀ᶠ t in l, γ t ≠ s) (h_to : Tendsto γ l (𝓝 s)) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) - s) ^ (k - 1))⁻¹)‖)
      l (𝓝 0) := by
  have h_d_to_zero : Tendsto (fun t => ‖γ t - s‖) l (𝓝 0) := by
    simpa using (h_to.sub_const s).norm
  have h_d_pos : ∀ᶠ t in l, 0 < ‖γ t - s‖ := by
    filter_upwards [h_ne] with t h
    exact norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have h_const_ratio : Tendsto
      (fun t => 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k))
      l (𝓝 0) := by
    simpa using
      (tendsto_div_pow_zero_of_isLittleO h_chord h_d_to_zero h_d_pos hkn).const_mul (2 ^ k : ℝ)
  have h_chord_le_d : ∀ᶠ t in l,
      ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ ≤ ‖γ t - s‖ := by
    filter_upwards [h_chord.bound one_pos,
      h_d_to_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      h_d_pos] with t hb hd hdp
    calc ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖
        ≤ ‖γ t - s‖ ^ n := by simpa using hb
      _ ≤ ‖γ t - s‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hd (by omega : 1 ≤ n)
      _ = ‖γ t - s‖ := pow_one _
  have h_F_diff_le : ∀ᶠ t in l,
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) - s) ^ (k - 1))⁻¹)‖ ≤
      2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k) := by
    filter_upwards [h_ne, h_chord_le_d] with t h_ne hcd
    have hcd' : ‖γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T)‖ ≤ ‖γ t - s‖ := by
      rwa [show γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) =
            γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T by ring]
    have h_bound := norm_antiderivative_diff_at_tangent_target_le hk hT h_ne hcd'
    rw [show ‖γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T)‖ =
          ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ by congr 1; ring] at h_bound
    calc ‖_‖
        ≤ (1 : ℝ) / (‖γ t - s‖ / 2) ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ := h_bound
      _ = 2 ^ k / ‖γ t - s‖ ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ := by
          congr 1; rw [div_pow]; field_simp
      _ = 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_ratio
    (Eventually.of_forall fun _ => norm_nonneg _) h_F_diff_le

/-- **The right-branch antiderivative asymptotics**: with one-sided derivative `L ≠ 0` from the
right at `t₀` and perpendicular deviation `o(‖γ t - s‖ ^ n)` against `L`, the antiderivative
difference between `γ t` and the tangent target on the `+L` ray tends to `0` as `t → t₀⁺`
(`2 ≤ k ≤ n`). -/
theorem antiderivative_diff_at_tangent_target_tendsto_zero_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (hL : L ≠ 0) (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s)
    (h_dev : (fun t => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[>] t₀]
      fun t => ‖γ t - s‖ ^ n)
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] t₀) (𝓝 0) := by
  have h_ne := eventually_ne_of_hasDerivWithinAt self_notMem_Ioi hL h_deriv h_s
  have h_re := eventually_re_mul_conj_nonneg hL h_deriv h_s
    (fun t ht => by rw [abs_of_pos (sub_pos.mpr ht)]) rfl
  exact antiderivative_diff_at_tangent_target_tendsto_zero hL hk hkn
    (chord_to_tangent_isLittleO hL h_re h_ne h_dev) h_ne
    (h_s ▸ h_deriv.continuousWithinAt)

/-- **The left-branch antiderivative asymptotics**: the counterpart of
`antiderivative_diff_at_tangent_target_tendsto_zero_right` from the left, with the tangent
target on the
`-L` ray. -/
theorem antiderivative_diff_at_tangent_target_tendsto_zero_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (hL : L ≠ 0) (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s)
    (h_dev : (fun t => ‖tangentDeviation (γ t - s) L‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - s‖ ^ n)
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[<] t₀) (𝓝 0) := by
  have h_ne := eventually_ne_of_hasDerivWithinAt self_notMem_Iio hL h_deriv h_s
  have h_re := eventually_re_mul_conj_nonneg hL h_deriv h_s
    (fun t ht => by rw [abs_of_neg (sub_neg.mpr ht), neg_smul, smul_neg, neg_neg])
    (norm_neg L)
  have h_dev' : (fun t => ‖tangentDeviation (γ t - s) (-L)‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - s‖ ^ n :=
    h_dev.congr' (Eventually.of_forall fun t => (norm_tangentDeviation_neg hL _).symm)
      EventuallyEq.rfl
  exact antiderivative_diff_at_tangent_target_tendsto_zero (neg_ne_zero.mpr hL) hk hkn
    (chord_to_tangent_isLittleO (neg_ne_zero.mpr hL) h_re h_ne h_dev') h_ne
    (h_s ▸ h_deriv.continuousWithinAt)

end TauCeti.Contour

end
