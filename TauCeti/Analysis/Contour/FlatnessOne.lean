/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Chord.TangentBound

/-!
# Immersions are flat of order one

A piecewise-`C¹` immersion is `FlatOfOrder γ t₀ 1` at every interior parameter, and
`FlatOfOrderBasepoint γ a b 1` across the join: the curve leaves each point first-order tangent
to its non-zero one-sided tangent, so the perpendicular deviation from the tangent line is
`o(‖γ t - γ t₀‖)`. This discharges the flatness clauses of `Contour.ConditionAprime` at simple
poles for immersed cycles — together with `IsPwC1ImmersionOn.finite_crossings` it makes (A′) at
simple poles a theorem about immersions rather than a hypothesis.

## Main results

* `Contour.IsPwC1ImmersionOn.flatOfOrder_one` — an immersion is flat of order `1` at every
  interior parameter.
* `Contour.IsPwC1ImmersionOn.flatOfOrderBasepoint_one` — an immersion is flat of order `1`
  across the basepoint join.

## Provenance

Migrated from `isFlatOfOrder_one` of `FlatnessConditions.lean` in the AINTLIB `LeanModularForms`
development, restated for the raw curve on `[[a, b]]`: the one-sided derivatives recovered there
from tendsto limits are here the within-piece derivatives of `IsPwC1ImmersionOn` at the piece
endpoints. See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
Residue Theorem*, arXiv:1808.00997, §3 (condition (A′) at simple poles).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Asymptotics Filter Set Topology

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- The one-sided first-order tangency computation: if `γ` has one-sided derivative `L ≠ 0` at
`t₀` within a set `s`, then along any filter `l ≤ 𝓝[s] t₀`, the perpendicular
deviation of `γ t` from the tangent line through `γ t₀` in direction `L` is `o(‖γ t - γ t₀‖)`. -/
private theorem perp_isLittleO_of_hasDerivWithinAt {s : Set ℝ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hd : HasDerivWithinAt γ L s t₀) {l : Filter ℝ} (hl : l ≤ 𝓝[s] t₀) :
    (fun t => |((γ t - γ t₀) * star L).im| / ‖L‖) =o[l] (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  have herr : (fun t => γ t - γ t₀ - (t - t₀) • L) =o[l] (fun t => t - t₀) :=
    (hasDerivWithinAt_iff_isLittleO.mp hd).mono hl
  -- the perpendicular part of the linear term vanishes, so perp ≤ ‖error‖
  have hperp_le : ∀ t, |((γ t - γ t₀) * star L).im| / ‖L‖ ≤ ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    intro t
    rw [Complex.star_def, ← norm_tangentDeviation hL]
    exact norm_tangentDeviation_le_norm_sub_smul _ _ _
  -- perp =o (t - t₀)
  have h1 : (fun t => |((γ t - γ t₀) * star L).im| / ‖L‖) =o[l] (fun t => t - t₀) :=
    (isBigO_of_le l fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hperp_le t).trans_isLittleO herr
  -- (t - t₀) =O ‖γ t - γ t₀‖, from the reverse triangle inequality against the error bound
  have h2 : (fun t => t - t₀) =O[l] (fun t => ‖γ t - γ t₀‖) := by
    rw [isBigO_iff]
    refine ⟨2 / ‖L‖, ?_⟩
    have hsmall := (isLittleO_iff.mp herr) (c := ‖L‖ / 2) (by positivity)
    filter_upwards [hsmall] with t ht
    have hpos : (0 : ℝ) < ‖L‖ := norm_pos_iff.mpr hL
    have hb : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ / 2 * |t - t₀| := by
      simpa [Real.norm_eq_abs] using ht
    have hnorm : |t - t₀| * ‖L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖γ t - γ t₀‖ := by
      have htri := norm_sub_norm_le ((t - t₀) • L) ((t - t₀) • L - (γ t - γ t₀))
      rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, norm_sub_rev] at htri
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [hnorm, hb, abs_nonneg (t - t₀)]
  simpa [pow_one] using h1.trans_isBigO h2

/-- The right-piece flatness clause: on a `C¹` piece `[t₀, d]` with non-vanishing within-piece
derivative, the perpendicular deviation from the right tangent at `t₀` is `o(‖γ t - γ t₀‖)` from
the right. -/
private theorem perp_isLittleO_right {t₀ d : ℝ} (hd : t₀ < d)
    (hC1 : ContDiffOn ℝ 1 γ (Icc t₀ d)) (hne : derivWithin γ (Icc t₀ d) t₀ ≠ 0) :
    (fun t => |((γ t - γ t₀) * star (derivWithin γ (Icc t₀ d) t₀)).im| /
      ‖derivWithin γ (Icc t₀ d) t₀‖) =o[𝓝[>] t₀] (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  refine perp_isLittleO_of_hasDerivWithinAt hne
    ((hC1.differentiableOn one_ne_zero) t₀ (left_mem_Icc.mpr hd.le)).hasDerivWithinAt ?_
  rw [← nhdsWithin_Ioo_eq_nhdsGT hd]
  exact nhdsWithin_mono t₀ Ioo_subset_Icc_self

/-- The left-piece flatness clause: on a `C¹` piece `[c, t₀]` with non-vanishing within-piece
derivative, the perpendicular deviation from the left tangent at `t₀` is `o(‖γ t - γ t₀‖)` from
the left. -/
private theorem perp_isLittleO_left {c t₀ : ℝ} (hc : c < t₀)
    (hC1 : ContDiffOn ℝ 1 γ (Icc c t₀)) (hne : derivWithin γ (Icc c t₀) t₀ ≠ 0) :
    (fun t => |((γ t - γ t₀) * star (derivWithin γ (Icc c t₀) t₀)).im| /
      ‖derivWithin γ (Icc c t₀) t₀‖) =o[𝓝[<] t₀] (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  refine perp_isLittleO_of_hasDerivWithinAt hne
    ((hC1.differentiableOn one_ne_zero) t₀ (right_mem_Icc.mpr hc.le)).hasDerivWithinAt ?_
  rw [← nhdsWithin_Ioo_eq_nhdsLT hc]
  exact nhdsWithin_mono t₀ Ioo_subset_Icc_self

/-- **An immersion is flat of order one at every interior parameter** (HW condition (A′) at a
simple pole): the curve is first-order tangent to its non-zero one-sided tangents, so the
perpendicular deviation from each tangent line is `o(‖γ t - γ t₀‖)`. -/
theorem IsPwC1ImmersionOn.flatOfOrder_one (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) : FlatOfOrder γ t₀ 1 := by
  obtain ⟨d, hd, -, hC1d, hned⟩ := h.exists_Icc_piece_right ⟨ht₀.1.le, ht₀.2⟩
  obtain ⟨c, hc, -, hC1c, hnec⟩ := h.exists_Icc_piece_left ⟨ht₀.1, ht₀.2.le⟩
  exact flatOfOrder_iff.mpr ⟨derivWithin γ (Icc t₀ d) t₀, derivWithin γ (Icc c t₀) t₀,
    hned t₀ (left_mem_Icc.mpr hd.le), hnec t₀ (right_mem_Icc.mpr hc.le),
    perp_isLittleO_right hd hC1d (hned t₀ (left_mem_Icc.mpr hd.le)),
    perp_isLittleO_left hc hC1c (hnec t₀ (right_mem_Icc.mpr hc.le))⟩

/-- **An immersion is flat of order one across the basepoint join** (`a < b`): the outgoing
branch at `a` and the incoming branch at `b` are each first-order tangent to their non-zero
one-sided tangents. -/
theorem IsPwC1ImmersionOn.flatOfOrderBasepoint_one (h : IsPwC1ImmersionOn γ a b)
    (hab : a < b) : FlatOfOrderBasepoint γ a b 1 := by
  have hmin : min a b = a := min_eq_left hab.le
  have hmax : max a b = b := max_eq_right hab.le
  obtain ⟨d, hd, -, hC1d, hned⟩ := h.exists_Icc_piece_right
    ⟨hmin.le, lt_of_lt_of_le hab hmax.ge⟩
  obtain ⟨c, hc, -, hC1c, hnec⟩ := h.exists_Icc_piece_left
    ⟨hmin.le.trans_lt hab, hmax.ge⟩
  exact flatOfOrderBasepoint_iff.mpr ⟨derivWithin γ (Icc a d) a, derivWithin γ (Icc c b) b,
    hned a (left_mem_Icc.mpr hd.le), hnec b (right_mem_Icc.mpr hc.le),
    perp_isLittleO_right hd hC1d (hned a (left_mem_Icc.mpr hd.le)),
    perp_isLittleO_left hc hC1c (hnec b (right_mem_Icc.mpr hc.le))⟩

end TauCeti.Contour

end
