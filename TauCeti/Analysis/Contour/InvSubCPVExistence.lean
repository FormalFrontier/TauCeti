/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
import TauCeti.Analysis.Calculus.OneSidedDerivLimit
import TauCeti.Analysis.Contour.Chord.QuotientAsymptotics
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.PVAggregation
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.PerWindow.CPV
import TauCeti.Analysis.Contour.PiecewiseC1On

/-!
# Existence of the Cauchy-kernel principal value along an immersed curve

For a piecewise-`C¹` immersed curve `γ` on `[a, b]` whose value-`s` parameters are all
interior, the single-point Cauchy principal value of `t ↦ (γ t - s)⁻¹ * deriv γ t` exists on
`[a, b]` — the integral defining the winding number converges even when the curve passes
through `s`. The immersion makes the crossing set finite; each interior crossing carries a
slit-plane radius (`Contour.exists_crossing_slitPlane_radius`), the radii shrink to a common
window radius (`Contour.exists_common_window_radius`), each window integral converges
(`Contour.perWindow_truncated_integral_tendsto`), and the windows aggregate
(`Contour.cauchyPVExistsAt_of_perWindow_tendsto`).

## Main results

* `Contour.IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub` — the single-point principal value at
  `s` of the Cauchy kernel exists along a piecewise-`C¹` immersion whose crossings of `s` are
  interior to `[a, b]`.

## Provenance

Migrated from the existence content of `hasCauchyPV_inv_sub_multiCrossing_corner` of
`MultiCrossingCPV.lean` in the AINTLIB `LeanModularForms` development (there stated for the
bundled `ClosedPwC1Immersion`, with the per-crossing radii of `exists_per_crossing_radius`).
See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- At an interior parameter, a piecewise-`C¹` immersion has non-zero one-sided tangents:
limits of `deriv γ` that are also one-sided derivatives. -/
private theorem exists_one_sided_tangents {γ : ℝ → ℂ} {a b t₀ : ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b) (ht₀ : t₀ ∈ Ioo a b) :
    ∃ L_R L_L : ℂ, L_R ≠ 0 ∧ L_L ≠ 0 ∧
      Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R) ∧ Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L) ∧
      HasDerivWithinAt γ L_R (Ioi t₀) t₀ ∧ HasDerivWithinAt γ L_L (Iio t₀) t₀ := by
  have hmin : min a b = a := min_eq_left hab.le
  have hmax : max a b = b := max_eq_right hab.le
  obtain ⟨L_R, hL_R, h_tend_R⟩ := h_imm.exists_deriv_right_limit
    (by rw [hmin, hmax]; exact ⟨ht₀.1.le, ht₀.2⟩)
  obtain ⟨L_L, hL_L, h_tend_L⟩ := h_imm.exists_deriv_left_limit
    (by rw [hmin, hmax]; exact ⟨ht₀.1, ht₀.2.le⟩)
  have h_cont : ContinuousAt γ t₀ := h_imm.continuousOn.continuousAt
    (by rw [uIcc_of_le hab.le]; exact Icc_mem_nhds ht₀.1 ht₀.2)
  have h_diff_R := h_imm.isPiecewiseC1On.eventually_differentiableAt_right
    (by rw [hmin, hmax]; exact ht₀)
  have h_diff_L := h_imm.isPiecewiseC1On.eventually_differentiableAt_left
    (by rw [hmin, hmax]; exact ht₀)
  exact ⟨L_R, L_L, hL_R, hL_L, h_tend_R, h_tend_L,
    hasDerivWithinAt_Ioi_of_tendsto_deriv h_cont h_diff_R h_tend_R,
    hasDerivWithinAt_Iio_of_tendsto_deriv h_cont h_diff_L h_tend_L⟩

/-- Around each interior crossing there is a radius `R > 0` such that at every window radius
`ρ ≤ R` whose window lies inside `[a, b]` and contains no other crossing, the truncated window
integral of the Cauchy kernel converges. -/
private theorem exists_radius_perWindow_tendsto {γ : ℝ → ℂ} {a b t₀ : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b) (ht₀ : t₀ ∈ Ioo a b) (h_at : γ t₀ = s) :
    ∃ R > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R → a < t₀ - ρ → t₀ + ρ ≤ b →
      (∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀) →
      ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t₀ - ρ)..(t₀ + ρ),
        if ‖γ u - s‖ > ε then (γ u - s)⁻¹ * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
  obtain ⟨L_R, L_L, hL_R, hL_L, h_tend_R, h_tend_L, h_dR, h_dL⟩ :=
    exists_one_sided_tangents h_imm hab ht₀
  obtain ⟨R, hR_pos, hc_R, hc_L, hc_plus, hc_minus⟩ :=
    exists_crossing_slitPlane_radius h_dR h_dL h_at hL_R hL_L
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  have ht₀' : t₀ ∈ Ioo (min a b) (max a b) := by
    rwa [min_eq_left hab.le, max_eq_right hab.le]
  refine ⟨R, hR_pos, fun ρ hρ_pos hρ_le h_lo h_hi h_unique => ⟨_,
    perWindow_truncated_integral_tendsto hρ_pos h_at
      (h_imm.continuousOn.mono (by
        rw [uIcc_of_le hab.le]
        exact Icc_subset_Icc (by linarith) h_hi))
      h_tend_R h_tend_L
      (h_imm.isPiecewiseC1On.eventually_differentiableAt_right ht₀')
      (h_imm.isPiecewiseC1On.eventually_differentiableAt_left ht₀')
      p.countable_toSet
      (fun t ht => hp t ⟨by
        rw [min_eq_left hab.le, max_eq_right hab.le]
        exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩)
      (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
        rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀ + ρ), uIcc_of_le hab.le]
        exact Icc_subset_Icc (by linarith) h_hi))
      h_unique
      (fun a' b' h1 h2 h3 => hc_R a' b' h1 h2 (h3.trans (by linarith)))
      (fun b' h1 h2 => hc_L (t₀ - ρ) b' (by linarith) h1 h2)
      (hc_plus ρ hρ_pos hρ_le) (hc_minus ρ hρ_pos hρ_le)⟩⟩

/-- **Existence of the Cauchy-kernel principal value along a piecewise-`C¹` immersion**: if
every parameter of `[a, b]` where `γ` meets `s` is interior, the single-point Cauchy principal
value of `t ↦ (γ t - s)⁻¹ * deriv γ t` at `s` exists on `[a, b]`. Endpoint crossings are
excluded by `h_interior`; for a closed curve this is the choice of a basepoint off `s`. -/
theorem IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b) :
    CauchyPVExistsAt γ a b (fun z => (z - s)⁻¹) s := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · exact CauchyPVExistsAt.of_eq γ rfl _ s
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq => hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht =>
    h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab.le).ge
  have h_int_tr : ∀ ε : ℝ, 0 < ε → IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b :=
    fun _ hε => intervalIntegrable_inv_sub_truncated h_imm.continuousOn
      h_imm.isPiecewiseC1On.intervalIntegrable_deriv hε
  rcases T.eq_empty_or_nonempty with hT_empty | -
  · refine cauchyPVExistsAt_of_perWindow_tendsto one_pos hab.le T ?_ ?_ ?_ h_int_tr ?_
      (exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => 1)
        fun t _ => one_pos)
    all_goals simp [hT_empty]
  · choose! R hR_pos h_spec using fun t₀ (ht₀ : t₀ ∈ T) =>
      exists_radius_perWindow_tendsto h_imm hab (h_Ioo t₀ ht₀) (hT_mem.mp ht₀).2
    -- one radius serving every crossing at once, below each per-crossing radius `R t`
    obtain ⟨ρ, hρ_pos, h_endpts, h_pair, hρ_le_R⟩ :=
      exists_common_window_radius_le h_Ioo R hR_pos
    refine cauchyPVExistsAt_of_perWindow_tendsto hρ_pos hab.le T
      (fun t ht => by linarith [(h_endpts t ht).1])
      (fun t ht => by linarith [(h_endpts t ht).2])
      h_pair
      h_int_tr
      (fun t₀ ht₀ => h_spec t₀ ht₀ ρ hρ_pos (hρ_le_R t₀ ht₀)
        (by linarith [(h_endpts t₀ ht₀).1]) (by linarith [(h_endpts t₀ ht₀).2])
        fun t ht h_eq => eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀)
          (h_pair t₀ ht₀) h_complete ht h_eq)
      (exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => ρ)
        fun t _ => hρ_pos)

end TauCeti.Contour

end
