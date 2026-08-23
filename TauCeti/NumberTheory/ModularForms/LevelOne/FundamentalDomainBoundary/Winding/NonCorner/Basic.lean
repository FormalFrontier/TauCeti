/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The excised logarithmic telescope for a branch adapted to a crossing point

The engine shared by the non-corner winding computations (`Winding/NonCorner/Vertical.lean`
and `Winding/NonCorner/Arc.lean`): running the excised logarithmic telescope on the branch
`log ((γ t - w) · c)` for a unit `c` that rotates the branch cut into a ray from `w` missing
the rest of the contour. With the cut so aimed, the whole excised contour is slit-plane-valued
for the one branch, the telescope needs no interior crossing corrections, and both pieces
evaluate by the comparison-free logarithmic FTC; closedness of the contour cancels the shared
basepoint, leaving the endpoint-log difference across the excision window.

## Main declarations

* `TauCeti.ModularForm.truncated_integral_spec_of_slit_branch`: over a two-piece excision of
  the parameter range, the truncated winding integrand is interval integrable and its
  integral is the branch-log difference at the excision endpoints.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

open Contour

namespace ModularForm

variable {H t t₀ s δ ε : ℝ} {w c : ℂ}


/-- Off the three parameterization corners the assembled contour is differentiable. -/
private lemma hasDerivAt_fdBoundary_of_ne (h1 : t ≠ 1) (h3 : t ≠ 3) (h4 : t ≠ 4) :
    HasDerivAt (fdBoundary H) (deriv (fdBoundary H) t) t := by
  rcases lt_trichotomy t 1 with h | h | h
  · exact (hasDerivAt_fdBoundary_of_lt_one h).differentiableAt.hasDerivAt
  · exact absurd h h1
  rcases lt_trichotomy t 3 with h' | h' | h'
  · exact (hasDerivAt_fdBoundary_of_mem_Ioo_one_three ⟨h, h'⟩).differentiableAt.hasDerivAt
  · exact absurd h' h3
  rcases lt_trichotomy t 4 with h'' | h'' | h''
  · exact (hasDerivAt_fdBoundary_of_mem_Ioo_three_four ⟨h', h''⟩).differentiableAt.hasDerivAt
  · exact absurd h'' h4
  · exact (hasDerivAt_fdBoundary_of_gt_four h'').differentiableAt.hasDerivAt

/-- **The telescope piece for an adapted branch.** On a corner-tolerant parameter range
along which the shifted-and-rotated contour `(γ t - w) · c` stays in the slit plane, the
logarithmic integrand of the shifted contour is interval integrable, and its integral is the
endpoint difference of the rotated branch `log ((γ t - w) · c)`. -/
private lemma telescope_piece_of_slit_branch {a b : ℝ} (hc : c ≠ 0) (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc (0 : ℝ) 5)
    (hslit : ∀ t ∈ Icc a b, (fdBoundary H t - w) * c ∈ Complex.slitPlane) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w)) volume a b ∧
    ∫ t in a..b, deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w) =
      Complex.log ((fdBoundary H b - w) * c) - Complex.log ((fdBoundary H a - w) * c) := by
  have hne : ∀ t ∈ Icc a b, fdBoundary H t ≠ w := fun t ht heq ↦
    Complex.slitPlane_ne_zero (hslit t ht) (by rw [heq, sub_self, zero_mul])
  have hint : IntervalIntegrable
      (fun t ↦ (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t) volume a b :=
    Contour.intervalIntegrable_inv_sub_mul_deriv (continuous_fdBoundary H).continuousOn
      (fun t ht ↦ hne t (by rwa [uIcc_of_le hab] at ht))
      (((isPiecewiseC1On_fdBoundary H).intervalIntegrable_deriv).mono_set
        (by rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)]; exact hsub))
  have hfun : (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t * c / ((fdBoundary H t - w) * c))
      = fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w) :=
    funext fun t ↦ mul_div_mul_right _ _ hc
  have hfun2 : (fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t / (fdBoundary H t - w))
      = fun t ↦ (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t :=
    funext fun t ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hdiff : ∀ t ∈ Ioo (min a b) (max a b) \ (fdBoundaryCorners : Set ℝ),
      HasDerivAt (fun s ↦ (fdBoundary H s - w) * c)
        (deriv (fun s ↦ fdBoundary H s - w) t * c) t := by
    intro t ht
    have hcor := ht.2
    rw [Finset.mem_coe, mem_fdBoundaryCorners] at hcor
    push Not at hcor
    simpa only [deriv_sub_const] using
      ((hasDerivAt_fdBoundary_of_ne hcor.1 hcor.2.1 hcor.2.2).sub_const w).mul_const c
  have hmain := Contour.integral_deriv_div_eq_log_sub_log
    (f := fun s ↦ (fdBoundary H s - w) * c)
    (f' := fun t ↦ deriv (fun s ↦ fdBoundary H s - w) t * c)
    fdBoundaryCorners.countable_toSet
    ((((continuous_fdBoundary H).sub continuous_const).mul continuous_const).continuousOn)
    hdiff (fun t ht ↦ hslit t (by rwa [uIcc_of_le hab] at ht))
    (by rw [hfun, hfun2]; exact hint)
  rw [hfun] at hmain
  exact ⟨by rw [hfun2]; exact hint, hmain⟩

/-- **The excision collapse for an adapted branch.** If beyond the excised parameter window
the contour keeps distance more than `ε` from `w` while the rotated branch stays in the slit
plane, and within the window it stays within `ε`, then the `ε`-truncated index integrand is
interval integrable over the whole contour and its integral is the window-endpoint log
difference of the rotated branch. -/
lemma truncated_integral_spec_of_slit_branch (hc : c ≠ 0)
    (h0 : 0 ≤ t₀ - δ) (hδ : 0 < δ) (h5 : t₀ + δ ≤ 5)
    (hslit : ∀ t ∈ Icc (0 : ℝ) 5, t ∉ Ioo (t₀ - δ) (t₀ + δ) →
      (fdBoundary H t - w) * c ∈ Complex.slitPlane)
    (hfar_left : ∀ s ∈ Ioo (0 : ℝ) (t₀ - δ), ε < ‖fdBoundary H s - w‖)
    (hfar_right : ∀ s ∈ Ioo (t₀ + δ) (5 : ℝ), ε < ‖fdBoundary H s - w‖)
    (hnear : ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ‖fdBoundary H s - w‖ ≤ ε) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      Complex.log ((fdBoundary H (t₀ - δ) - w) * c) -
        Complex.log ((fdBoundary H (t₀ + δ) - w) * c) := by
  have hab2 : t₀ - δ ≤ t₀ + δ := by linarith
  obtain ⟨hiL, heL⟩ := telescope_piece_of_slit_branch hc h0
    (Icc_subset_Icc le_rfl (by linarith)) (fun t ht ↦ hslit t ⟨ht.1, by linarith [ht.2]⟩
      fun hmem ↦ absurd ht.2 (not_le.mpr hmem.1))
  obtain ⟨hiR, heR⟩ := telescope_piece_of_slit_branch hc h5
    (Icc_subset_Icc (by linarith) le_rfl) (fun t ht ↦ hslit t ⟨by linarith [ht.1], ht.2⟩
      fun hmem ↦ absurd ht.1 (not_le.mpr hmem.2))
  have haeL := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H) (z₀ := w) (ε := ε)
    h0 hfar_left
  have haeR := Contour.ae_logDeriv_sub_eq_truncated (γ := fdBoundary H) (z₀ := w) (ε := ε)
    h5 hfar_right
  obtain ⟨hiM, hM0⟩ :=
    Contour.intervalIntegrable_truncated_and_integral_truncated_eq_zero_of_norm_le
      (γ := fdBoundary H) (z₀ := w)
      (g := fun s ↦ (fdBoundary H s - w)⁻¹ * deriv (fdBoundary H) s)
      (Filter.Eventually.of_forall fun s hs ↦ hnear s
        (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab2] at hs)))
  have hiL' := hiL.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr haeL)
  have hiR' := hiR.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr haeR)
  refine ⟨(hiL'.trans hiM).trans hiR', ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiL'.trans hiM) hiR',
    ← intervalIntegral.integral_add_adjacent_intervals hiL' hiM, hM0, add_zero,
    ← intervalIntegral.integral_congr_ae haeL, ← intervalIntegral.integral_congr_ae haeR,
    heL, heR, fdBoundary_apply_five, fdBoundary_apply_zero]
  ring


end ModularForm

end TauCeti

end
