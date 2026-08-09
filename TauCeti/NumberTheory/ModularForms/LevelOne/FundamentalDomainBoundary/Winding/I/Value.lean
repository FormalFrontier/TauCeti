/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.I.Geometry

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Complex.LogBranch
import TauCeti.Analysis.Contour.LogDerivFTC
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The winding number of the boundary contour at `i`

The generalized winding number of the truncated-fundamental-domain boundary about the
elliptic point `i` is `-1/2`. Over the `δ`-excised parameter ranges the logarithmic
integral of the shifted contour `t ↦ fdBoundary H t - i` telescopes piece by piece through
the boundary-tolerant logarithmic fundamental theorem — the branch crossing on the left
vertical contributing `-2πi` — and the `ε`-excision of the principal value collapses to
those ranges at the chord-matched half-width `δ(ε) = 12/π·arcsin(ε/2)`. The endpoint
distances are then exactly `ε`, the log-norm parts cancel, and only the straight-angle
defect `π` survives the limit.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_I` (the principal value `-πi`).
* `TauCeti.ModularForm.windingNumber_fdBoundary_I` (the winding number `-1/2`).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`) this file ports onto the
  current Mathlib pin.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

namespace ModularForm


variable {H δ : ℝ}

/-- The corner row lies strictly below `1`. -/
private lemma sqrt_three_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  nlinarith [Real.sq_sqrt (by positivity : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]

/-- The ordered slit-plane comparison step of the telescope: the canonical logarithmic FTC
`TauCeti.Contour.integral_deriv_div_eq_log_sub_log` applied to the comparison function, its
integrability from the continuous derivative, both transported to the contour across the
interior agreement. -/
private lemma slit_comparison {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : Set.EqOn g h (Ioo a b)) (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t ↦ deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hu : uIcc a b = Icc a b := uIcc_of_le hab
  have hne : ∀ t ∈ Icc a b, h t ≠ 0 := fun t ht ↦ Complex.slitPlane_ne_zero (hh_slit t ht)
  have heq' : Set.EqOn (fun t ↦ deriv g t / g t) (fun t ↦ deriv h t / h t) (uIoo a b) := by
    intro t ht
    rw [uIoo_of_le hab] at ht
    simp only [heq ht, heq.deriv isOpen_Ioo ht]
  have hint : IntervalIntegrable (fun t ↦ deriv h t / h t) volume a b :=
    ((hh_deriv_cont.div hh_cont hne).mono (hu ▸ Set.Subset.rfl)).intervalIntegrable
  refine ⟨hint.congr_uIoo fun t ht ↦ (heq' ht).symm, ?_⟩
  calc ∫ t in a..b, deriv g t / g t
      = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_uIoo heq'
    _ = Complex.log (h b) - Complex.log (h a) :=
        Contour.integral_deriv_div_eq_log_sub_log countable_empty (hu ▸ hh_cont)
          (fun t ht ↦ (hh_diff t (by
            rw [min_eq_left hab, max_eq_right hab] at ht
            exact ht.1)).hasDerivAt)
          (fun t ht ↦ hh_slit t (hu ▸ ht)) hint
    _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]

/-- The right-vertical piece `[0, 1]` of the telescope: the shifted contour stays in the
right half-plane, so the logarithmic integral is a difference of principal logarithms. -/
private lemma telescope_piece_right_vertical (H : ℝ) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 0 1 ∧
    ∫ t in (0 : ℝ)..1,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 1 - Complex.I) - Complex.log (fdBoundary H 0 - Complex.I) := by
  have heval : ∀ s ∈ Icc (0 : ℝ) 1, fdBoundary H s = fdBoundary_segment1 H s := fun s hs ↦
    fdBoundary_of_le_one hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment1 H s - Complex.I) =
      fun _ ↦ (UpperHalfPlane.ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment1]
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment1 H s - Complex.I) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment1 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment1 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_lt_two H ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 0 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - Complex.I) (heval 1 (right_mem_Icc.mpr (by norm_num))))

/-- The left arc piece `[1, 2-δ]` of the telescope: right of the top of the arc the
shifted contour stays in the slit plane. -/
private lemma telescope_piece_arc_left (H : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 1 (2 - δ) ∧
    ∫ t in (1 : ℝ)..(2 - δ),
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H (2 - δ) - Complex.I) -
        Complex.log (fdBoundary H 1 - Complex.I) := by
  have hab : (1 : ℝ) ≤ 2 - δ := by linarith
  have heval : ∀ s ∈ Icc (1 : ℝ) (2 - δ), fdBoundary H s = fdBoundary_segment2 s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · rw [← h1, fdBoundary_apply_one, fdBoundary_segment2_apply_one]
    · exact fdBoundary_of_le_two h1 (by linarith [hs.2])
  have hd : deriv (fun s ↦ fdBoundary_segment2 s - Complex.I) = fun s ↦
      (Real.pi / 2 - Real.pi / 3) •
        (circleMap 0 1 (Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment2]
  have hθc : Continuous fun s : ℝ ↦ Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment2 s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment2 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment2 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (Real.pi / 2 - Real.pi / 3)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_lt_two H ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 1 (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval (2 - δ) (right_mem_Icc.mpr hab)))

/-- The right arc piece `[2+δ, 3]` of the telescope: left of the top of the arc the
shifted contour stays in the slit plane. -/
private lemma telescope_piece_arc_right (H : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (2 + δ) 3 ∧
    ∫ t in (2 + δ : ℝ)..3,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 3 - Complex.I) -
        Complex.log (fdBoundary H (2 + δ) - Complex.I) := by
  have hab : (2 + δ : ℝ) ≤ 3 := by linarith
  have heval : ∀ s ∈ Icc (2 + δ : ℝ) 3, fdBoundary H s = fdBoundary_segment3 s := fun s hs ↦
    fdBoundary_of_le_three (by linarith [hs.1]) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment3 s - Complex.I) = fun s ↦
      (2 * Real.pi / 3 - Real.pi / 2) •
        (circleMap 0 1 (Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) *
          Complex.I) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment3]
  have hθc : Continuous fun s : ℝ ↦
      Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
    fun_prop
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment3 s - Complex.I) hab
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment3 s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment3 t).differentiableAt.sub_const _)
    (by
      rw [hd]
      exact (Continuous.const_smul
        (((continuous_circleMap 0 1).comp hθc).mul continuous_const)
        (2 * Real.pi / 3 - Real.pi / 2)).continuousOn)
    (fun t ht ↦ heval t ht ▸
      fdBoundary_sub_I_mem_slitPlane_of_two_lt H (by linarith [ht.1]) ht.2)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval (2 + δ) (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval 3 (right_mem_Icc.mpr hab)))

/-- The lower left-vertical piece `[3, t₀]` of the telescope, up to the height-`1`
crossing: the shifted contour stays in the closed lower half-plane, so the logarithmic
integral evaluates against the negated arguments. -/
private lemma telescope_piece_left_lower (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 3 (leftVerticalCrossingI H) ∧
    ∫ t in (3 : ℝ)..leftVerticalCrossingI H,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (-(fdBoundary H (leftVerticalCrossingI H) - Complex.I)) -
        Complex.log (-(fdBoundary H 3 - Complex.I)) := by
  have hHs : Real.sqrt 3 / 2 < H := by linarith [sqrt_three_div_two_lt_one]
  have hab : (3 : ℝ) ≤ leftVerticalCrossingI H := (three_lt_leftVerticalCrossingI hHs).le
  have hsub : Icc (3 : ℝ) (leftVerticalCrossingI H) ⊆ Icc (3 : ℝ) 4 :=
    Icc_subset_Icc le_rfl (leftVerticalCrossingI_lt_four hH).le
  have heval : ∀ s ∈ Icc (3 : ℝ) (leftVerticalCrossingI H),
      fdBoundary H s = fdBoundary_segment4 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three, fdBoundary_segment4_apply_three]
    · exact fdBoundary_of_le_four h3 (hsub hs).2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have hne : ∀ t ∈ Icc (3 : ℝ) (leftVerticalCrossingI H),
      fdBoundary H t - Complex.I ≠ 0 := by
    intro t ht h0
    have hre := re_fdBoundary_segment4 H (hsub ht)
    rw [sub_eq_zero] at h0
    rw [h0, Complex.I_re] at hre
    norm_num at hre
  have hu : uIcc (3 : ℝ) (leftVerticalCrossingI H) = Icc 3 (leftVerticalCrossingI H) :=
    uIcc_of_le hab
  have ho : Ioo (min (3 : ℝ) (leftVerticalCrossingI H)) (max 3 (leftVerticalCrossingI H))
      = Ioo 3 (leftVerticalCrossingI H) := by rw [min_eq_left hab, max_eq_right hab]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment4 H s - Complex.I)
      (Icc (3 : ℝ) (leftVerticalCrossingI H)) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (3 : ℝ) (leftVerticalCrossingI H),
      fdBoundary_segment4 H t - Complex.I ≠ 0 := fun t ht ↦ heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) t /
        (fdBoundary_segment4 H t - Complex.I)) volume 3 (leftVerticalCrossingI H) :=
    ((((by rw [hd]; exact continuousOn_const :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment4 H s - Complex.I)
          (Icc (3 : ℝ) (leftVerticalCrossingI H)))).div hcont hne').mono
      (hu ▸ Set.Subset.rfl)).intervalIntegrable
  refine
    Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_neg_sub_log_neg_of_im_nonpos
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment4 H s - Complex.I) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ ?_)
    (heval 3 (left_mem_Icc.mpr hab) ▸ hne 3 (left_mem_Icc.mpr hab))
    (heval _ (right_mem_Icc.mpr hab) ▸ hne _ (right_mem_Icc.mpr hab))
    (fun t ht ↦ ?_)
    (fun t ht ↦ congrArg (· - Complex.I)
      (heval t ⟨(ho ▸ ht).1.le, (ho ▸ ht).2.le⟩))
    (congrArg (· - Complex.I) (heval 3 (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval _ (right_mem_Icc.mpr hab)))
  · -- The comparison hypothesis is stated for the abstract `h` of the comparison FTC, so the
    -- goal arrives as that function applied at `t`; naming the beta-reduced form is what lets
    -- the segment lemmas below apply to it.
    show (fdBoundary_segment4 H t - Complex.I).im ≤ 0
    rw [hu] at ht
    rw [← heval t ht]
    rcases eq_or_lt_of_le ht.1 with h3 | h3
    · rw [← h3]
      exact (im_fdBoundary_sub_I_at_three_neg H).le
    · rcases eq_or_lt_of_le ht.2 with ht0 | ht0
      · rw [ht0]
        exact (im_fdBoundary_sub_I_leftVerticalCrossingI hH.le).le
      · exact (im_fdBoundary_sub_I_neg_of_lt_crossing hH h3 ht0).le
  · -- Likewise for the negated slit-plane hypothesis of the lower comparison form.
    show -(fdBoundary_segment4 H t - Complex.I) ∈ Complex.slitPlane
    rw [ho] at ht
    rw [← heval t ⟨ht.1.le, ht.2.le⟩]
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    have := im_fdBoundary_sub_I_neg_of_lt_crossing hH ht.1 ht.2
    simpa using ne_of_gt (by linarith : 0 < -(fdBoundary H t - Complex.I).im)

/-- The upper left-vertical piece `[t₀, 4]` of the telescope, above the height-`1`
crossing: the shifted contour stays in the closed upper half-plane. -/
private lemma telescope_piece_left_upper (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (leftVerticalCrossingI H) 4 ∧
    ∫ t in (leftVerticalCrossingI H : ℝ)..4,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 4 - Complex.I) -
        Complex.log (fdBoundary H (leftVerticalCrossingI H) - Complex.I) := by
  have hHs : Real.sqrt 3 / 2 < H := by linarith [sqrt_three_div_two_lt_one]
  have hab : leftVerticalCrossingI H ≤ (4 : ℝ) := (leftVerticalCrossingI_lt_four hH).le
  have hsub : Icc (leftVerticalCrossingI H) (4 : ℝ) ⊆ Icc (3 : ℝ) 4 :=
    Icc_subset_Icc (three_lt_leftVerticalCrossingI hHs).le le_rfl
  have heval : ∀ s ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      fdBoundary H s = fdBoundary_segment4 H s := fun s hs ↦
    fdBoundary_of_le_four (lt_of_lt_of_le (three_lt_leftVerticalCrossingI hHs) hs.1) hs.2
  have hd : deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) =
      fun _ ↦ -1 / 2 + H * Complex.I - (UpperHalfPlane.ρ : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment4]
  have hne : ∀ t ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      fdBoundary H t - Complex.I ≠ 0 := by
    intro t ht h0
    have hre := re_fdBoundary_segment4 H (hsub ht)
    rw [sub_eq_zero] at h0
    rw [h0, Complex.I_re] at hre
    norm_num at hre
  have him : ∀ t ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      0 ≤ (fdBoundary H t - Complex.I).im := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← ht0]
      exact (im_fdBoundary_sub_I_leftVerticalCrossingI hH.le).ge
    · exact (im_fdBoundary_sub_I_pos_of_crossing_lt hH ht0 ht.2).le
  have hu : uIcc (leftVerticalCrossingI H) (4 : ℝ) = Icc (leftVerticalCrossingI H) 4 :=
    uIcc_of_le hab
  have ho : Ioo (min (leftVerticalCrossingI H) (4 : ℝ)) (max (leftVerticalCrossingI H) 4)
      = Ioo (leftVerticalCrossingI H) 4 := by rw [min_eq_left hab, max_eq_right hab]
  have hcont : ContinuousOn (fun s ↦ fdBoundary_segment4 H s - Complex.I)
      (Icc (leftVerticalCrossingI H) (4 : ℝ)) :=
    Continuous.continuousOn (Differentiable.continuous fun s ↦
      (hasDerivAt_fdBoundary_segment4 H s).differentiableAt.sub_const _)
  have hne' : ∀ t ∈ Icc (leftVerticalCrossingI H) (4 : ℝ),
      fdBoundary_segment4 H t - Complex.I ≠ 0 := fun t ht ↦ heval t ht ▸ hne t ht
  have hint : IntervalIntegrable (fun t ↦
      deriv (fun s ↦ fdBoundary_segment4 H s - Complex.I) t /
        (fdBoundary_segment4 H t - Complex.I)) volume (leftVerticalCrossingI H) 4 :=
    ((((by rw [hd]; exact continuousOn_const :
        ContinuousOn (deriv fun s ↦ fdBoundary_segment4 H s - Complex.I)
          (Icc (leftVerticalCrossingI H) (4 : ℝ)))).div hcont hne').mono
      (hu ▸ Set.Subset.rfl)).intervalIntegrable
  refine Contour.intervalIntegrable_deriv_div_and_integral_deriv_div_eq_log_sub_log_of_im_nonneg
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment4 H s - Complex.I) countable_empty
    (hu ▸ hcont)
    (fun t ht ↦ (hasDerivAt_fdBoundary_segment4 H t).differentiableAt.sub_const _)
    hint
    (fun t ht ↦ heval t (hu ▸ ht) ▸ him t (hu ▸ ht))
    (heval _ (left_mem_Icc.mpr hab) ▸ hne _ (left_mem_Icc.mpr hab))
    (heval 4 (right_mem_Icc.mpr hab) ▸ hne 4 (right_mem_Icc.mpr hab))
    (fun t ht ↦ ?_)
    (fun t ht ↦ congrArg (· - Complex.I)
      (heval t ⟨(ho ▸ ht).1.le, (ho ▸ ht).2.le⟩))
    (congrArg (· - Complex.I) (heval _ (left_mem_Icc.mpr hab)))
    (congrArg (· - Complex.I) (heval 4 (right_mem_Icc.mpr hab)))
  rw [ho] at ht
  have hpos := im_fdBoundary_sub_I_pos_of_crossing_lt hH ht.1 ht.2.le
  rw [heval t ⟨ht.1.le, ht.2.le⟩] at hpos
  exact Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hpos))

/-- The ceiling piece `[4, 5]` of the telescope: the shifted contour stays at height
`H - 1 > 0`, inside the slit plane. -/
private lemma telescope_piece_ceiling (hH : 1 < H) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 4 5 ∧
    ∫ t in (4 : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I) =
      Complex.log (fdBoundary H 5 - Complex.I) - Complex.log (fdBoundary H 4 - Complex.I) := by
  have heval : ∀ s ∈ Icc (4 : ℝ) 5, fdBoundary H s = fdBoundary_segment5 H s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h4 | h4
    · rw [← h4, fdBoundary_apply_four, fdBoundary_segment5_apply_four]
    · exact fdBoundary_of_gt_four h4
  have hd : deriv (fun s ↦ fdBoundary_segment5 H s - Complex.I) = fun _ ↦ (1 : ℂ) :=
    funext fun s ↦ by rw [deriv_sub_const, deriv_fdBoundary_segment5]
  have hslit : ∀ t ∈ Icc (4 : ℝ) 5, fdBoundary H t - Complex.I ∈ Complex.slitPlane := by
    intro t ht
    refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
    rw [Complex.sub_im, Complex.I_im, im_fdBoundary_segment5 H ht]
    linarith
  exact slit_comparison
    (g := fun s ↦ fdBoundary H s - Complex.I)
    (h := fun s ↦ fdBoundary_segment5 H s - Complex.I) (by norm_num)
    (Continuous.continuousOn (Differentiable.continuous fun s ↦
      ((hasDerivAt_fdBoundary_segment5 H s).differentiableAt.sub_const _)))
    (fun t _ ↦ (hasDerivAt_fdBoundary_segment5 H t).differentiableAt.sub_const _)
    (by rw [hd]; exact continuousOn_const)
    (fun t ht ↦ heval t ht ▸ hslit t ht)
    (fun t ht ↦ congrArg (· - Complex.I) (heval t ⟨ht.1.le, ht.2.le⟩))
    (congrArg (· - Complex.I) (heval 4 (left_mem_Icc.mpr (by norm_num))))
    (congrArg (· - Complex.I) (heval 5 (right_mem_Icc.mpr (by norm_num))))

/-- For a point on the open negative real axis, the logarithm of the negation loses
`π·i`. -/
private lemma log_neg_eq_log_sub_pi_mul_I {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
    Complex.log (-z) = Complex.log z - Real.pi * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re]
  · rw [Complex.log_im, Complex.sub_im, Complex.log_im,
      Complex.arg_eq_pi_iff.mpr ⟨hre, him⟩,
      Complex.arg_eq_zero_iff.mpr ⟨by simpa using hre.le, by simpa using him⟩]
    simp

/-- **The logarithmic telescope at `i`**: over the `δ`-excluded ranges the logarithmic
integral of the shifted contour is integrable and evaluates to the endpoint logarithms
minus the branch crossing `2πi`. -/
private theorem ftc_logDeriv_telescope_I (H : ℝ) (hH : 1 < H) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume 0 (2 - δ) ∧
    IntervalIntegrable
      (fun t ↦ deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I))
      volume (2 + δ) 5 ∧
    (∫ t in (0 : ℝ)..(2 - δ),
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I)) +
      (∫ t in (2 + δ : ℝ)..5,
        deriv (fun s ↦ fdBoundary H s - Complex.I) t / (fdBoundary H t - Complex.I)) =
      Complex.log (fdBoundary H (2 - δ) - Complex.I) -
        Complex.log (fdBoundary H (2 + δ) - Complex.I) - 2 * Real.pi * Complex.I := by
  obtain ⟨hi01, he01⟩ := telescope_piece_right_vertical H
  obtain ⟨hi12, he12⟩ := telescope_piece_arc_left H hδ hδ1
  obtain ⟨hi23, he23⟩ := telescope_piece_arc_right H hδ hδ1
  obtain ⟨hi3c, he3c⟩ := telescope_piece_left_lower hH
  obtain ⟨hic4, hec4⟩ := telescope_piece_left_upper hH
  obtain ⟨hi45, he45⟩ := telescope_piece_ceiling hH
  have hint34 := hi3c.trans hic4
  have hint35 := hint34.trans hi45
  refine ⟨hi01.trans hi12, hi23.trans hint35, ?_⟩
  have hlog3 : Complex.log (-(fdBoundary H 3 - Complex.I)) =
      Complex.log (fdBoundary H 3 - Complex.I) + Real.pi * Complex.I :=
    log_neg_eq_log_add_pi_mul_I_of_im_neg (im_fdBoundary_sub_I_at_three_neg H)
  have hlogt0 : Complex.log (-(fdBoundary H (leftVerticalCrossingI H) - Complex.I)) =
      Complex.log (fdBoundary H (leftVerticalCrossingI H) - Complex.I) -
        Real.pi * Complex.I := by
    refine log_neg_eq_log_sub_pi_mul_I ?_ (im_fdBoundary_sub_I_leftVerticalCrossingI hH.le)
    rw [Complex.sub_re, Complex.I_re, re_fdBoundary_segment4 H
      ⟨(three_lt_leftVerticalCrossingI (by linarith [sqrt_three_div_two_lt_one])).le,
        (leftVerticalCrossingI_lt_four hH).le⟩]
    norm_num
  have hlog50 : Complex.log (fdBoundary H 5 - Complex.I) =
      Complex.log (fdBoundary H 0 - Complex.I) := by
    rw [fdBoundary_apply_five, fdBoundary_apply_zero]
  rw [← intervalIntegral.integral_add_adjacent_intervals hi01 hi12,
    ← intervalIntegral.integral_add_adjacent_intervals hi23 hint35,
    ← intervalIntegral.integral_add_adjacent_intervals hint34 hi45,
    ← intervalIntegral.integral_add_adjacent_intervals hi3c hic4,
    he01, he12, he23, he3c, hec4, he45, hlog3, hlogt0, hlog50]
  ring


variable {H ε δ t : ℝ}

/-- The sine of a sub-half-turn multiple of `π/12` factors through the absolute value. -/
private lemma abs_sin_mul_pi_div_twelve {u : ℝ} (hu : |u| ≤ 1) :
    |Real.sin (u * (Real.pi / 12))| = Real.sin (|u| * (Real.pi / 12)) := by
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, abs_nonneg u]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]

/-- Far from the arc top, the chord distance strictly exceeds the excision chord. -/
private lemma lt_norm_fdBoundary_sub_I_arc_of_far (harc : t ∈ Icc (1 : ℝ) 3) (hd : 0 < δ)
    (hd1 : δ < 1) (hfar : δ < |t - 2|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - Complex.I‖ := by
  have habs1 : |t - 2| ≤ 1 := abs_le.mpr ⟨by linarith [harc.1], by linarith [harc.2]⟩
  rw [norm_fdBoundary_sub_I_arc H harc, abs_sin_mul_pi_div_twelve habs1]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - 2| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 2)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the arc top, the chord distance is at most the excision chord. -/
private lemma norm_fdBoundary_sub_I_arc_le_of_near (harc : t ∈ Icc (1 : ℝ) 3) (hd1 : δ < 1)
    (hnear : |t - 2| ≤ δ) :
    ‖fdBoundary H t - Complex.I‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have habs1 : |t - 2| ≤ 1 := hnear.trans hd1.le
  have hd0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_I_arc H harc, abs_sin_mul_pi_div_twelve habs1]
  have hmono : Real.sin (|t - 2| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin.monotoneOn
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - 2)], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- Left of the excised arc top, the contour keeps distance more than `ε` from `i`. -/
private lemma lt_norm_of_far_left (hε₁ : ε < 1 / 2) (hd : 0 < δ) (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Ico (0 : ℝ) (2 - δ)) :
    ε < ‖fdBoundary H t - Complex.I‖ := by
  rcases le_or_gt t 1 with ht1 | ht1
  · calc ε < 1 / 2 := hε₁
      _ ≤ ‖fdBoundary H t - Complex.I‖ := norm_fdBoundary_sub_I_segment1 H ⟨ht.1, ht1⟩
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_I_arc_of_far ⟨ht1.le, by linarith [ht.2]⟩ hd hd1 ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [ht.2] : (0 : ℝ) < 2 - t)]
    linarith [ht.2]

/-- Right of the excised arc top, the contour keeps distance more than `ε` from `i`. -/
private lemma lt_norm_of_far_right (hε₁ : ε < 1 / 2) (hε₂ : ε < H - 1)
    (hd : 0 < δ) (hd1 : δ < 1) (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε)
    (ht : t ∈ Ioc (2 + δ : ℝ) 5) :
    ε < ‖fdBoundary H t - Complex.I‖ := by
  rcases le_or_gt t 3 with ht3 | ht3
  · rw [← h2sin]
    refine lt_norm_fdBoundary_sub_I_arc_of_far ⟨by linarith [ht.1], ht3⟩ hd hd1 ?_
    rw [abs_of_pos (by linarith [ht.1] : (0 : ℝ) < t - 2)]
    linarith [ht.1]
  · rcases le_or_gt t 4 with ht4 | ht4
    · calc ε < 1 / 2 := hε₁
        _ ≤ ‖fdBoundary H t - Complex.I‖ := norm_fdBoundary_sub_I_segment4 H ⟨ht3.le, ht4⟩
    · calc ε < H - 1 := hε₂
        _ ≤ |H - 1| := le_abs_self _
        _ ≤ ‖fdBoundary H t - Complex.I‖ :=
          norm_fdBoundary_sub_I_segment5 H ⟨ht4.le, ht.2⟩

/-- Over the excised arc top, the contour stays within distance `ε` of `i`. -/
private lemma norm_le_of_near (hd1 : δ < 1)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (ht : t ∈ Icc (2 - δ : ℝ) (2 + δ)) :
    ‖fdBoundary H t - Complex.I‖ ≤ ε := by
  rw [← h2sin]
  refine norm_fdBoundary_sub_I_arc_le_of_near
    ⟨by linarith [ht.1], by linarith [ht.2]⟩ hd1 (abs_le.mpr ⟨?_, ?_⟩)
  · linarith [ht.1]
  · linarith [ht.2]

/-- The excision half-width `δ(ε) = 12/π · arcsin(ε/2)` is positive, below `1`, and
turns the chord identity into the exact excision radius `ε`. -/
private lemma delta_spec (hε : 0 < ε) (hε₁ : ε < 1 / 2)
    (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    0 < 12 / Real.pi * Real.arcsin (ε / 2) ∧ 12 / Real.pi * Real.arcsin (ε / 2) < 1 ∧
      2 * Real.sin (12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have harc_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr (by linarith)
  have harc_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
    have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
      Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
    rwa [Real.arcsin_sin (by linarith) (by linarith)] at h1
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_lt_one hπ]
    linarith
  · have hδπ : 12 / Real.pi * Real.arcsin (ε / 2) * (Real.pi / 12) = Real.arcsin (ε / 2) := by
      field_simp
    rw [hδπ, Real.sin_arcsin (by linarith) (by linarith)]
    ring

/-- **The excision collapse**: for small `ε`, the `ε`-excised index integrand of the
boundary contour about `i` is interval integrable, and its integral is exactly
`-πi - 2·arcsin(ε/2)·i` — the telescope value at the matched half-width `δ(ε)`. -/
private lemma truncated_integral_spec (hH : 1 < H) (hε : 0 < ε) (hε₁ : ε < 1 / 2)
    (hε₂ : ε < H - 1) (hε₃ : ε < 2 * Real.sin (Real.pi / 12)) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - Complex.I‖
        then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0)
      volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - Complex.I‖
        then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδ_pos, hδ_lt, h2sin⟩ := delta_spec hε hε₁ hε₃
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  obtain ⟨hi_left, hi_right, hval⟩ := ftc_logDeriv_telescope_I H hH hδ_pos hδ_lt
  have hconv : ∀ s : ℝ, (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s =
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) :=
    fun s ↦ by rw [deriv_sub_const, inv_mul_eq_div]
  have hae_left : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) (2 - δ) →
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) =
        (if ε < ‖fdBoundary H s - Complex.I‖
          then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) := by
    have hb_ae : ({2 - δ} : Set ℝ)ᶜ ∈ ae volume := by
      simp [MeasureTheory.mem_ae_iff]
    filter_upwards [hb_ae] with s hs_ne hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hsIco : s ∈ Ico (0 : ℝ) (2 - δ) := ⟨hmem.1.le,
      lt_of_le_of_ne hmem.2 fun h ↦ hs_ne (mem_singleton_iff.mpr h)⟩
    rw [if_pos (lt_norm_of_far_left hε₁ hδ_pos hδ_lt h2sin hsIco), hconv s]
  have hae_right : ∀ᵐ s ∂volume, s ∈ uIoc (2 + δ : ℝ) 5 →
      deriv (fun r ↦ fdBoundary H r - Complex.I) s / (fdBoundary H s - Complex.I) =
        (if ε < ‖fdBoundary H s - Complex.I‖
          then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) := by
    refine Eventually.of_forall fun s hmem ↦ ?_
    rw [uIoc_of_le (by linarith)] at hmem
    rw [if_pos (lt_norm_of_far_right hε₁ hε₂ hδ_pos hδ_lt h2sin hmem), hconv s]
  have hmid : EqOn (fun s ↦ if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0)
      (fun _ ↦ (0 : ℂ)) (uIcc (2 - δ : ℝ) (2 + δ)) := by
    intro s hs
    rw [uIcc_of_le (by linarith)] at hs
    exact if_neg (not_lt.mpr (norm_le_of_near hδ_lt h2sin hs))
  have hi02 := hi_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_left)
  have hi25 := hi_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr hae_right)
  have himid : IntervalIntegrable (fun s ↦ if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0)
      volume (2 - δ) (2 + δ) := by
    refine (intervalIntegrable_const (c := (0 : ℂ))).congr_ae
      ((ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun s hs ↦ ?_))
    rw [uIoc_of_le (by linarith)] at hs
    have hsub : s ∈ uIcc (2 - δ : ℝ) (2 + δ) := by
      rw [uIcc_of_le (by linarith : (2 - δ : ℝ) ≤ 2 + δ)]
      exact Ioc_subset_Icc_self hs
    exact (hmid hsub).symm
  refine ⟨(hi02.trans himid).trans hi25, ?_⟩
  have hδ6 : δ * (Real.pi / 6) = 2 * Real.arcsin (ε / 2) := by
    rw [hδ_def]
    field_simp
    ring
  have hmid0 : ∫ s in (2 - δ : ℝ)..(2 + δ), (if ε < ‖fdBoundary H s - Complex.I‖
      then (fdBoundary H s - Complex.I)⁻¹ * deriv (fdBoundary H) s else 0) = 0 := by
    rw [intervalIntegral.integral_congr hmid]
    simp
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi02.trans himid) hi25,
    ← intervalIntegral.integral_add_adjacent_intervals hi02 himid,
    hmid0, add_zero,
    ← intervalIntegral.integral_congr_ae hae_left,
    ← intervalIntegral.integral_congr_ae hae_right,
    hval, log_fdBoundary_two_sub_sub_I_sub_log_fdBoundary_two_add_sub_I H hδ_pos hδ_lt.le, hδ6.symm]
  push_cast
  ring

/-- **The principal value at `i`**: the Cauchy principal value of the index integrand of
the boundary contour about the elliptic point `i` is `-πi` — half a full turn, as the
contour passes straight through `i` along the arc. -/
theorem hasCauchyPVAt_fdBoundary_I (hH : 1 < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - Complex.I)⁻¹) Complex.I
      (-(Real.pi : ℂ) * Complex.I) := by
  have hsin12 : 0 < 2 * Real.sin (Real.pi / 12) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := Real.pi / 12) (by positivity)
      (by linarith [Real.pi_pos])
    linarith
  have hε₀ : 0 < min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12)) :=
    lt_min (lt_min (by norm_num) (by linarith)) hsin12
  have hIoo : Ioo (0 : ℝ) (min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12))) ∈
      𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min (1 / 2) (H - 1)) (2 * Real.sin (Real.pi / 12))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - Complex.I‖
          then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0)
        volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - Complex.I‖
          then (fdBoundary H t - Complex.I)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec hH hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le (min_le_right _ _))
  have hcont : Tendsto (fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
      ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
    have hc : Continuous fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
        ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
      refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
      exact continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const 2))
    simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ hcont
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at `i` is `-1/2`**: the elliptic point
`i` sits on the contour, and the principal-value normalization sees exactly half a
clockwise turn. -/
@[simp]
theorem windingNumber_fdBoundary_I (hH : 1 < H) :
    Contour.windingNumber (fdBoundary H) 0 5 Complex.I = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_fdBoundary_I hH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end ModularForm

end TauCeti

end
