/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.NonCorner.Basic

/-!
# Winding of the boundary contour at the open vertical edges

A point `w` of an open vertical edge is crossed by exactly one straight segment of the
boundary contour, and the winding number there is `-1/2`: half a clockwise turn. Along the
crossing segment the shifted contour `γ t - w` is purely imaginary, so the chord distance is
linear in the parameter and the matched half-width is `δ(ε) = ε / (H - √3/2)`. The adapted
branch (`Winding/NonCorner/Basic.lean`) negates on the right edge and is the principal one on
the left; either way the excision endpoints are `±ε·i` and the excised integral is the
constant `-π·i`.

Two spellings recur below: linear bounds enter as inline `show _ by linarith` terms, stating
each bound at the sign-adjusted operand its consuming `abs` estimate needs, and the log
evaluations reshape real-cast products by `show _ by push_cast; ring` into the
`((r : ℝ) : ℂ) * z` operand that `Complex.log_ofReal_mul` splits.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_vertical`,
  `TauCeti.ModularForm.windingNumber_fdBoundary_vertical`: the principal value `-πi` and the
  winding number `-1/2` at a point of an open vertical edge.

The hypotheses are spelled the way the singular-set interface provides them
(`TauCeti.ModularForm.verticalSingularSet`): a vertical point carries
`w.re = 2⁻¹ ∨ w.re = -(2⁻¹)`, `1 < ‖w‖`, `0 < w.im` and `w.im < H`; no lower height
hypothesis is needed.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) (commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck) — the statement
  pair fills the vertical-edge role of that project's `FDWindingDataFull.boundary_winding`,
  whose vertical inputs are the FTC-provider files `ForMathlib/Seg1FTCProvider.lean` and
  `ForMathlib/Seg4FTCProvider.lean`. The proof route is Tau Ceti's own rotated-branch
  telescope.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

open Contour

namespace ModularForm

variable {H t s ε : ℝ} {w : ℂ}
/-! ## The vertical edges

A point `w` of an open vertical edge is crossed by exactly one straight segment. Along it the
shifted contour `γ t - w` is purely imaginary, so the chord distance is linear in the
parameter and the matched half-width is `δ(ε) = ε / (H - √3/2)`. The adapted branch negates
on the right edge and is the principal one on the left; either way the excision endpoints are
`±ε·i` and the excised integral is the constant `-π·i`.

Two spellings recur below: linear bounds enter as inline `show _ by linarith` terms, stating
each bound at the sign-adjusted operand its consuming `abs` estimate needs, and the log
evaluations reshape real-cast products by `show _ by push_cast; ring` into the
`((r : ℝ) : ℂ) * z` operand that `Complex.log_ofReal_mul` splits.
-/

/-- On the right vertical the shifted contour is purely imaginary, with signed height linear
in the parameter. -/
private lemma fdBoundary_sub_of_le_one (hre : w.re = 1 / 2) (hs : s ≤ 1) :
    fdBoundary H s - w =
      ((H - w.im - s * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [Complex.sub_re, re_fdBoundary_of_le_one hs, hre, Complex.mul_I_re, Complex.ofReal_im]
    norm_num
  · rw [Complex.sub_im, im_fdBoundary_of_le_one hs, Complex.mul_I_im, Complex.ofReal_re]
    ring

/-- On the left vertical the shifted contour is purely imaginary, with signed height linear
in the parameter. -/
private lemma fdBoundary_sub_of_mem_Icc_three_four (hre : w.re = -(1 / 2))
    (hs : s ∈ Icc (3 : ℝ) 4) :
    fdBoundary H s - w =
      ((Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im : ℝ) : ℂ) * Complex.I := by
  refine Complex.ext ?_ ?_
  · rw [Complex.sub_re, re_fdBoundarySegment4 H hs, hre, Complex.mul_I_re, Complex.ofReal_im]
    norm_num
  · rw [Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re]
    rcases eq_or_lt_of_le hs.1 with h3 | h3
    · rw [← h3, fdBoundary_apply_three]
      rw [rho_im]
      ring
    · rw [im_fdBoundary_of_le_four h3 hs.2]

/-- For a right-vertical point, the negated branch is slit-plane-valued wherever the contour
misses `w`: the whole contour lies weakly left of the edge. -/
private lemma slit_branch_vertical_right (hre : w.re = 1 / 2) (ht : t ≤ 5)
    (hne : fdBoundary H t ≠ w) : (fdBoundary H t - w) * (-1) ∈ Complex.slitPlane := by
  have hre0 : 0 ≤ (w - fdBoundary H t).re := by
    rw [Complex.sub_re, hre]
    linarith [(abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht)).2]
  rw [mul_neg_one, neg_sub, Complex.mem_slitPlane_iff]
  rcases eq_or_ne (w - fdBoundary H t).im 0 with him0 | him0
  · rcases lt_or_eq_of_le hre0 with h | h
    · exact Or.inl h
    · refine absurd (sub_eq_zero.mp ?_).symm hne
      exact Complex.ext (by simpa using h.symm) (by simpa using him0)
  · exact Or.inr him0

/-- For a left-vertical point, the principal branch is slit-plane-valued wherever the contour
misses `w`: the whole contour lies weakly right of the edge. -/
private lemma slit_branch_vertical_left (hre : w.re = -(1 / 2)) (ht : t ≤ 5)
    (hne : fdBoundary H t ≠ w) : fdBoundary H t - w ∈ Complex.slitPlane := by
  have hre0 : 0 ≤ (fdBoundary H t - w).re := by
    rw [Complex.sub_re, hre]
    linarith [(abs_le.mp (abs_re_fdBoundary_le_half (H := H) ht)).1]
  rw [Complex.mem_slitPlane_iff]
  rcases eq_or_ne (fdBoundary H t - w).im 0 with him0 | him0
  · rcases lt_or_eq_of_le hre0 with h | h
    · exact Or.inl h
    · refine absurd (sub_eq_zero.mp ?_) hne
      exact Complex.ext (by simpa using h.symm) (by simpa using him0)
  · exact Or.inr him0

/-- The endpoint-log difference shared by both vertical edges: the two excision endpoints
of a straight crossing sit at `∓ε·i` for the adapted branch, and their logarithms differ by
the straight angle `-π·i` — the log-norm parts cancel exactly. -/
private lemma log_neg_eps_I_sub_log_eps_I (hε : 0 < ε) :
    Complex.log (((-ε : ℝ) : ℂ) * Complex.I) - Complex.log ((ε : ℂ) * Complex.I) =
      -(Real.pi : ℂ) * Complex.I := by
  rw [show ((-ε : ℝ) : ℂ) * Complex.I = (ε : ℂ) * -Complex.I by push_cast; ring,
    Complex.log_ofReal_mul hε (neg_ne_zero.mpr Complex.I_ne_zero),
    Complex.log_ofReal_mul hε Complex.I_ne_zero, Complex.log_neg_I, Complex.log_I]
  ring

/-- The contour meets a right-vertical point only at the crossing parameter
`t₀ = (H - w.im) / (H - √3/2)`. -/
private lemma fdBoundary_ne_right (hre : w.re = 1 / 2) (hnorm : 1 < ‖w‖)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H)
    (hts : t ≠ (H - w.im) / (H - Real.sqrt 3 / 2)) : fdBoundary H t ≠ w := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hI := fdBoundary_sub_of_le_one (H := H) hre h1
    rw [heq, sub_self] at hI
    have h0 : H - w.im - t * (H - Real.sqrt 3 / 2) = 0 := by
      simpa using congrArg Complex.im hI.symm
    refine hts ?_
    rw [eq_div_iff hk.ne']
    linarith
  · rcases le_or_gt t 3 with h3 | h3
    · have hn := norm_fdBoundary_arc (H := H) h1.le h3
      rw [heq] at hn
      linarith
    · rcases le_or_gt t 4 with h4 | h4
      · have hr := re_fdBoundarySegment4 H ⟨h3.le, h4⟩
        rw [heq, hre] at hr
        norm_num at hr
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        linarith

/-- The contour meets a left-vertical point only at the crossing parameter
`t₀ = 3 + (w.im - √3/2) / (H - √3/2)`. -/
private lemma fdBoundary_ne_left (hre : w.re = -(1 / 2)) (hnorm : 1 < ‖w‖)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H)
    (hts : t ≠ 3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)) :
    fdBoundary H t ≠ w := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hr := re_fdBoundary_of_le_one (H := H) h1
    rw [heq, hre] at hr
    norm_num at hr
  · rcases le_or_gt t 3 with h3 | h3
    · have hn := norm_fdBoundary_arc (H := H) h1.le h3
      rw [heq] at hn
      linarith
    · rcases le_or_gt t 4 with h4 | h4
      · have hI := fdBoundary_sub_of_mem_Icc_three_four (H := H) hre ⟨h3.le, h4⟩
        rw [heq, sub_self] at hI
        have h0 : Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - w.im = 0 := by
          simpa using congrArg Complex.im hI.symm
        refine hts ?_
        have hdiv : t - 3 = (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) := by
          rw [eq_div_iff hk.ne']
          linarith
        linarith
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        linarith

/-- Away from the right vertical, the contour keeps its distance from a right-vertical
point: at least `1` on the opposite vertical, `‖w‖ - 1` on the arc, and `H - w.im` on the
ceiling. -/
private lemma lt_norm_sub_right_of_off_segment (hre : w.re = 1 / 2)
    (hε₁ : ε < 1) (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (h1 : 1 ≤ s)
    (h5 : s ≤ 5) : ε < ‖fdBoundary H s - w‖ := by
  rcases le_or_gt s 3 with h3 | h3
  · calc ε < ‖w‖ - ‖fdBoundary H s‖ := by rw [norm_fdBoundary_arc h1 h3]; linarith
      _ ≤ ‖w - fdBoundary H s‖ := norm_sub_norm_le _ _
      _ = ‖fdBoundary H s - w‖ := norm_sub_rev _ _
  · rcases le_or_gt s 4 with h4 | h4
    · have hr : (fdBoundary H s - w).re = -1 := by
        rw [Complex.sub_re, re_fdBoundarySegment4 H ⟨h3.le, h4⟩, hre]
        norm_num
      calc ε < 1 := hε₁
        _ = |(fdBoundary H s - w).re| := by rw [hr]; norm_num
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · have hi : (fdBoundary H s - w).im = H - w.im := by
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, h5⟩]
      calc ε < H - w.im := hεc
        _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- Away from the left vertical, the contour keeps its distance from a left-vertical point:
at least `1` on the opposite vertical, `‖w‖ - 1` on the arc, and `H - w.im` on the
ceiling. -/
private lemma lt_norm_sub_left_of_off_segment (hre : w.re = -(1 / 2))
    (hε₁ : ε < 1) (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hs : s ∈ Icc (0 : ℝ) 5)
    (hoff : s ≤ 3 ∨ 4 ≤ s) : ε < ‖fdBoundary H s - w‖ := by
  rcases hoff with h3 | h4
  · rcases le_or_gt s 1 with h1 | h1
    · have hr : (fdBoundary H s - w).re = 1 := by
        rw [Complex.sub_re, re_fdBoundary_of_le_one h1, hre]
        norm_num
      calc ε < 1 := hε₁
        _ = |(fdBoundary H s - w).re| := by rw [hr]; norm_num
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · calc ε < ‖w‖ - ‖fdBoundary H s‖ := by rw [norm_fdBoundary_arc h1.le h3]; linarith
        _ ≤ ‖w - fdBoundary H s‖ := norm_sub_norm_le _ _
        _ = ‖fdBoundary H s - w‖ := norm_sub_rev _ _
  · have hi : (fdBoundary H s - w).im = H - w.im := by
      rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4, hs.2⟩]
    calc ε < H - w.im := hεc
      _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
      _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- The norm of the shifted contour along the right vertical, in linear form. -/
private lemma norm_fdBoundary_sub_of_le_one (hre : w.re = 1 / 2) (hs : s ≤ 1) :
    ‖fdBoundary H s - w‖ = |H - w.im - s * (H - Real.sqrt 3 / 2)| := by
  rw [fdBoundary_sub_of_le_one hre hs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The window of a right-vertical crossing**: the chord-matched window around the
crossing parameter sits inside the open segment range, and its endpoints are exactly
`w ± ε·i`. -/
private lemma right_window_endpoints (hre : w.re = 1 / 2) (hε : 0 < ε)
    (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    0 < (H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2) ∧
    (H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 ∧
    fdBoundary H ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2)) - w =
      (ε : ℂ) * Complex.I ∧
    fdBoundary H ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)) - w =
      ((-ε : ℝ) : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  have ht₀k : (H - w.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - w.im :=
    div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  have hwl : 0 < (H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2) := by
    rw [← sub_div]
    exact div_pos (by linarith) hk
  have hwr : (H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 := by
    rw [← add_div, div_lt_one hk]
    linarith
  refine ⟨hwl, hwr, ?_, ?_⟩ <;> rw [fdBoundary_sub_of_le_one hre (by linarith [hwr])]
  · exact congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) (by rw [sub_mul]; linarith)
  · exact congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) (by rw [add_mul]; linarith)

/-- **The distance bounds of a right-vertical crossing**: beyond the chord-matched window
the contour keeps distance more than `ε` from `w`, and within it at most `ε`. -/
private lemma right_window_bounds (hre : w.re = 1 / 2) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    (∀ s ∈ Ioo (0 : ℝ) ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2)),
      ε < ‖fdBoundary H s - w‖) ∧
    (∀ s ∈ Ioo ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)) (5 : ℝ),
      ε < ‖fdBoundary H s - w‖) ∧
    ∀ s ∈ Icc ((H - w.im) / (H - Real.sqrt 3 / 2) - ε / (H - Real.sqrt 3 / 2))
      ((H - w.im) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)),
      ‖fdBoundary H s - w‖ ≤ ε := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, -, -⟩ := right_window_endpoints hre hε hεc hεv
  have ht₀k : (H - w.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - w.im :=
    div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · have hlt := mul_lt_mul_of_pos_right hs.2 hk
    rw [sub_mul, ht₀k, hδk] at hlt
    rw [norm_fdBoundary_sub_of_le_one hre (by linarith [hs.2, hwr])]
    exact lt_of_lt_of_le
      (show ε < H - w.im - s * (H - Real.sqrt 3 / 2) by linarith) (le_abs_self _)
  · rcases le_or_gt s 1 with h1 | h1
    · have hlt := mul_lt_mul_of_pos_right hs.1 hk
      rw [add_mul, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_le_one hre h1]
      exact lt_of_lt_of_le
        (show ε < -(H - w.im - s * (H - Real.sqrt 3 / 2)) by linarith) (neg_le_abs _)
    · exact lt_norm_sub_right_of_off_segment hre hε₁ hεa hεc h1.le hs.2.le
  · have hl := mul_le_mul_of_nonneg_right hs.1 hk.le
    have hr := mul_le_mul_of_nonneg_right hs.2 hk.le
    rw [sub_mul, ht₀k, hδk] at hl
    rw [add_mul, ht₀k, hδk] at hr
    rw [norm_fdBoundary_sub_of_le_one hre (by linarith [hs.2, hwr])]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The excision collapse at a right-vertical point**: for small `ε`, the `ε`-excised
index integrand of the boundary contour about `w` is interval integrable, and its integral
is exactly `-πi` — the excision endpoints are `w ± ε·i` and the log-norm parts cancel. -/
private lemma truncated_integral_spec_right (hre : w.re = 1 / 2)
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, hL, hR⟩ := right_window_endpoints hre hε hεc hεv
  obtain ⟨hfl, hfr, hnear⟩ := right_window_bounds hre hε hε₁ hεa hεc hεv
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := -1)
    (neg_ne_zero.mpr one_ne_zero) hwl.le hδpos (by linarith)
    (fun t ht htw ↦ slit_branch_vertical_right hre ht.2 (fdBoundary_ne_right hre
      (by linarith) him_lo himH fun h ↦ htw (by rw [h]; exact ⟨by linarith, by linarith⟩)))
    hfl hfr hnear
  refine ⟨hint, ?_⟩
  rw [hval, hL, hR, show (ε : ℂ) * Complex.I * -1 = ((-ε : ℝ) : ℂ) * Complex.I by
      push_cast; ring,
    show ((-ε : ℝ) : ℂ) * Complex.I * -1 = (ε : ℂ) * Complex.I by push_cast; ring]
  exact log_neg_eps_I_sub_log_eps_I hε

/-- The norm of the shifted contour along the left vertical, in linear form. -/
private lemma norm_fdBoundary_sub_of_mem_Icc_three_four (hre : w.re = -(1 / 2))
    (hs : s ∈ Icc (3 : ℝ) 4) : ‖fdBoundary H s - w‖ =
      |Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im| := by
  rw [fdBoundary_sub_of_mem_Icc_three_four hre hs, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

/-- **The window of a left-vertical crossing**: the chord-matched window around the
crossing parameter sits inside the open segment range, and its endpoints are exactly
`w ∓ ε·i`. -/
private lemma left_window_endpoints (hre : w.re = -(1 / 2)) (hε : 0 < ε)
    (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    ε / (H - Real.sqrt 3 / 2) < (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ∧
    (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2) < 1 ∧
    fdBoundary H (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
        ε / (H - Real.sqrt 3 / 2)) - w = ((-ε : ℝ) : ℂ) * Complex.I ∧
    fdBoundary H (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) +
        ε / (H - Real.sqrt 3 / 2)) - w = (ε : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  have ht₀k : (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) =
      w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : ε / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  have hwl : ε / (H - Real.sqrt 3 / 2) < (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) :=
    by rw [div_lt_div_iff_of_pos_right hk]; linarith
  have hwr : (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)
      < 1 := by rw [← add_div, div_lt_one hk]; linarith
  refine ⟨hwl, hwr, ?_, ?_⟩ <;>
    rw [fdBoundary_sub_of_mem_Icc_three_four hre ⟨by linarith, by linarith⟩]
  · refine congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) ?_
    rw [sub_right_comm, add_sub_cancel_left, sub_mul]
    linarith
  · refine congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) ?_
    rw [add_assoc, add_sub_cancel_left, add_mul]
    linarith

/-- **The near bound of a left-vertical crossing**: within the chord-matched window the
contour stays within `ε` of `w`. -/
private lemma left_window_near (hre : w.re = -(1 / 2)) (hε : 0 < ε) (hεc : ε < H - w.im)
    (hεv : ε < w.im - Real.sqrt 3 / 2) :
    ∀ s ∈ Icc (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
        ε / (H - Real.sqrt 3 / 2))
      (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) + ε / (H - Real.sqrt 3 / 2)),
      ‖fdBoundary H s - w‖ ≤ ε := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  obtain ⟨hwl, hwr, -, -⟩ := left_window_endpoints hre hε hεc hεv
  set u := (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)
  set δ := ε / (H - Real.sqrt 3 / 2)
  have hδpos : 0 < δ := div_pos hε hk
  have ht₀k : u * (H - Real.sqrt 3 / 2) = w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : δ * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  intro s hs
  have hl := mul_le_mul_of_nonneg_right (show u - δ ≤ s - 3 by linarith [hs.1]) hk.le
  have hr := mul_le_mul_of_nonneg_right (show s - 3 ≤ u + δ by linarith [hs.2]) hk.le
  rw [sub_mul u δ, ht₀k, hδk] at hl
  rw [add_mul u δ, ht₀k, hδk] at hr
  rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre
    ⟨by linarith [hs.1, hwl], by linarith [hs.2, hwr]⟩]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The far bounds of a left-vertical crossing**: beyond the chord-matched window the
contour keeps distance more than `ε` from `w`. -/
private lemma left_window_bounds (hre : w.re = -(1 / 2)) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    (∀ s ∈ Ioo (0 : ℝ) (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) -
      ε / (H - Real.sqrt 3 / 2)), ε < ‖fdBoundary H s - w‖) ∧
    ∀ s ∈ Ioo (3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) +
      ε / (H - Real.sqrt 3 / 2)) (5 : ℝ), ε < ‖fdBoundary H s - w‖ := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  obtain ⟨hwl, hwr, -, -⟩ := left_window_endpoints hre hε hεc hεv
  set u := (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)
  set δ := ε / (H - Real.sqrt 3 / 2)
  have hδpos : 0 < δ := div_pos hε hk
  have ht₀k : u * (H - Real.sqrt 3 / 2) = w.im - Real.sqrt 3 / 2 := div_mul_cancel₀ _ hk.ne'
  have hδk : δ * (H - Real.sqrt 3 / 2) = ε := div_mul_cancel₀ _ hk.ne'
  refine ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rcases le_or_gt s 3 with h3 | h3
    · exact lt_norm_sub_left_of_off_segment hre hε₁ hεa hεc
        ⟨hs.1.le, by linarith [hs.2, hwr]⟩ (Or.inl h3)
    · have hlt := mul_lt_mul_of_pos_right (show s - 3 < u - δ by linarith [hs.2]) hk
      rw [sub_mul u δ, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre ⟨h3.le, by linarith [hs.2, hwr]⟩]
      exact lt_of_lt_of_le
        (show ε < -(Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im) by linarith)
        (neg_le_abs _)
  · rcases le_or_gt s 4 with h4 | h4
    · have hlt := mul_lt_mul_of_pos_right (show u + δ < s - 3 by linarith [hs.1]) hk
      rw [add_mul u δ, ht₀k, hδk] at hlt
      rw [norm_fdBoundary_sub_of_mem_Icc_three_four hre ⟨by linarith [hs.1], h4⟩]
      exact lt_of_lt_of_le
        (show ε < Real.sqrt 3 / 2 + (s - 3) * (H - Real.sqrt 3 / 2) - w.im by linarith)
        (le_abs_self _)
    · exact lt_norm_sub_left_of_off_segment hre hε₁ hεa hεc
        ⟨by linarith [hs.1], hs.2.le⟩ (Or.inr h4.le)

/-- **The excision collapse at a left-vertical point**: for small `ε`, the `ε`-excised index
integrand of the boundary contour about `w` is interval integrable, and its integral is
exactly `-πi`. -/
private lemma truncated_integral_spec_left (hre : w.re = -(1 / 2))
    (him_lo : Real.sqrt 3 / 2 < w.im) (himH : w.im < H) (hε : 0 < ε) (hε₁ : ε < 1)
    (hεa : ε < ‖w‖ - 1) (hεc : ε < H - w.im) (hεv : ε < w.im - Real.sqrt 3 / 2) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I := by
  have hk : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hδpos : 0 < ε / (H - Real.sqrt 3 / 2) := div_pos hε hk
  obtain ⟨hwl, hwr, hL, hR⟩ := left_window_endpoints hre hε hεc hεv
  obtain ⟨hfl, hfr⟩ := left_window_bounds hre hε hε₁ hεa hεc hεv
  have hnear := left_window_near hre hε hεc hεv
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := 1) one_ne_zero
    (t₀ := 3 + (w.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)) (by linarith) hδpos
    (by linarith)
    (fun t ht htw ↦ by
      rw [mul_one]
      refine slit_branch_vertical_left hre ht.2 (fdBoundary_ne_left hre (by linarith)
        him_lo himH fun h ↦ htw ?_)
      rw [h]
      exact ⟨by linarith, by linarith⟩)
    hfl hfr hnear
  refine ⟨hint, ?_⟩
  rw [hval, hL, hR, mul_one, mul_one]
  exact log_neg_eps_I_sub_log_eps_I hε

/-- A point of an open vertical edge lies strictly above the corner row. -/
private lemma sqrt_three_div_two_lt_im (hre : w.re = 1 / 2 ∨ w.re = -(1 / 2))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) : Real.sqrt 3 / 2 < w.im := by
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hre2 : w.re ^ 2 = 1 / 4 := by rcases hre with h | h <;> rw [h] <;> norm_num
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 3, norm_nonneg w]

/-- **The principal value at a vertical-edge point**: the Cauchy principal value of the
index integrand of the boundary contour about a point of an open vertical edge is `-πi` —
half a clockwise turn, as the contour passes straight through `w` along the edge. -/
theorem hasCauchyPVAt_fdBoundary_vertical (hre : w.re = 2⁻¹ ∨ w.re = -(2⁻¹))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) (himH : w.im < H) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - w)⁻¹) w
      (-(Real.pi : ℂ) * Complex.I) := by
  rw [← one_div] at hre
  have him_lo := sqrt_three_div_two_lt_im hre hnorm him
  have hb : (0 : ℝ) <
      min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2)) :=
    lt_min (lt_min one_pos (by linarith)) (lt_min (by linarith) (by linarith))
  have hIoo : Ioo (0 : ℝ) (min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2)))
      ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hb))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ)
      (min (min 1 (‖w‖ - 1)) (min (H - w.im) (w.im - Real.sqrt 3 / 2))),
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I := by
    intro ε hε
    have h1 := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have ha := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hc := hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hv := hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    rcases hre with h | h
    · exact truncated_integral_spec_right h him_lo himH hε.1 h1 ha hc hv
    · exact truncated_integral_spec_left h him_lo himH hε.1 h1 ha hc hv
  exact Contour.HasCauchyPVAt.of_tendsto tendsto_const_nhds (eventually_of_mem hIoo hspec)

/-- **The winding number of the boundary contour at a vertical-edge point is `-1/2`**: the
point sits on an open vertical edge, and the principal-value normalization sees exactly half
a clockwise turn. -/
@[simp]
theorem windingNumber_fdBoundary_vertical (hre : w.re = 2⁻¹ ∨ w.re = -(2⁻¹))
    (hnorm : 1 < ‖w‖) (him : 0 < w.im) (himH : w.im < H) :
    Contour.windingNumber (fdBoundary H) 0 5 w = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_fdBoundary_vertical hre hnorm him himH)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end ModularForm

end TauCeti

end
