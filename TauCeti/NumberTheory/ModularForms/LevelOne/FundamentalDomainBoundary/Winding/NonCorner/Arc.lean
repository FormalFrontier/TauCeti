/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Containment
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.NonCorner.Basic
import TauCeti.Topology.Circle.Metric

/-!
# Winding of the boundary contour at the open unit arc

A point `w` of the open unit arc is `fdBoundary H t₀` for a unique `t₀ ∈ (1, 3)`; the arc is
one smooth circle parameterization through `t = 2`, so no corner is in the way even at `i`,
and the winding number at every open-arc point is `-1/2`. The adapted branch
(`Winding/NonCorner/Basic.lean`) is `c = w⁻¹`, whose cut ray `{r·w : r ≤ 1}` runs from `w`
through the open unit disc and leaves through the lower half-plane, missing the rest of the
contour. The chord distance is `2·sin(|t - t₀|·π/12)`, uniform along the arc; the excised
integral is `-π·i - 2·arcsin(ε/2)·i`, and the limit is `-π·i`.

The statements cover the whole open arc, including `i`: a consumer wanting the value there
supplies the elliptic point's three elementary facts — `‖i‖ = 1`, `|re i| = 0 < 1/2`,
`0 < im i` — directly to the theorems below.

The polar computations below restate angle and cast algebra as inline `show _ by ring` /
`show _ by push_cast; ring` equations: each aims the expression at the exact spelling the
next `Real.cos`/`Complex.exp`/`Complex.log` rewrite matches.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPVAt_fdBoundary_arc`,
  `TauCeti.ModularForm.windingNumber_fdBoundary_arc`: the principal value `-πi` and the
  winding number `-1/2` at a point of the open unit arc.

The hypotheses are spelled the way the singular-set interface provides them
(`TauCeti.ModularForm.arcSingularSet`): an arc point carries `‖w‖ = 1`, `|w.re| < 2⁻¹` and
`0 < w.im`. The theorems also assume `1 < H`, which makes the contour the boundary of a
genuine truncation: the ceiling then clears the arc point by `H - 1 > 0`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) (commit
  `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck) — the statement
  pair fills the arc role of that project's `FDWindingDataFull.boundary_winding`, whose arc
  input is the FTC-provider file `ForMathlib/ArcGenericFTCProvider.lean`. The proof route is
  Tau Ceti's own rotated-branch telescope.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Filter MeasureTheory Set Topology

namespace TauCeti

open Contour

namespace ModularForm

variable {H t t₀ δ ε : ℝ} {w : ℂ}
/-! ## The arc

A point `w` of the open unit arc is `fdBoundary H t₀` for a unique `t₀ ∈ (1, 3)`; the arc is
one smooth circle parameterization through `t = 2`, so no corner is in the way even at `i`.
The adapted branch is `c = w⁻¹`, whose cut ray `{r·w : r ≤ 1}` runs from `w` through the
open unit disc and leaves through the lower half-plane, missing the rest of the contour. The
chord distance is `2·sin(|t - t₀|·π/12)`, uniform along the arc.

The polar computations below restate angle and cast algebra as inline `show _ by ring` /
`show _ by push_cast; ring` equations: each aims the expression at the exact spelling the
next `Real.cos`/`Complex.exp`/`Complex.log` rewrite matches.
-/

/-- The argument of a point of the open unit arc lies in the open middle third of
`(0, π)`. -/
private lemma arg_mem_Ioo (hnorm : ‖w‖ = 1) (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    Complex.arg w ∈ Ioo (Real.pi / 3) (2 * Real.pi / 3) := by
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  have hcos : Real.cos (Complex.arg w) = w.re := by rw [Complex.cos_arg hw0, hnorm, div_one]
  have habs := abs_lt.mp hre
  have harg_lt : Complex.arg w < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  have harg_pos : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr him.le
  constructor
  · by_contra hle
    push Not at hle
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi harg_pos (by linarith [Real.pi_pos]) hle
    rw [hcos, Real.cos_pi_div_three] at hmono
    linarith [habs.2]
  · by_contra hle
    push Not at hle
    have hmono := Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) harg_lt.le hle
    rw [hcos, show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hmono
    linarith [habs.1]

/-- Every point of the open unit arc is hit by the arc parameterization. -/
private lemma exists_arc_param (hnorm : ‖w‖ = 1) (hre : |w.re| < 1 / 2) (him : 0 < w.im) :
    ∃ t₀ ∈ Ioo (1 : ℝ) 3, fdBoundary H t₀ = w := by
  have hπ := Real.pi_pos
  have h13 := arg_mem_Ioo hnorm hre him
  have h1 : (1 : ℝ) < 6 * Complex.arg w / Real.pi - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hπ]
    nlinarith [h13.1]
  have h3 : 6 * Complex.arg w / Real.pi - 1 < 3 := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hπ]
    nlinarith [h13.2]
  refine ⟨6 * Complex.arg w / Real.pi - 1, ⟨h1, h3⟩, ?_⟩
  have hcurve : fdBoundary H (6 * Complex.arg w / Real.pi - 1) =
      circleMap 0 1 ((6 * Complex.arg w / Real.pi - 1 + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨h1.le, h3.le⟩
  have hpolar := Complex.norm_mul_exp_arg_mul_I w
  rw [hnorm, Complex.ofReal_one, one_mul] at hpolar
  rw [hcurve,
    show (6 * Complex.arg w / Real.pi - 1 + 1) * (Real.pi / 6) = Complex.arg w by
      field_simp; ring,
    circleMap_zero, Complex.ofReal_one, one_mul]
  exact hpolar

/-- On the arc the distance between two contour points is the chord distance
`2·sin(|t - t₀|·π/12)`, up to the absolute value inside the sine. -/
private lemma norm_fdBoundary_sub_fdBoundary_arc (ht : t ∈ Icc (1 : ℝ) 3)
    (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - fdBoundary H t₀‖ = 2 * |Real.sin ((t - t₀) * (Real.pi / 12))| := by
  rw [eqOn_fdBoundary_arc H ht, eqOn_fdBoundary_arc H ht₀, ← Complex.dist_eq,
    dist_circleMap_eq_two_mul_abs_sin,
    show ((t + 1) * (Real.pi / 6) - (t₀ + 1) * (Real.pi / 6)) / 2 = (t - t₀) * (Real.pi / 12)
      by ring]
  norm_num

/-- Far from the crossing along the arc, the chord distance strictly exceeds the excision
chord. -/
private lemma lt_norm_sub_arc_of_far (ht : t ∈ Icc (1 : ℝ) 3) (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hδ : 0 < δ) (hfar : δ < |t - t₀|) :
    2 * Real.sin (δ * (Real.pi / 12)) < ‖fdBoundary H t - fdBoundary H t₀‖ := by
  have habs2 : |t - t₀| ≤ 2 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1, ht₀.2], by linarith [ht.2, ht₀.1]⟩
  rw [norm_fdBoundary_sub_fdBoundary_arc ht ht₀,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (δ * (Real.pi / 12)) < Real.sin (|t - t₀| * (Real.pi / 12)) := by
    refine Real.strictMonoOn_sin ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos, abs_nonneg (t - t₀)], by nlinarith [Real.pi_pos]⟩ ?_
    exact mul_lt_mul_of_pos_right hfar (by positivity)
  linarith

/-- Near the crossing along the arc, the chord distance is at most the excision chord. -/
private lemma norm_sub_arc_le_of_near (ht : t ∈ Icc (1 : ℝ) 3) (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hδ2 : δ ≤ 2) (hnear : |t - t₀| ≤ δ) :
    ‖fdBoundary H t - fdBoundary H t₀‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hnear
  rw [norm_fdBoundary_sub_fdBoundary_arc ht ht₀,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
      nlinarith [Real.pi_pos, abs_nonneg (t - t₀)]),
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 12)]
  have hmono : Real.sin (|t - t₀| * (Real.pi / 12)) ≤ Real.sin (δ * (Real.pi / 12)) := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos, abs_nonneg (t - t₀)]) (by nlinarith [Real.pi_pos]) ?_
    exact mul_le_mul_of_nonneg_right hnear (by positivity)
  linarith

/-- The rotated shifted contour along the arc, with signed offset: the half-angle sine
turned a quarter past the offset half-angle. The rotation `w⁻¹` makes the polar data
independent of the crossing point. -/
private lemma fdBoundary_sub_mul_inv_polar {ξ : ℝ} (ht₀ : t₀ ∈ Icc (1 : ℝ) 3)
    (hξ : t₀ + ξ ∈ Icc (1 : ℝ) 3) :
    (fdBoundary H (t₀ + ξ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      2 * ((Real.sin (ξ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I *
        Complex.exp (((ξ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have h1 : fdBoundary H (t₀ + ξ) =
      Complex.exp ((((t₀ + ξ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
    have hcurve : fdBoundary H (t₀ + ξ) = circleMap 0 1 ((t₀ + ξ + 1) * (Real.pi / 6)) :=
      eqOn_fdBoundary_arc H hξ
    rw [hcurve, circleMap_zero, Complex.ofReal_one, one_mul]
  have h2 : fdBoundary H t₀ =
      Complex.exp ((((t₀ + 1) * (Real.pi / 6) : ℝ) : ℂ) * Complex.I) := by
    have hcurve : fdBoundary H t₀ = circleMap 0 1 ((t₀ + 1) * (Real.pi / 6)) :=
      eqOn_fdBoundary_arc H ht₀
    rw [hcurve, circleMap_zero, Complex.ofReal_one, one_mul]
  rw [h1, h2, exp_mul_I_sub_exp_mul_I,
    show ((t₀ + ξ + 1) * (Real.pi / 6) - (t₀ + 1) * (Real.pi / 6)) / 2 = ξ * (Real.pi / 12)
      by ring,
    ← Complex.exp_neg, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The rotated shifted contour beside the crossing, right side, in polar form: radial part
`2·sin(δ·π/12)` and argument `π/2 + δ·π/12`. -/
private lemma fdBoundary_sub_mul_inv_add_eq (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ)
    (hδ3 : t₀ + δ ≤ 3) :
    (fdBoundary H (t₀ + δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((Real.pi / 2 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  rw [fdBoundary_sub_mul_inv_polar ht₀ ⟨by linarith [ht₀.1], hδ3⟩,
    show ((Real.pi / 2 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I =
      (Real.pi : ℂ) / 2 * Complex.I + ((δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
    Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  push_cast
  ring

/-- The rotated shifted contour beside the crossing, left side, in polar form: the mirror
argument `-(π/2 + δ·π/12)`. -/
private lemma fdBoundary_sub_mul_inv_sub_eq (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ)
    (hδ1 : 1 ≤ t₀ - δ) :
    (fdBoundary H (t₀ - δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹ =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((-(Real.pi / 2 + δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I) := by
  have h := fdBoundary_sub_mul_inv_polar (H := H) (ξ := -δ) ht₀
    ⟨by linarith, by linarith [ht₀.2]⟩
  rw [← sub_eq_add_neg, neg_mul, Real.sin_neg] at h
  rw [h, show ((-(Real.pi / 2 + δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I =
      -((Real.pi : ℂ) / 2 * Complex.I) + ((-(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
    Complex.exp_add, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  push_cast
  ring

/-- **The symmetric log difference at the crossing**: the two endpoint logarithms of the
`δ`-excised arc for the rotated branch differ by the pure phase `-(π + δ·π/6)·i` — the chord
norms agree, and only the argument difference survives. -/
private lemma log_sub_log_arc (ht₀ : t₀ ∈ Icc (1 : ℝ) 3) (hδ : 0 < δ) (hδ1 : 1 ≤ t₀ - δ)
    (hδ3 : t₀ + δ ≤ 3) :
    Complex.log ((fdBoundary H (t₀ - δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹) -
      Complex.log ((fdBoundary H (t₀ + δ) - fdBoundary H t₀) * (fdBoundary H t₀)⁻¹) =
      -((Real.pi + δ * (Real.pi / 6) : ℝ) : ℂ) * Complex.I := by
  have hπ := Real.pi_pos
  have hδ2 : δ ≤ 2 := by linarith [ht₀.1, ht₀.2]
  have hsin : 0 < Real.sin (δ * (Real.pi / 12)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  rw [fdBoundary_sub_mul_inv_sub_eq ht₀ hδ hδ1, fdBoundary_sub_mul_inv_add_eq ht₀ hδ hδ3,
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith) (by simp; nlinarith),
    Complex.log_exp (by simp; nlinarith) (by simp; nlinarith)]
  push_cast
  ring

/-- The contour meets an arc point only at its arc parameter. -/
private lemma fdBoundary_ne_arc (hH : 1 < H) (hre : |w.re| < 1 / 2)
    (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) (hw : fdBoundary H t₀ = w)
    (hts : t ≠ t₀) : fdBoundary H t ≠ w := by
  intro heq
  rcases le_or_gt t 1 with h1 | h1
  · have hr := re_fdBoundary_of_le_one (H := H) h1
    rw [heq] at hr
    rw [hr] at hre
    norm_num at hre
  · rcases le_or_gt t 3 with h3 | h3
    · exact hts (injOn_fdBoundary_arc H ⟨h1.le, h3⟩ ⟨ht₀.1.le, ht₀.2.le⟩
        (heq.trans hw.symm))
    · rcases le_or_gt t 4 with h4 | h4
      · have hr := re_fdBoundary_of_le_four (H := H) h3 h4
        rw [heq] at hr
        rw [hr] at hre
        norm_num at hre
      · have hi := im_fdBoundary_of_gt_four (H := H) h4
        rw [heq] at hi
        have him1 : w.im ≤ 1 := by
          rw [← hw]
          exact im_fdBoundary_arc_le H ⟨ht₀.1.le, ht₀.2.le⟩
        linarith

/-- For an arc point, the branch rotated by `w⁻¹` is slit-plane-valued wherever the contour
misses `w`: the cut ray `{r·w : r ≤ 1}` meets the contour only at `w` itself. -/
private lemma slit_branch_arc (hH : 1 < H) (hnorm : ‖w‖ = 1) (him : 0 < w.im)
    (ht : t ∈ Icc (0 : ℝ) 5) (hne : fdBoundary H t ≠ w) :
    (fdBoundary H t - w) * w⁻¹ ∈ Complex.slitPlane := by
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  by_contra hmem
  rw [Complex.mem_slitPlane_iff] at hmem
  push Not at hmem
  obtain ⟨hre0, him0⟩ := hmem
  set x := ((fdBoundary H t - w) * w⁻¹).re with hx
  have hxeq : (fdBoundary H t - w) * w⁻¹ = (x : ℂ) := Complex.ext rfl (by simpa using him0)
  have hγ : fdBoundary H t = (1 + (x : ℂ)) * w := by
    have h1 := congrArg (· * w) hxeq
    simp only [inv_mul_cancel_right₀ hw0] at h1
    linear_combination h1
  rcases le_or_gt 0 (1 + x) with hpos | hneg
  · have hn := congrArg norm hγ
    rw [norm_mul, hnorm, mul_one, show (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hn
    have h1 := one_le_norm_fdBoundary hH.le ht
    have hx0 : x = 0 := le_antisymm hre0 (by rw [hn] at h1; linarith)
    refine hne ?_
    rw [hγ, hx0]
    push_cast
    ring
  · have hi := congrArg Complex.im hγ
    rw [show (1 + (x : ℂ)) * w = ((1 + x : ℝ) : ℂ) * w by push_cast; ring] at hi
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at hi
    have him2 := sqrt_three_div_two_le_im_fdBoundary
      (le_of_lt (sqrt_three_div_two_lt_one.trans hH)) ht
    nlinarith [Real.sqrt_nonneg 3, mul_neg_of_neg_of_pos hneg him]

/-- **The chord-matched half-width fits the window**: for an excision radius `ε` below both
corner chords, the half-width `δ(ε)` is positive, keeps the window inside the open arc
range, and reproduces `ε` as its own chord. -/
private lemma arcExcisionHalfWidth_spec (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) (hε : 0 < ε)
    (hεl : ε < 2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
    (hεr : ε < 2 * Real.sin ((3 - t₀) * (Real.pi / 12))) :
    0 < fdBoundaryArcExcisionHalfWidth ε ∧
      fdBoundaryArcExcisionHalfWidth ε < t₀ - 1 ∧
      fdBoundaryArcExcisionHalfWidth ε < 3 - t₀ ∧
      2 * Real.sin (fdBoundaryArcExcisionHalfWidth ε * (Real.pi / 12)) = ε := by
  have hπ := Real.pi_pos
  have key : ∀ m : ℝ, 0 < m → m ≤ 2 → ε < 2 * Real.sin (m * (Real.pi / 12)) →
      fdBoundaryArcExcisionHalfWidth ε < m := by
    intro m hm hm2 hεm
    have harc : Real.arcsin (ε / 2) < m * (Real.pi / 12) := by
      have h1 : Real.arcsin (ε / 2) < Real.arcsin (Real.sin (m * (Real.pi / 12))) :=
        Real.arcsin_lt_arcsin (by linarith) (by linarith) (Real.sin_le_one _)
      rwa [Real.arcsin_sin (by nlinarith) (by nlinarith)] at h1
    rw [fdBoundaryArcExcisionHalfWidth_def, div_mul_eq_mul_div, div_lt_iff₀ hπ]
    nlinarith
  have hεπ : ε < 2 * Real.sin (Real.pi / 12) := by
    rcases le_total (t₀ - 1) (3 - t₀) with h | h
    · refine hεl.trans_le (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [ht₀.1]) (by nlinarith) ?_
      nlinarith [ht₀.1]
    · refine hεr.trans_le (mul_le_mul_of_nonneg_left ?_ (by norm_num))
      refine Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [ht₀.2]) (by nlinarith) ?_
      nlinarith [ht₀.2]
  obtain ⟨hδ0, _, h2sin⟩ :=
    fdBoundaryArcExcisionHalfWidth_pos_and_lt_one_and_two_mul_sin_eq hε hεπ
  exact ⟨hδ0, key _ (by linarith [ht₀.1]) (by linarith [ht₀.2]) hεl,
    key _ (by linarith [ht₀.2]) (by linarith [ht₀.1]) hεr, h2sin⟩

/-- Left of the excised window, the contour keeps distance more than `ε` from the arc
point. -/
private lemma lt_norm_sub_arc_of_far_left (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hδ : 0 < δ)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε) (hε₁ : ε < 1 / 2 - w.re)
    (hs : s ∈ Ioo (0 : ℝ) (t₀ - δ)) : ε < ‖fdBoundary H s - w‖ := by
  rcases le_or_gt s 1 with h1 | h1
  · have hr : (fdBoundary H s - w).re = 1 / 2 - w.re := by
      rw [Complex.sub_re, re_fdBoundary_of_le_one h1]
    calc ε < 1 / 2 - w.re := hε₁
      _ ≤ |(fdBoundary H s - w).re| := by rw [hr]; exact le_abs_self _
      _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
  · rw [← hw, ← h2sin]
    refine lt_norm_sub_arc_of_far ⟨h1.le, by linarith [hs.2, ht₀.2]⟩ ⟨ht₀.1.le, ht₀.2.le⟩
      hδ ?_
    rw [abs_sub_comm, abs_of_pos (by linarith [hs.2] : (0 : ℝ) < t₀ - s)]
    linarith [hs.2]

/-- Right of the excised window, the contour keeps distance more than `ε` from the arc
point. -/
private lemma lt_norm_sub_arc_of_far_right (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hδ : 0 < δ)
    (h2sin : 2 * Real.sin (δ * (Real.pi / 12)) = ε)
    (hε₂ : ε < w.re + 1 / 2) (hεc : ε < H - 1) (hs : s ∈ Ioo (t₀ + δ) (5 : ℝ)) :
    ε < ‖fdBoundary H s - w‖ := by
  have him1 : w.im ≤ 1 := by
    rw [← hw]
    exact im_fdBoundary_arc_le H ⟨ht₀.1.le, ht₀.2.le⟩
  rcases le_or_gt s 3 with h3 | h3
  · rw [← hw, ← h2sin]
    refine lt_norm_sub_arc_of_far ⟨by linarith [hs.1, ht₀.1], h3⟩ ⟨ht₀.1.le, ht₀.2.le⟩
      hδ ?_
    rw [abs_of_pos (by linarith [hs.1] : (0 : ℝ) < s - t₀)]
    linarith [hs.1]
  · rcases le_or_gt s 4 with h4 | h4
    · have hr : (fdBoundary H s - w).re = -(1 / 2) - w.re := by
        rw [Complex.sub_re, re_fdBoundarySegment4 H ⟨h3.le, h4⟩]
      calc ε < w.re + 1 / 2 := hε₂
        _ ≤ |(fdBoundary H s - w).re| := by
          rw [hr, abs_sub_comm, sub_neg_eq_add]
          exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_re_le_norm _
    · have hi : (fdBoundary H s - w).im = H - w.im := by
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, hs.2.le⟩]
      calc ε < H - w.im := by linarith
        _ ≤ |(fdBoundary H s - w).im| := by rw [hi]; exact le_abs_self _
        _ ≤ ‖fdBoundary H s - w‖ := Complex.abs_im_le_norm _

/-- **The excision collapse at an arc point**: for small `ε`, the `ε`-excised index
integrand of the boundary contour about `w` is interval integrable, and its integral is
exactly `-πi - 2·arcsin(ε/2)·i` — the value of the telescope at the matched half-width. -/
private lemma truncated_integral_spec_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 1 / 2) (him : 0 < w.im) (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3)
    (hw : fdBoundary H t₀ = w) (hε : 0 < ε)
    (hεl : ε < 2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
    (hεr : ε < 2 * Real.sin ((3 - t₀) * (Real.pi / 12)))
    (hε₁ : ε < 1 / 2 - w.re) (hε₂ : ε < w.re + 1 / 2) (hεc : ε < H - 1) :
    IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
    ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
        then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
      -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨hδ0, hδl, hδr, h2sin⟩ := arcExcisionHalfWidth_spec ht₀ hε hεl hεr
  set δ := fdBoundaryArcExcisionHalfWidth ε with hδ_def
  have hw0 : w ≠ 0 := fun h ↦ by rw [h, norm_zero] at hnorm; norm_num at hnorm
  obtain ⟨hint, hval⟩ := truncated_integral_spec_of_slit_branch (c := w⁻¹)
    (inv_ne_zero hw0) (by linarith [ht₀.1]) hδ0 (by linarith [ht₀.2])
    (fun t ht htw ↦ slit_branch_arc hH hnorm him ht (fdBoundary_ne_arc hH hre ht₀ hw
      fun h ↦ htw (by rw [h]; exact ⟨by linarith, by linarith⟩)))
    (fun s hs ↦ lt_norm_sub_arc_of_far_left ht₀ hw hδ0 h2sin hε₁ hs)
    (fun s hs ↦ lt_norm_sub_arc_of_far_right ht₀ hw hδ0 h2sin hε₂ hεc hs)
    (fun s hs ↦ by
      rw [← hw, ← h2sin]
      exact norm_sub_arc_le_of_near ⟨by linarith [hs.1, ht₀.1], by linarith [hs.2, ht₀.2]⟩
        ⟨ht₀.1.le, ht₀.2.le⟩ (by linarith [ht₀.1, ht₀.2])
        (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  refine ⟨hint, ?_⟩
  rw [hval, ← hw, log_sub_log_arc ⟨ht₀.1.le, ht₀.2.le⟩ hδ0 (by linarith [ht₀.1])
    (by linarith [ht₀.2]),
    show δ * (Real.pi / 6) = 2 * Real.arcsin (ε / 2) by
      rw [hδ_def, fdBoundaryArcExcisionHalfWidth_def]; field_simp; ring]
  push_cast
  ring

/-- The excised arc values converge to `-πi` as the excision radius shrinks. -/
private lemma tendsto_neg_pi_sub_arcsin :
    Tendsto (fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
        ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I) (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have hc : Continuous fun ε : ℝ ↦ -(Real.pi : ℂ) * Complex.I -
      ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I := by
    refine continuous_const.sub ((Complex.continuous_ofReal.comp ?_).mul continuous_const)
    exact continuous_const.mul (Real.continuous_arcsin.comp (continuous_id.div_const 2))
  simpa [Real.arcsin_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The five distance clearances of an arc point are simultaneously positive. -/
private lemma arc_min_radius_pos (hH : 1 < H) (hre : |w.re| < 1 / 2)
    (ht₀ : t₀ ∈ Ioo (1 : ℝ) 3) :
    0 < min (min (2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
        (2 * Real.sin ((3 - t₀) * (Real.pi / 12))))
      (min (1 / 2 - w.re) (min (w.re + 1 / 2) (H - 1))) := by
  have hπ := Real.pi_pos
  have habs := abs_lt.mp hre
  refine lt_min (lt_min ?_ ?_)
    (lt_min (by linarith [habs.2]) (lt_min (by linarith [habs.1]) (by linarith)))
  · exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [ht₀.1]) (by nlinarith [ht₀.1, ht₀.2]))
  · exact mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [ht₀.2]) (by nlinarith [ht₀.1, ht₀.2]))

/-- **The principal value at an arc point**: the Cauchy principal value of the index
integrand of the boundary contour about a point of the open unit arc is `-πi` — half a
clockwise turn, as the contour passes smoothly through `w` along the arc. -/
theorem hasCauchyPVAt_fdBoundary_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 2⁻¹) (him : 0 < w.im) :
    Contour.HasCauchyPVAt (fdBoundary H) 0 5 (fun z ↦ (z - w)⁻¹) w
      (-(Real.pi : ℂ) * Complex.I) := by
  rw [← one_div] at hre
  obtain ⟨t₀, ht₀, hw⟩ := exists_arc_param (H := H) hnorm hre him
  set b := min (min (2 * Real.sin ((t₀ - 1) * (Real.pi / 12)))
      (2 * Real.sin ((3 - t₀) * (Real.pi / 12))))
    (min (1 / 2 - w.re) (min (w.re + 1 / 2) (H - 1))) with hb_def
  have hb : 0 < b := arc_min_radius_pos hH hre ht₀
  have hIoo : Ioo (0 : ℝ) b ∈ 𝓝[>] (0 : ℝ) := by
    rw [← Ioi_inter_Iio]
    exact inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hb))
  have hspec : ∀ ε ∈ Ioo (0 : ℝ) b,
      IntervalIntegrable (fun t ↦ if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) volume 0 5 ∧
      ∫ t in (0 : ℝ)..5, (if ε < ‖fdBoundary H t - w‖
          then (fdBoundary H t - w)⁻¹ * deriv (fdBoundary H) t else 0) =
        -(Real.pi : ℂ) * Complex.I - ((2 * Real.arcsin (ε / 2) : ℝ) : ℂ) * Complex.I :=
    fun ε hε ↦ truncated_integral_spec_arc hH hnorm hre him ht₀ hw hε.1
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _)))
      (hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _))))
      (hε.2.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _))))
  refine Contour.hasCauchyPVAt_iff.mpr ⟨?_, ?_⟩
  · filter_upwards [hIoo] with ε hε
    exact (hspec ε hε).1
  · refine Tendsto.congr' ?_ tendsto_neg_pi_sub_arcsin
    filter_upwards [hIoo] with ε hε
    exact ((hspec ε hε).2).symm

/-- **The winding number of the boundary contour at an arc point is `-1/2`**: the point sits
on the open unit arc, and the principal-value normalization sees exactly half a clockwise
turn. -/
@[simp]
theorem windingNumber_fdBoundary_arc (hH : 1 < H) (hnorm : ‖w‖ = 1)
    (hre : |w.re| < 2⁻¹) (him : 0 < w.im) :
    Contour.windingNumber (fdBoundary H) 0 5 w = -(1 / 2 : ℂ) := by
  rw [Contour.windingNumber_eq_of_hasCauchyPVAt
    (hasCauchyPVAt_fdBoundary_arc hH hnorm hre him)]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end ModularForm

end TauCeti

end
