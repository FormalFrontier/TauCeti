/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# A uniform derivative bound for the boundary contour

The derivative of the boundary contour is bounded at every parameter: off the three corners
each piece has a constant derivative or a scaled unit tangent, and at a corner the contour is
not differentiable — the one-sided chords disagree — so `deriv` takes its junk value `0`.
One constant therefore bounds the whole contour.

This is the growth input of the on-curve principal values at a fixed excision radius: on
the complement of an `ε`-ball around a point of the contour, the winding integrand
`(γ t - s)⁻¹ • deriv γ t` is bounded in norm by `ε⁻¹` times this bound. Integrability of that
integrand is a separate matter, and needs the derivative rather than the contour: it is
`TauCeti.Contour.intervalIntegrable_inv_sub_mul_deriv`, from the continuity of `γ`, its
avoidance of `s`, and the interval integrability of `deriv γ` — the last of which the bound
proved here does not by itself supply. The bound also degrades as `ε` shrinks, so it is not a
dominator for the excision limit itself, which rests on the symmetric cancellation at the
crossing.

## Main declarations

* `TauCeti.ModularForm.not_differentiableAt_fdBoundary_one`, `…_three`, `…_four`: the
  contour is not differentiable at its corners, with the `@[simp]` normal forms
  `TauCeti.ModularForm.deriv_fdBoundary_one`, `…_three`, `…_four` recording that `deriv`
  is `0` there.
* `TauCeti.ModularForm.exists_norm_deriv_fdBoundary_le`: a bound on `‖deriv (fdBoundary H)‖`
  valid at every parameter.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/OnCurvePV/Basic.lean`) this file ports onto the
  current Mathlib pin.
-/

public section

open Complex Set UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}

/-- The real part of the arc's tangent at a corner angle: `-(π/6)·sin θ`, negative wherever
the angle lies strictly between `0` and `π`. This is what distinguishes the arc's tangent
from the verticals' purely imaginary chords. -/
private lemma re_arc_tangent (θ : ℝ) :
    ((Real.pi / 6) • (circleMap 0 1 θ * Complex.I) : ℂ).re = -(Real.pi / 6 * Real.sin θ) := by
  simp only [circleMap, Complex.smul_re, zero_add, Complex.ofReal_one, one_mul,
    Complex.mul_re, Complex.I_re, Complex.I_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, smul_eq_mul]
  ring

/-- The one-sided derivative from the left at the ceiling corner: the left vertical's
chord. -/
private lemma hasDerivWithinAt_fdBoundary_four_left (H : ℝ) :
    HasDerivWithinAt (fdBoundary H) (-1 / 2 + H * Complex.I - (ρ : ℂ)) (Icc 3 4) 4 :=
  ((hasDerivAt_fdBoundarySegment4 H 4).hasDerivWithinAt).congr
    (fun t ht => eqOn_fdBoundarySegment4 H ht) (eqOn_fdBoundarySegment4 H (by norm_num))

/-- The one-sided derivative from the right at the ceiling corner: the ceiling's unit
horizontal. -/
private lemma hasDerivWithinAt_fdBoundary_four_right (H : ℝ) :
    HasDerivWithinAt (fdBoundary H) 1 (Icc 4 5) 4 :=
  ((hasDerivAt_fdBoundarySegment5 H 4).hasDerivWithinAt).congr
    (fun t ht => eqOn_fdBoundarySegment5 H ht) (eqOn_fdBoundarySegment5 H (by norm_num))

/-- **The contour is not differentiable at the ceiling corner.** The left vertical arrives
with a purely imaginary chord and the ceiling leaves with the unit horizontal, so no single
derivative serves both sides. -/
theorem not_differentiableAt_fdBoundary_four (H : ℝ) :
    ¬ DifferentiableAt ℝ (fdBoundary H) 4 := by
  intro hd
  have hL := hasDerivWithinAt_fdBoundary_four_left H
  have hR := hasDerivWithinAt_fdBoundary_four_right H
  have hLd : -1 / 2 + H * Complex.I - (ρ : ℂ) = deriv (fdBoundary H) 4 :=
    (uniqueDiffOn_Icc (by norm_num : (3 : ℝ) < 4) 4 (by norm_num)).eq_deriv _ hL
      (hd.hasDerivAt.hasDerivWithinAt)
  have hRd : (1 : ℂ) = deriv (fdBoundary H) 4 :=
    (uniqueDiffOn_Icc (by norm_num : (4 : ℝ) < 5) 4 (by norm_num)).eq_deriv _ hR
      (hd.hasDerivAt.hasDerivWithinAt)
  have hre : ((-1 / 2 + H * Complex.I - (ρ : ℂ)) : ℂ).re = (1 : ℂ).re := by
    rw [hLd, hRd]
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re] at hre
  norm_num [ρ] at hre

/-- The one-sided derivative from the left at the first corner: the right vertical's
chord. -/
private lemma hasDerivWithinAt_fdBoundary_one_left (H : ℝ) :
    HasDerivWithinAt (fdBoundary H) ((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)) (Icc 0 1) 1 :=
  ((hasDerivAt_fdBoundarySegment1 H 1).hasDerivWithinAt).congr
    (fun t ht => eqOn_fdBoundarySegment1 H ht) (eqOn_fdBoundarySegment1 H (by norm_num))

/-- **The contour is not differentiable at the first corner.** The right vertical arrives
with a purely imaginary chord and the arc leaves with a tangent of nonzero real part. -/
theorem not_differentiableAt_fdBoundary_one (H : ℝ) :
    ¬ DifferentiableAt ℝ (fdBoundary H) 1 := by
  intro hd
  have hLd : (ρ : ℂ) + 1 - (1 / 2 + H * Complex.I) = deriv (fdBoundary H) 1 :=
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 1 (by norm_num)).eq_deriv _
      (hasDerivWithinAt_fdBoundary_one_left H) (hd.hasDerivAt.hasDerivWithinAt)
  have hRd : (Real.pi / 6) • (circleMap 0 1 ((1 + 1) * (Real.pi / 6)) * Complex.I) =
      deriv (fdBoundary H) 1 :=
    (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 3) 1 (by norm_num)).eq_deriv _
      (hasDerivWithinAt_fdBoundary_arc (H := H) le_rfl le_rfl (by norm_num))
      (hd.hasDerivAt.hasDerivWithinAt)
  have hre : (((ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)) : ℂ).re =
      ((Real.pi / 6) • (circleMap 0 1 ((1 + 1) * (Real.pi / 6)) * Complex.I) : ℂ).re := by
    rw [hLd, hRd]
  have hangle : ((1 : ℝ) + 1) * (Real.pi / 6) = Real.pi / 3 := by ring
  rw [hangle, re_arc_tangent, Real.sin_pi_div_three] at hre
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re] at hre
  norm_num [ρ] at hre

/-- **The contour is not differentiable at the second corner.** The arc arrives with a
tangent of nonzero real part and the left vertical leaves with a purely imaginary chord. -/
theorem not_differentiableAt_fdBoundary_three (H : ℝ) :
    ¬ DifferentiableAt ℝ (fdBoundary H) 3 := by
  intro hd
  have hLd : (Real.pi / 6) • (circleMap 0 1 ((3 + 1) * (Real.pi / 6)) * Complex.I) =
      deriv (fdBoundary H) 3 :=
    (uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 3) 3 (by norm_num)).eq_deriv _
      (hasDerivWithinAt_fdBoundary_arc (H := H) le_rfl le_rfl (by norm_num))
      (hd.hasDerivAt.hasDerivWithinAt)
  have hRd : -1 / 2 + H * Complex.I - (ρ : ℂ) = deriv (fdBoundary H) 3 :=
    (uniqueDiffOn_Icc (by norm_num : (3 : ℝ) < 4) 3 (by norm_num)).eq_deriv _
      (((hasDerivAt_fdBoundarySegment4 H 3).hasDerivWithinAt).congr
        (fun t ht => eqOn_fdBoundarySegment4 H ht)
        (eqOn_fdBoundarySegment4 H (by norm_num)))
      (hd.hasDerivAt.hasDerivWithinAt)
  have hre : ((Real.pi / 6) • (circleMap 0 1 ((3 + 1) * (Real.pi / 6)) * Complex.I) : ℂ).re =
      ((-1 / 2 + H * Complex.I - (ρ : ℂ)) : ℂ).re := by
    rw [hLd, hRd]
  have hangle : ((3 : ℝ) + 1) * (Real.pi / 6) = 2 * Real.pi / 3 := by ring
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have hsplit : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [hsplit, Real.sin_pi_sub]
    exact Real.sin_pi_div_three
  rw [hangle, re_arc_tangent, hsin] at hre
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  norm_num [ρ] at hre

/-- The contour's derivative at the first corner is the junk value `0`. -/
@[simp]
theorem deriv_fdBoundary_one (H : ℝ) : deriv (fdBoundary H) 1 = 0 :=
  deriv_zero_of_not_differentiableAt (not_differentiableAt_fdBoundary_one H)

/-- The contour's derivative at the second corner is the junk value `0`. -/
@[simp]
theorem deriv_fdBoundary_three (H : ℝ) : deriv (fdBoundary H) 3 = 0 :=
  deriv_zero_of_not_differentiableAt (not_differentiableAt_fdBoundary_three H)

/-- The contour's derivative at the ceiling corner is the junk value `0`. -/
@[simp]
theorem deriv_fdBoundary_four (H : ℝ) : deriv (fdBoundary H) 4 = 0 :=
  deriv_zero_of_not_differentiableAt (not_differentiableAt_fdBoundary_four H)

/-- **A uniform bound on the contour's derivative.** Every parameter has
`‖deriv (fdBoundary H) t‖ ≤ ‖ρ + 1 - (1/2 + H·i)‖ + π/6 + ‖-1/2 + H·i - ρ‖ + 1`: off the
corners the derivative is one of the four piecewise values — the two vertical chords, the
arc's `π/6`-scaled unit tangent, and the ceiling's `1` — each bounded by one summand, and at
a corner the contour is not differentiable, so `deriv` takes its junk value `0` there.

The bound is an existential over a positive constant, the form its consumers use: at a fixed
excision radius they need only *some* bound on the contour's speed. -/
theorem exists_norm_deriv_fdBoundary_le (H : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, ‖deriv (fdBoundary H) t‖ ≤ M := by
  refine ⟨‖(ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)‖ + Real.pi / 6 +
    ‖-1 / 2 + H * Complex.I - (ρ : ℂ)‖ + 1, by positivity, fun t ↦ ?_⟩
  have hpi : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have hn1 : (0 : ℝ) ≤ ‖(ρ : ℂ) + 1 - (1 / 2 + H * Complex.I)‖ := norm_nonneg _
  have hn2 : (0 : ℝ) ≤ ‖-1 / 2 + H * Complex.I - (ρ : ℂ)‖ := norm_nonneg _
  rcases eq_or_ne t 1 with rfl | h1
  · rw [deriv_fdBoundary_one, norm_zero]
    linarith
  rcases eq_or_ne t 3 with rfl | h3
  · rw [deriv_fdBoundary_three, norm_zero]
    linarith
  rcases eq_or_ne t 4 with rfl | h4
  · rw [deriv_fdBoundary_four, norm_zero]
    linarith
  rcases lt_or_gt_of_ne h1 with hlt1 | hgt1
  · rw [deriv_fdBoundary_of_lt_one hlt1]
    nlinarith [hn1, hn2, hpi]
  rcases lt_or_gt_of_ne h3 with hlt3 | hgt3
  · rw [deriv_fdBoundary_of_mem_Ioo_one_three ⟨hgt1, hlt3⟩, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hpi, norm_mul, norm_circleMap_zero, abs_one, one_mul, norm_I, mul_one]
    linarith
  rcases lt_or_gt_of_ne h4 with hlt4 | hgt4
  · rw [deriv_fdBoundary_of_mem_Ioo_three_four ⟨hgt3, hlt4⟩]
    nlinarith [hn1, hn2, hpi]
  · rw [deriv_fdBoundary_of_gt_four hgt4, norm_one]
    linarith

end ModularForm

end TauCeti

end
