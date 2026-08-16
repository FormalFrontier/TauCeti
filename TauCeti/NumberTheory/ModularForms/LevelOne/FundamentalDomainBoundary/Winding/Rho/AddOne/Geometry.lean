/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Rho.Geometry

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic
import TauCeti.Topology.Circle.Metric

/-!
# Distance of the boundary contour from `ρ + 1`

The geometry of the shifted contour `t ↦ fdBoundary H t - (ρ + 1)` about the corner
`ρ + 1` at parameter `t = 1`: the purely imaginary linear form along the right vertical,
the chord distance along the arc, the norm lower bounds on the far pieces, the
closed-upper-half-plane confinement — and the exact endpoint logarithms beside the corner.

The confinement holds only once the ceiling clears the corner row, and the confinement
results accordingly carry `√3/2 ≤ H`. Under that hypothesis the shifted contour touches the
branch cut at `t = 3`, where its value is `-1`, but never crosses it; at the degenerate
height `H = √3/2` the whole left vertical degenerates to that point and lies on the cut
throughout. Below the corner row the claim fails outright: on the left vertical the shifted
contour is `-1 + (t - 3)(H - √3/2)i`, so for `H < √3/2` the imaginary part is negative
immediately after `t = 3` and the contour does cross the cut.

The corner joins the vertical to the arc at the interior
angle `π/3`, which is exactly the gap between the one-sided argument limits `π/2` and
`5π/6` — the source of the winding value `-1/6` at `ρ + 1`.

## Main declarations

* `TauCeti.ModularForm.rho_add_one_im` (the corner shares the row `Im = √3/2` with `ρ`).
* `TauCeti.ModularForm.fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one` (the linear form).
* `TauCeti.ModularForm.norm_fdBoundary_sub_rho_add_one_arc` (the chord distance) and
  `TauCeti.ModularForm.norm_fdBoundary_sub_rho_add_one_arc_le` (its monotonicity in the
  angular gap).
* `TauCeti.ModularForm.log_fdBoundary_one_sub_sub_rho_add_one`,
  `TauCeti.ModularForm.log_fdBoundary_one_add_sub_rho_add_one` (the endpoint logarithms).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/RhoPlusOne.lean`) this file
  ports onto the current Mathlib pin.
-/

public section

open Complex Set

namespace TauCeti

namespace ModularForm

variable {H δ t : ℝ}

/-- **The corner `ρ + 1` sits on the same row `Im = √3/2` as `ρ`**: the shift is by a real
number, which does not move the imaginary part.

Not `@[simp]`, for the same reason as `rho_im`: simp reaches `ρ.im` through
`Complex.add_im`, `UpperHalfPlane.coe_im` and `Complex.one_im` before this could fire. -/
theorem rho_add_one_im : ((UpperHalfPlane.ρ : ℂ) + 1).im = Real.sqrt 3 / 2 := by
  rw [Complex.add_im, rho_im, Complex.one_im, add_zero]

/-- The corner `ρ + 1` is the unit-circle point of angle `π/3`. -/
private lemma rho_add_one_eq_exp :
    (UpperHalfPlane.ρ : ℂ) + 1 = Complex.exp (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  refine Complex.ext ?_ ?_
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
    norm_num [UpperHalfPlane.ρ]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]
    exact rho_add_one_im

/-- The corner `ρ + 1` as a point of the unit circle traced by `circleMap`. -/
private lemma rho_add_one_eq_circleMap :
    (UpperHalfPlane.ρ : ℂ) + 1 = circleMap 0 1 (Real.pi / 3) := by
  rw [circleMap_zero, Complex.ofReal_one, one_mul]
  exact rho_add_one_eq_exp

/-- On the right vertical the shifted contour is the purely imaginary linear form
`(1 - t)·(H - √3/2)·i`. -/
theorem fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one (H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) =
      (((1 - t) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  rw [eqOn_fdBoundarySegment1 H ht, fdBoundarySegment1_apply, AffineMap.lineMap_apply]
  refine Complex.ext ?_ ?_
  · simp [UpperHalfPlane.ρ, Complex.real_smul]
    ring
  · simp [UpperHalfPlane.ρ, Complex.real_smul]
    ring

/-- On the arc the distance from `ρ + 1` is the chord distance: `2·sin(|t - 1|·π/12)`
up to the absolute value inside the sine. -/
theorem norm_fdBoundary_sub_rho_add_one_arc (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ =
      2 * |Real.sin ((t - 1) * (Real.pi / 12))| := by
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ht
  rw [← Complex.dist_eq, hcurve, rho_add_one_eq_circleMap, dist_circleMap_eq_two_mul_abs_sin,
    (by ring : ((t + 1) * (Real.pi / 6) - Real.pi / 3) / 2 = (t - 1) * (Real.pi / 12))]
  norm_num

/-- **Along the arc the chord to `ρ + 1` grows with the parameter.** A point of the arc at
parameter `t` is no further from the corner than the point at parameter `1 + δ` is, whose
chord is `2·sin(δ·π/12)`.

This is the generic monotonicity of a chord in the angular gap,
`TauCeti.dist_circleMap_le_dist_circleMap_of_abs_sub_le`, read along the arc, whose
parameter runs at `π/6` per unit; `δ ≤ 6` keeps the comparison point within half a turn of
the corner, where the chord is still increasing. -/
theorem norm_fdBoundary_sub_rho_add_one_arc_le (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) (hδ : δ ≤ 6)
    (hle : t - 1 ≤ δ) :
    ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ ≤ 2 * Real.sin (δ * (Real.pi / 12)) := by
  have hδ0 : 0 ≤ δ := le_trans (by linarith [ht.1]) hle
  have hgap : Real.pi / 3 + δ * (Real.pi / 6) - Real.pi / 3 = δ * (Real.pi / 6) := by ring
  have hchord : dist (circleMap 0 1 (Real.pi / 3 + δ * (Real.pi / 6)))
      (circleMap 0 1 (Real.pi / 3)) = 2 * Real.sin (δ * (Real.pi / 12)) := by
    rw [dist_circleMap_eq_two_mul_abs_sin,
      (by ring : (Real.pi / 3 + δ * (Real.pi / 6) - Real.pi / 3) / 2 = δ * (Real.pi / 12)),
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hδ0 (by positivity))
        (by nlinarith [Real.pi_pos]))]
    norm_num
  rw [← Complex.dist_eq, eqOn_fdBoundary_arc H ht, rho_add_one_eq_circleMap, ← hchord]
  refine dist_circleMap_le_dist_circleMap_of_abs_sub_le 0 1 ?_ ?_
  · rw [(by ring : (t + 1) * (Real.pi / 6) - Real.pi / 3 = (t - 1) * (Real.pi / 6)), hgap,
      abs_of_nonneg (mul_nonneg (by linarith [ht.1]) (by positivity)),
      abs_of_nonneg (mul_nonneg hδ0 (by positivity))]
    nlinarith [Real.pi_pos]
  · rw [hgap, abs_of_nonneg (mul_nonneg hδ0 (by positivity))]
    nlinarith [Real.pi_pos]

/-- On the left vertical the shifted contour is `-1` plus the imaginary linear form of the
`ρ`-shift, so its real part is constantly `-1` and it runs alongside the branch cut. Where the
ceiling misses the corner row the imaginary part vanishes only at `t = 3`, so the cut is met
there alone — above it when the ceiling clears the row, below it otherwise. At the degenerate
height `H = √3/2` the imaginary part vanishes identically and the whole segment is the point
`-1`, lying on the cut throughout. -/
theorem fdBoundary_sub_rho_add_one_of_mem_Icc_three_four (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) =
      -1 + (((t - 3) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  have hsplit : fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1) =
      fdBoundary H t - (UpperHalfPlane.ρ : ℂ) - 1 := by ring
  rw [hsplit, fdBoundary_sub_rho_of_mem_Icc_three_four H ht]
  ring

/-- On the left vertical the contour keeps distance at least `1` from `ρ + 1`: the real parts
differ by exactly `1`. -/
theorem norm_fdBoundary_sub_rho_add_one_segment4 (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    1 ≤ ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := by
  have hre : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).re = -1 := by
    rw [fdBoundary_sub_rho_add_one_of_mem_Icc_three_four H ht]
    simp
  have h1 : |(fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).re| ≤
      ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := Complex.abs_re_le_norm _
  rw [hre] at h1
  simpa using h1

/-- On the ceiling the contour keeps distance at least `|H - √3/2|` from `ρ + 1`. The
absolute value is what the height difference gives, and it is the only form with content
below the corner row, where `H - √3/2 < 0` makes the signed bound vacuous. -/
theorem norm_fdBoundary_sub_rho_add_one_segment5 (ht : t ∈ Icc (4 : ℝ) 5) :
    |H - Real.sqrt 3 / 2| ≤ ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := by
  have him : (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im = H - Real.sqrt 3 / 2 := by
    rw [Complex.sub_im, im_fdBoundarySegment5 H ht, rho_add_one_im]
  have h1 : |(fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im| ≤
      ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ := Complex.abs_im_le_norm _
  exact him ▸ h1

/-- Strictly inside the middle arc range, the sine stays strictly above `√3/2`. -/
private lemma sqrt_three_div_two_lt_sin {θ : ℝ} (h1 : Real.pi / 3 < θ)
    (h2 : θ < 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 < Real.sin θ := by
  rcases le_or_gt θ (Real.pi / 2) with hle | hgt
  · rw [← Real.sin_pi_div_three]
    exact Real.strictMonoOn_sin
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], hle⟩ h1
  · rw [← Real.sin_pi_div_three, ← Real.sin_pi_sub θ]
    exact Real.strictMonoOn_sin
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
      (by nlinarith [Real.pi_pos])

/-- On the arc the shifted contour stays in the closed upper half-plane. -/
theorem im_fdBoundary_sub_rho_add_one_arc_nonneg (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    0 ≤ (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im := by
  -- On the arc the contour does not depend on the height, so the corner-row bound already
  -- proved for a contour at the corner height transports to this one.
  have htransport : fdBoundary H t = fdBoundary (Real.sqrt 3 / 2) t := by
    rw [eqOn_fdBoundary_arc H ht, eqOn_fdBoundary_arc (Real.sqrt 3 / 2) ht]
  have ht05 : t ∈ Icc (0 : ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [Complex.sub_im, rho_add_one_im, htransport]
  linarith [sqrt_three_div_two_le_im_fdBoundary (H := Real.sqrt 3 / 2) le_rfl ht05]

/-- Strictly inside the arc the shifted contour has positive height. -/
theorem im_fdBoundary_sub_rho_add_one_arc_pos (H : ℝ) (ht1 : 1 < t) (ht3 : t < 3) :
    0 < (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im := by
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨ht1.le, ht3.le⟩
  rw [Complex.sub_im, hcurve, circleMap_zero_im, one_mul, rho_add_one_im]
  linarith [sqrt_three_div_two_lt_sin (θ := (t + 1) * (Real.pi / 6))
    (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])]

/-- The shifted contour stays in the closed upper half-plane over the whole parameter
range: the contour clears the corner row `√3/2`, which is the height of `ρ + 1`. -/
theorem im_fdBoundary_sub_rho_add_one_nonneg (hH : Real.sqrt 3 / 2 ≤ H)
    (ht : t ∈ Icc (0 : ℝ) 5) :
    0 ≤ (fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)).im := by
  rw [Complex.sub_im, rho_add_one_im]
  linarith [sqrt_three_div_two_le_im_fdBoundary hH ht]

/-- The polar form of the shifted contour just after the corner. -/
private lemma fdBoundary_one_add_sub_rho_add_one_eq (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    fdBoundary H (1 + δ) - ((UpperHalfPlane.ρ : ℂ) + 1) =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((5 * Real.pi / 6 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have hI : Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I.symm
  have hcurve : fdBoundary H (1 + δ) = circleMap 0 1 ((1 + δ + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨by linarith, by linarith⟩
  rw [hcurve, circleMap_zero, Complex.ofReal_one, one_mul, rho_add_one_eq_exp,
    exp_mul_I_sub_exp_mul_I,
    (by ring : ((1 + δ + 1) * (Real.pi / 6) - Real.pi / 3) / 2 = δ * (Real.pi / 12)),
    (by ring : ((1 + δ + 1) * (Real.pi / 6) + Real.pi / 3) / 2 =
      Real.pi / 3 + δ * (Real.pi / 12))]
  have hsplit : ((5 * Real.pi / 6 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I +
        ((Real.pi / 3 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← hI]
  push_cast
  ring

/-- The principal logarithm of the shifted contour just before the corner. -/
theorem log_fdBoundary_one_sub_sub_rho_add_one (hH : Real.sqrt 3 / 2 < H) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1) :
    Complex.log (fdBoundary H (1 - δ) - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      ((Real.log (δ * (H - Real.sqrt 3 / 2)) : ℝ) : ℂ) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have heval : fdBoundary H (1 - δ) - ((UpperHalfPlane.ρ : ℂ) + 1) =
      ((δ * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
    rw [fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one H ⟨by linarith, by linarith⟩]
    norm_num
  rw [heval, Complex.log_ofReal_mul (by positivity) Complex.I_ne_zero, Complex.log_I,
    Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The principal logarithm of the shifted contour just after the corner. -/
theorem log_fdBoundary_one_add_sub_rho_add_one (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    Complex.log (fdBoundary H (1 + δ) - ((UpperHalfPlane.ρ : ℂ) + 1)) =
      ((Real.log (2 * Real.sin (δ * (Real.pi / 12))) : ℝ) : ℂ) +
        ((5 * Real.pi / 6 + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
  have hsin_pos : 0 < Real.sin (δ * (Real.pi / 12)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [fdBoundary_one_add_sub_rho_add_one_eq H hδ hδ2,
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [Real.pi_pos]) (by simp; nlinarith [Real.pi_pos])]


/-- The contour passes through `ρ + 1` only at the corner `t = 1`. -/
theorem eq_one_of_fdBoundary_eq_rho_add_one (hH : H ≠ Real.sqrt 3 / 2) (ht : t ∈ Icc (0 : ℝ) 5)
    (heq : fdBoundary H t = (UpperHalfPlane.ρ : ℂ) + 1) : t = 1 := by
  have h0 : ‖fdBoundary H t - ((UpperHalfPlane.ρ : ℂ) + 1)‖ = 0 := by
    rw [heq]
    simp
  rcases le_or_gt t 1 with h1 | h1
  · rw [fdBoundary_sub_rho_add_one_of_mem_Icc_zero_one H ⟨ht.1, h1⟩, norm_mul,
      Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_eq_zero] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · linarith
    · exact absurd (by linarith) hH
  · rcases le_or_gt t 3 with h3 | h3
    · rw [norm_fdBoundary_sub_rho_add_one_arc H ⟨h1.le, h3⟩] at h0
      have hsin : Real.sin ((t - 1) * (Real.pi / 12)) = 0 :=
        abs_eq_zero.mp (by linarith)
      have habs : |t - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      obtain ⟨hb1, hb2⟩ := abs_le.mp habs
      have harg : (t - 1) * (Real.pi / 12) = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])).mp hsin
      rcases mul_eq_zero.mp harg with h | h
      · linarith
      · exact absurd h (by positivity)
    · rcases le_or_gt t 4 with h4 | h4
      · have := norm_fdBoundary_sub_rho_add_one_segment4 H ⟨h3.le, h4⟩
        rw [h0] at this
        norm_num at this
      · have him := congrArg Complex.im (norm_eq_zero.mp h0)
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, ht.2⟩, rho_add_one_im,
          Complex.zero_im] at him
        exact absurd (by linarith) hH

end ModularForm

end TauCeti

end
