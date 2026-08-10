/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Topology.Circle.Metric

/-!
# The geometry of the shifted contour at `i`

The shifted contour `t ↦ fdBoundary H t - i` about the elliptic point `i` at parameter
`t = 2`: the chord distance along the arc, the norm lower bounds on the far pieces, the
slit-plane confinement on either side of the arc top, the left-vertical height-`1`
crossing where the shifted contour meets the branch cut, the uniqueness of the crossing
time, and the exact endpoint logarithms beside the arc top.

## Main declarations

* `TauCeti.ModularForm.norm_fdBoundary_sub_I_arc` (the chord distance).
* `TauCeti.ModularForm.leftVerticalCrossingI` (the height-`1` crossing parameter).
* `TauCeti.ModularForm.eq_two_of_fdBoundary_eq_I` (crossing-time uniqueness).
* `TauCeti.ModularForm.log_fdBoundary_two_sub_sub_I_sub_log_fdBoundary_two_add_sub_I`
  (the symmetric endpoint log difference).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/I.lean`) this file ports onto
  the current Mathlib pin.
* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997.
-/

public section

open Complex Set

namespace TauCeti

namespace ModularForm

variable {H t : ℝ}



/-- On the arc the distance from `i` is the chord distance: `2·sin(|t - 2|·π/12)` up to
the absolute value inside the sine. -/
theorem norm_fdBoundary_sub_I_arc (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - Complex.I‖ = 2 * |Real.sin ((t - 2) * (Real.pi / 12))| := by
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ht
  have hI : Complex.I = circleMap 0 1 (Real.pi / 2) := by
    rw [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [← Complex.dist_eq, hcurve, hI, dist_circleMap_eq_two_mul_abs_sin,
    (by ring : ((t + 1) * (Real.pi / 6) - Real.pi / 2) / 2 = (t - 2) * (Real.pi / 12))]
  norm_num


/-- Left of the crossing the shifted contour stays in the slit plane through its
positive real part. -/
theorem fdBoundary_sub_I_mem_slitPlane_of_lt_two (H : ℝ) (ht : t ∈ Ico (0 : ℝ) 2) :
    fdBoundary H t - Complex.I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [Complex.sub_re, Complex.I_re, sub_zero, re_fdBoundary_segment1 H ⟨ht.1, ht1⟩]
    norm_num
  · have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
      eqOn_fdBoundary_arc H ⟨ht1.le, by linarith [ht.2]⟩
    rw [Complex.sub_re, Complex.I_re, sub_zero, hcurve, circleMap_zero_re, one_mul]
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · nlinarith [Real.pi_pos, ht.1]
    · nlinarith [Real.pi_pos, ht.2]

/-- Right of the crossing, on the arc, the shifted contour stays in the slit plane
through its negative imaginary part. -/
theorem fdBoundary_sub_I_mem_slitPlane_of_two_lt (H : ℝ) (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary H t - Complex.I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨by linarith, ht3⟩
  rw [Complex.sub_im, Complex.I_im, hcurve, circleMap_zero_im, one_mul]
  have hlt : Real.sin ((t + 1) * (Real.pi / 6)) < 1 := by
    have hθ1 : Real.pi / 2 < (t + 1) * (Real.pi / 6) := by nlinarith [Real.pi_pos]
    have hθ2 : (t + 1) * (Real.pi / 6) < Real.pi := by nlinarith [Real.pi_pos]
    have hcos := Real.cos_neg_of_pi_div_two_lt_of_lt hθ1 (by linarith [Real.pi_pos])
    by_contra hge
    push Not at hge
    have := le_antisymm (Real.sin_le_one _) hge
    nlinarith [Real.sin_sq_add_cos_sq ((t + 1) * (Real.pi / 6))]
  linarith

/-- On the right vertical the contour keeps distance at least `1/2` from `i`: its real part
is constantly `1/2`. -/
theorem norm_fdBoundary_sub_I_segment1 (H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 2 ≤ ‖fdBoundary H t - Complex.I‖ := by
  have hre : (fdBoundary H t - Complex.I).re = 1 / 2 := by
    rw [Complex.sub_re, Complex.I_re, sub_zero, re_fdBoundary_segment1 H ht]
  calc (1 : ℝ) / 2 = |(fdBoundary H t - Complex.I).re| := by rw [hre]; norm_num
    _ ≤ ‖fdBoundary H t - Complex.I‖ := Complex.abs_re_le_norm _

/-- On the left vertical the contour keeps distance at least `1/2` from `i`: its real part
is constantly `-1/2`. -/
theorem norm_fdBoundary_sub_I_segment4 (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    1 / 2 ≤ ‖fdBoundary H t - Complex.I‖ := by
  have hre : (fdBoundary H t - Complex.I).re = -(1 / 2) := by
    rw [Complex.sub_re, Complex.I_re, sub_zero, re_fdBoundary_segment4 H ht]
  calc (1 : ℝ) / 2 = |(fdBoundary H t - Complex.I).re| := by rw [hre]; norm_num
    _ ≤ ‖fdBoundary H t - Complex.I‖ := Complex.abs_re_le_norm _

/-- On the ceiling the contour keeps distance at least `|H - 1|` from `i`: its height
is constantly `H`. -/
theorem norm_fdBoundary_sub_I_segment5 (H : ℝ) (ht : t ∈ Icc (4 : ℝ) 5) :
    |H - 1| ≤ ‖fdBoundary H t - Complex.I‖ := by
  have him : (fdBoundary H t - Complex.I).im = H - 1 := by
    rw [Complex.sub_im, Complex.I_im, im_fdBoundary_segment5 H ht]
  calc |H - 1| = |(fdBoundary H t - Complex.I).im| := by rw [him]
    _ ≤ ‖fdBoundary H t - Complex.I‖ := Complex.abs_im_le_norm _


/-- The parameter on the left vertical where, for `1 < H`, the contour crosses height
`1`: the imaginary part of `fdBoundary H t - i` changes sign there. For `H ≤ 1` the
algebraic formula does not represent a crossing: the left vertical then never reaches
height `1`, the value can leave the parameter interval `[3, 4]`, and at `H = √3/2` the
denominator vanishes. -/
noncomputable def leftVerticalCrossingI (H : ℝ) : ℝ :=
  3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

/-- The corner row lies strictly below `1`. -/
private lemma sqrt_three_div_two_lt_one : Real.sqrt 3 / 2 < 1 := by
  have h : Real.sqrt 3 < 2 := by
    nlinarith [Real.sq_sqrt (by positivity : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
  linarith

/-- The crossing parameter lies right of the corner. -/
theorem three_lt_leftVerticalCrossingI (hH : Real.sqrt 3 / 2 < H) :
    3 < leftVerticalCrossingI H := by
  have h_den : 0 < H - Real.sqrt 3 / 2 := by linarith
  have := div_pos (by linarith [sqrt_three_div_two_lt_one] : 0 < 1 - Real.sqrt 3 / 2)
    h_den
  rw [leftVerticalCrossingI]
  linarith

/-- The crossing parameter lies below the ceiling corner. -/
theorem leftVerticalCrossingI_lt_four (hH : 1 < H) : leftVerticalCrossingI H < 4 := by
  have h_den : 0 < H - Real.sqrt 3 / 2 := by linarith [sqrt_three_div_two_lt_one]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 := by
    rw [div_lt_one h_den]
    linarith
  rw [leftVerticalCrossingI]
  linarith

/-- The crossing parameter does not exceed the ceiling corner; at `H = 1` it reaches it. -/
theorem leftVerticalCrossingI_le_four (hH : 1 ≤ H) : leftVerticalCrossingI H ≤ 4 := by
  have h_den : 0 < H - Real.sqrt 3 / 2 := by linarith [sqrt_three_div_two_lt_one]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ≤ 1 := by
    rw [div_le_one h_den]
    linarith
  rw [leftVerticalCrossingI]
  linarith

/-- The imaginary part of the shifted contour vanishes at the crossing parameter. At `H = 1`
the crossing sits at the ceiling corner `t = 4` and the identity still holds. -/
theorem im_fdBoundary_sub_I_leftVerticalCrossingI (hH : 1 ≤ H) :
    (fdBoundary H (leftVerticalCrossingI H) - Complex.I).im = 0 := by
  have h_den : (H - Real.sqrt 3 / 2) ≠ 0 :=
    ne_of_gt (by linarith [sqrt_three_div_two_lt_one])
  rw [Complex.sub_im, Complex.I_im,
    im_fdBoundary_of_le_four (three_lt_leftVerticalCrossingI
      (by linarith [sqrt_three_div_two_lt_one]))
      (leftVerticalCrossingI_le_four hH), leftVerticalCrossingI]
  have h2 : 2 * H - Real.sqrt 3 ≠ 0 := fun h ↦ h_den (by linarith)
  field_simp
  ring

/-- Below the crossing the shifted contour has negative imaginary part. -/
theorem im_fdBoundary_sub_I_neg_of_lt_crossing (hH : 1 < H) (ht3 : 3 < t)
    (ht0 : t < leftVerticalCrossingI H) : (fdBoundary H t - Complex.I).im < 0 := by
  have h_den : 0 < H - Real.sqrt 3 / 2 := by linarith [sqrt_three_div_two_lt_one]
  rw [Complex.sub_im, Complex.I_im,
    im_fdBoundary_of_le_four ht3 (by linarith [leftVerticalCrossingI_lt_four hH])]
  have h0 := im_fdBoundary_sub_I_leftVerticalCrossingI hH.le
  rw [Complex.sub_im, Complex.I_im,
    im_fdBoundary_of_le_four (three_lt_leftVerticalCrossingI
      (by linarith [sqrt_three_div_two_lt_one]))
      (leftVerticalCrossingI_lt_four hH).le] at h0
  nlinarith

/-- Above the crossing the shifted contour has positive imaginary part. -/
theorem im_fdBoundary_sub_I_pos_of_crossing_lt (hH : 1 < H)
    (ht0 : leftVerticalCrossingI H < t) (ht4 : t ≤ 4) :
    0 < (fdBoundary H t - Complex.I).im := by
  have h_den : 0 < H - Real.sqrt 3 / 2 := by linarith [sqrt_three_div_two_lt_one]
  rw [Complex.sub_im, Complex.I_im,
    im_fdBoundary_of_le_four (lt_trans (three_lt_leftVerticalCrossingI
      (by linarith [sqrt_three_div_two_lt_one])) ht0) ht4]
  have h0 := im_fdBoundary_sub_I_leftVerticalCrossingI hH.le
  rw [Complex.sub_im, Complex.I_im,
    im_fdBoundary_of_le_four (three_lt_leftVerticalCrossingI
      (by linarith [sqrt_three_div_two_lt_one]))
      (leftVerticalCrossingI_lt_four hH).le] at h0
  nlinarith


/-- At the corner `t = 3` the shifted contour has negative imaginary part: the corner
value is `ρ - i` of height `√3/2 - 1`. -/
theorem im_fdBoundary_sub_I_at_three_neg (H : ℝ) :
    (fdBoundary H 3 - Complex.I).im < 0 := by
  rw [Complex.sub_im, Complex.I_im, fdBoundary_apply_three]
  have := sqrt_three_div_two_lt_one
  have him : ((UpperHalfPlane.ρ : ℂ)).im = Real.sqrt 3 / 2 := by
    simp [UpperHalfPlane.ρ]
  rw [him]
  linarith


/-- The polar form of the shifted contour beside the arc top, with signed offset: radial
coefficient `2·sin(ε·π/12)` and argument `π + ε·π/12`, both signed with `ε`. The endpoint
forms on either side are its specializations. -/
private lemma fdBoundary_two_add_sub_I_polar (H : ℝ) {ε : ℝ} (hε : -1 ≤ ε) (hε1 : ε ≤ 1) :
    fdBoundary H (2 + ε) - Complex.I =
      ((2 * Real.sin (ε * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((Real.pi + ε * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have hI : Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I.symm
  have hcurve : fdBoundary H (2 + ε) = circleMap 0 1 ((2 + ε + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨by linarith, by linarith⟩
  conv_lhs => rw [hI, hcurve, circleMap_zero, Complex.ofReal_one, one_mul]
  rw [exp_mul_I_sub_exp_mul_I,
    (by ring : ((2 + ε + 1) * (Real.pi / 6) - Real.pi / 2) / 2 = ε * (Real.pi / 12)),
    (by ring : ((2 + ε + 1) * (Real.pi / 6) + Real.pi / 2) / 2 =
      Real.pi / 2 + ε * (Real.pi / 12))]
  have hsplit : ((Real.pi + ε * (Real.pi / 12) : ℝ) : ℂ) * Complex.I =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I +
        ((Real.pi / 2 + ε * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← hI]
  push_cast
  ring

/-- The polar form of the shifted contour just right of the arc top. -/
private lemma fdBoundary_two_sub_sub_I_eq (H : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    fdBoundary H (2 - δ) - Complex.I =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((-(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I) := by
  have harg : (2 : ℝ) + -δ = 2 - δ := by ring
  have hneg : -δ * (Real.pi / 12) = -(δ * (Real.pi / 12)) := by ring
  have hsplit : ((Real.pi + -(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I =
      ((Real.pi : ℝ) : ℂ) * Complex.I + ((-(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h := fdBoundary_two_add_sub_I_polar H (ε := -δ) (by linarith) (by linarith)
  rw [harg, hneg, Real.sin_neg, hsplit, Complex.exp_add, Complex.exp_pi_mul_I] at h
  rw [h]
  push_cast
  ring

/-- The polar form of the shifted contour just left of the arc top. -/
private lemma fdBoundary_two_add_sub_I_eq (H : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    fdBoundary H (2 + δ) - Complex.I =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((δ * (Real.pi / 12) - Real.pi : ℝ) : ℂ) * Complex.I) := by
  have hwrap : ((Real.pi + δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I =
      ((δ * (Real.pi / 12) - Real.pi : ℝ) : ℂ) * Complex.I +
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fdBoundary_two_add_sub_I_polar H (by linarith) hδ1, hwrap, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

/-- The half-angle sine of the excision half-width is positive. -/
private lemma sin_delta_pos (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < Real.sin (δ * (Real.pi / 12)) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

/-- The principal logarithm of the shifted contour just right of the arc top. -/
theorem log_fdBoundary_two_sub_sub_I (H : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Complex.log (fdBoundary H (2 - δ) - Complex.I) =
      ((Real.log (2 * Real.sin (δ * (Real.pi / 12))) : ℝ) : ℂ) +
        ((-(δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I := by
  rw [fdBoundary_two_sub_sub_I_eq H hδ hδ1,
    Complex.log_ofReal_mul (by linarith [sin_delta_pos hδ hδ1]) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [Real.pi_pos]) (by simp; nlinarith [Real.pi_pos])]

/-- The principal logarithm of the shifted contour just left of the arc top. -/
theorem log_fdBoundary_two_add_sub_I (H : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Complex.log (fdBoundary H (2 + δ) - Complex.I) =
      ((Real.log (2 * Real.sin (δ * (Real.pi / 12))) : ℝ) : ℂ) +
        ((δ * (Real.pi / 12) - Real.pi : ℝ) : ℂ) * Complex.I := by
  rw [fdBoundary_two_add_sub_I_eq H hδ hδ1,
    Complex.log_ofReal_mul (by linarith [sin_delta_pos hδ hδ1]) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [Real.pi_pos]) (by simp; nlinarith [Real.pi_pos])]

/-- **The symmetric log difference at the arc top**: the two endpoint logarithms of the
`δ`-excised arc differ by the pure phase `(π - δ·π/6)·i` — the chord norms agree, and only
the argument difference survives. -/
theorem log_fdBoundary_two_sub_sub_I_sub_log_fdBoundary_two_add_sub_I (H : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Complex.log (fdBoundary H (2 - δ) - Complex.I) -
      Complex.log (fdBoundary H (2 + δ) - Complex.I) =
      ((Real.pi - δ * (Real.pi / 6) : ℝ) : ℂ) * Complex.I := by
  rw [log_fdBoundary_two_sub_sub_I H hδ hδ1, log_fdBoundary_two_add_sub_I H hδ hδ1]
  push_cast
  ring


/-- The contour passes through `i` only at the arc top `t = 2`. -/
theorem eq_two_of_fdBoundary_eq_I (hH : H ≠ 1) (ht : t ∈ Icc (0 : ℝ) 5)
    (heq : fdBoundary H t = Complex.I) : t = 2 := by
  have h0 : ‖fdBoundary H t - Complex.I‖ = 0 := by
    rw [heq]
    simp
  rcases le_or_gt t 1 with h1 | h1
  · have := norm_fdBoundary_sub_I_segment1 H ⟨ht.1, h1⟩
    rw [h0] at this
    norm_num at this
  · rcases le_or_gt t 3 with h3 | h3
    · rw [norm_fdBoundary_sub_I_arc H ⟨h1.le, h3⟩] at h0
      have hsin : Real.sin ((t - 2) * (Real.pi / 12)) = 0 :=
        abs_eq_zero.mp (by linarith)
      have habs : |t - 2| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      obtain ⟨hb1, hb2⟩ := abs_le.mp habs
      have harg : (t - 2) * (Real.pi / 12) = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])).mp hsin
      rcases mul_eq_zero.mp harg with h | h
      · linarith
      · exact absurd h (by positivity)
    · rcases le_or_gt t 4 with h4 | h4
      · have := norm_fdBoundary_sub_I_segment4 H ⟨h3.le, h4⟩
        rw [h0] at this
        norm_num at this
      · have := norm_fdBoundary_sub_I_segment5 H ⟨h4.le, ht.2⟩
        rw [h0] at this
        exact absurd (le_antisymm this (abs_nonneg _))
          (abs_ne_zero.mpr (sub_ne_zero.mpr hH))

end ModularForm

end TauCeti

end
