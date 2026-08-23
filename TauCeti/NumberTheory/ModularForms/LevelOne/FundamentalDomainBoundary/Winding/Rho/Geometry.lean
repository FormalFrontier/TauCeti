/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Topology.Circle.Metric

/-!
# Distance of the boundary contour from `ρ`

The geometry of the shifted contour `t ↦ fdBoundary H t - ρ` about the corner `ρ` at
parameter `t = 3`: the chord distance along the arc, the purely imaginary linear form
along the left vertical, the norm lower bounds on the far pieces, the slit-plane
confinement of every piece, and the exact polar forms and principal logarithms of the
shifted contour beside the corner. The corner joins the arc to the vertical at the
interior angle `π/3`, which is exactly the gap between the two one-sided argument limits
`π/6` and `π/2` — the source of the winding value `-1/6` at `ρ`.

## Main declarations

* `TauCeti.ModularForm.norm_fdBoundary_sub_rho_arc` (the chord distance).
* `TauCeti.ModularForm.fdBoundary_sub_rho_of_mem_Icc_three_four` (the linear form).
* `TauCeti.ModularForm.log_fdBoundary_three_sub_sub_rho`,
  `TauCeti.ModularForm.log_fdBoundary_three_add_sub_rho` (the endpoint logarithms).

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Rho.lean`) this file ports onto
  the current Mathlib pin.
-/

public section

open Complex Set

namespace TauCeti

namespace ModularForm

variable {H δ t : ℝ}

/-- The corner `ρ` is the unit-circle point of angle `2π/3`. -/
private lemma rho_eq_exp :
    (UpperHalfPlane.ρ : ℂ) = Complex.exp (((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I) := by
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  refine Complex.ext ?_ ?_
  · rw [Complex.exp_ofReal_mul_I_re, h23, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num [UpperHalfPlane.ρ]
  · rw [Complex.exp_ofReal_mul_I_im, h23, Real.sin_pi_sub, Real.sin_pi_div_three]
    exact rho_im

/-- On the arc the distance from `ρ` is the chord distance: `2·sin(|t - 3|·π/12)` up to
the absolute value inside the sine. -/
theorem norm_fdBoundary_sub_rho_arc (H : ℝ) (ht : t ∈ Icc (1 : ℝ) 3) :
    ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ = 2 * |Real.sin ((t - 3) * (Real.pi / 12))| := by
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ht
  have hρ : (UpperHalfPlane.ρ : ℂ) = circleMap 0 1 (2 * Real.pi / 3) := by
    rw [circleMap_zero, Complex.ofReal_one, one_mul]
    exact rho_eq_exp
  rw [← Complex.dist_eq, hcurve, hρ, dist_circleMap_eq_two_mul_abs_sin,
    (by ring : ((t + 1) * (Real.pi / 6) - 2 * Real.pi / 3) / 2 = (t - 3) * (Real.pi / 12))]
  norm_num

/-- On the left vertical the shifted contour is the purely imaginary linear form
`(t - 3)·(H - √3/2)·i`. -/
theorem fdBoundary_sub_rho_of_mem_Icc_three_four (H : ℝ) (ht : t ∈ Icc (3 : ℝ) 4) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) =
      (((t - 3) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
  rw [eqOn_fdBoundarySegment4 H ht, fdBoundarySegment4_apply, AffineMap.lineMap_apply]
  refine Complex.ext ?_ ?_
  · simp [UpperHalfPlane.ρ, Complex.real_smul]
  · simp [UpperHalfPlane.ρ, Complex.real_smul]

/-- On the right vertical the contour keeps distance at least `1` from `ρ`: the real parts differ
by exactly `1`. -/
theorem norm_fdBoundary_sub_rho_segment1 (H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    1 ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have hre : (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).re = 1 := by
    rw [Complex.sub_re, re_fdBoundarySegment1 H ht]
    norm_num [UpperHalfPlane.ρ]
  have h1 : |(fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).re| ≤
      ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := Complex.abs_re_le_norm _
  rw [hre] at h1
  simpa using h1

/-- On the ceiling the contour keeps distance at least `|H - √3/2|` from `ρ`: the heights
differ by exactly `H - √3/2`. The absolute value is what the height difference actually
gives, and it is the only form with content below the corner row, where `H - √3/2 < 0`
makes the signed bound vacuous. -/
theorem norm_fdBoundary_sub_rho_segment5 (ht : t ∈ Icc (4 : ℝ) 5) :
    |H - Real.sqrt 3 / 2| ≤ ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := by
  have him : (fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rw [Complex.sub_im, im_fdBoundarySegment5 H ht, rho_im]
  have h1 : |(fdBoundary H t - (UpperHalfPlane.ρ : ℂ)).im| ≤
      ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ := Complex.abs_im_le_norm _
  exact him ▸ h1

/-- Right of the corner column the shifted contour has real part `1`: slit plane. -/
theorem fdBoundary_sub_rho_mem_slitPlane_of_le_one (H : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [Complex.sub_re, re_fdBoundarySegment1 H ht]
  norm_num [UpperHalfPlane.ρ]

/-- Before the corner the arc stays right of the corner column: the real part of the
shifted contour is `cos((t+1)·π/6) + 1/2 > 0`, so it lies in the slit plane. -/
theorem fdBoundary_sub_rho_arc_mem_slitPlane_of_lt_three (H : ℝ) (ht1 : 1 ≤ t)
    (ht3 : t < 3) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have hcurve : fdBoundary H t = circleMap 0 1 ((t + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨ht1, ht3.le⟩
  rw [Complex.sub_re, hcurve, circleMap_zero_re, one_mul]
  have hcos : Real.cos (2 * Real.pi / 3) < Real.cos ((t + 1) * (Real.pi / 6)) := by
    refine Real.strictAntiOn_cos ⟨by positivity, by nlinarith [Real.pi_pos]⟩
      ⟨by positivity, by nlinarith [Real.pi_pos]⟩ (by nlinarith [Real.pi_pos])
  have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three] at hcos
  have hrho : ((UpperHalfPlane.ρ : ℂ)).re = -(1 / 2) := by
    norm_num [UpperHalfPlane.ρ]
  rw [hrho]
  linarith

/-- Above the corner the left vertical is purely imaginary of positive height: slit
plane. -/
theorem fdBoundary_sub_rho_mem_slitPlane_of_three_lt (hH : Real.sqrt 3 / 2 < H)
    (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
  rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨ht3.le, ht4⟩]
  have him : ((((t - 3) * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I).im =
      (t - 3) * (H - Real.sqrt 3 / 2) := by
    simp
  rw [him]
  positivity

/-- On the ceiling the shifted contour has height `H - √3/2 > 0`: slit plane. -/
theorem fdBoundary_sub_rho_mem_slitPlane_of_mem_Icc_four_five (hH : Real.sqrt 3 / 2 < H)
    (ht : t ∈ Icc (4 : ℝ) 5) :
    fdBoundary H t - (UpperHalfPlane.ρ : ℂ) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
  rw [Complex.sub_im, im_fdBoundarySegment5 H ht, rho_im]
  positivity

/-- The polar form of the shifted contour just before the corner. -/
private lemma fdBoundary_three_sub_sub_rho_eq (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    fdBoundary H (3 - δ) - (UpperHalfPlane.ρ : ℂ) =
      ((2 * Real.sin (δ * (Real.pi / 12)) : ℝ) : ℂ) *
        Complex.exp (((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I) := by
  have hI : Complex.I = Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I.symm
  have hcurve : fdBoundary H (3 - δ) = circleMap 0 1 ((3 - δ + 1) * (Real.pi / 6)) :=
    eqOn_fdBoundary_arc H ⟨by linarith, by linarith⟩
  rw [hcurve, circleMap_zero, Complex.ofReal_one, one_mul, rho_eq_exp,
    exp_mul_I_sub_exp_mul_I,
    (by ring : ((3 - δ + 1) * (Real.pi / 6) - 2 * Real.pi / 3) / 2 = -(δ * (Real.pi / 12))),
    (by ring : ((3 - δ + 1) * (Real.pi / 6) + 2 * Real.pi / 3) / 2 =
      Real.pi / 2 + (Real.pi / 6 - δ * (Real.pi / 12))),
    Real.sin_neg]
  have hsplit : ((Real.pi / 2 + (Real.pi / 6 - δ * (Real.pi / 12)) : ℝ) : ℂ) * Complex.I =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I +
        ((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, ← hI]
  push_cast
  -- The two factors of `I` are separated by the exponential, so `Complex.I_mul_I` has no
  -- `I * I` to match; `ring_nf` collects them into `I ^ 2` first, and the squaring lemma
  -- supplies the value `ring` cannot know.
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The principal logarithm of the shifted contour just before the corner. -/
theorem log_fdBoundary_three_sub_sub_rho (H : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    Complex.log (fdBoundary H (3 - δ) - (UpperHalfPlane.ρ : ℂ)) =
      ((Real.log (2 * Real.sin (δ * (Real.pi / 12))) : ℝ) : ℂ) +
        ((Real.pi / 6 - δ * (Real.pi / 12) : ℝ) : ℂ) * Complex.I := by
  have hsin_pos : 0 < Real.sin (δ * (Real.pi / 12)) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  rw [fdBoundary_three_sub_sub_rho_eq H hδ hδ2,
    Complex.log_ofReal_mul (by linarith) (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; nlinarith [Real.pi_pos]) (by simp; nlinarith [Real.pi_pos])]

/-- The principal logarithm of the shifted contour just after the corner. -/
theorem log_fdBoundary_three_add_sub_rho (hH : Real.sqrt 3 / 2 < H) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1) :
    Complex.log (fdBoundary H (3 + δ) - (UpperHalfPlane.ρ : ℂ)) =
      ((Real.log (δ * (H - Real.sqrt 3 / 2)) : ℝ) : ℂ) +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
  have heval : fdBoundary H (3 + δ) - (UpperHalfPlane.ρ : ℂ) =
      ((δ * (H - Real.sqrt 3 / 2) : ℝ) : ℂ) * Complex.I := by
    rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨by linarith, by linarith⟩]
    norm_num
  rw [heval, Complex.log_ofReal_mul (by positivity) Complex.I_ne_zero, Complex.log_I,
    Complex.ofReal_div, Complex.ofReal_ofNat]


/-- The contour passes through `ρ` only at the corner `t = 3`. -/
theorem eq_three_of_fdBoundary_eq_rho (hH : H ≠ Real.sqrt 3 / 2) (ht : t ∈ Icc (0 : ℝ) 5)
    (heq : fdBoundary H t = (UpperHalfPlane.ρ : ℂ)) : t = 3 := by
  have h0 : ‖fdBoundary H t - (UpperHalfPlane.ρ : ℂ)‖ = 0 := by
    rw [heq]
    simp
  rcases le_or_gt t 1 with h1 | h1
  · have := norm_fdBoundary_sub_rho_segment1 H ⟨ht.1, h1⟩
    rw [h0] at this
    norm_num at this
  · rcases le_or_gt t 3 with h3 | h3
    · rw [norm_fdBoundary_sub_rho_arc H ⟨h1.le, h3⟩] at h0
      have hsin : Real.sin ((t - 3) * (Real.pi / 12)) = 0 :=
        abs_eq_zero.mp (by linarith)
      have habs : |t - 3| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      obtain ⟨hb1, hb2⟩ := abs_le.mp habs
      have harg : (t - 3) * (Real.pi / 12) = 0 :=
        (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])).mp hsin
      rcases mul_eq_zero.mp harg with h | h
      · linarith
      · exact absurd h (by positivity)
    · rcases le_or_gt t 4 with h4 | h4
      · rw [fdBoundary_sub_rho_of_mem_Icc_three_four H ⟨h3.le, h4⟩, norm_mul,
          Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_eq_zero] at h0
        rcases mul_eq_zero.mp h0 with h | h
        · linarith
        · exact absurd (by linarith) hH
      · have hz : fdBoundary H t - (UpperHalfPlane.ρ : ℂ) = 0 := norm_eq_zero.mp h0
        have him := congrArg Complex.im hz
        rw [Complex.sub_im, im_fdBoundarySegment5 H ⟨h4.le, ht.2⟩, rho_im,
          Complex.zero_im] at him
        exact absurd (by linarith) hH

end ModularForm

end TauCeti

end
