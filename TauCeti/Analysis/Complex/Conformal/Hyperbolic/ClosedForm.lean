/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Closed forms for the hyperbolic distance on the unit disc

The hyperbolic (Poincaré) distance of `Conformal/Hyperbolic/Distance.lean` is defined as
`hyperbolicDist z w = Real.artanh (pseudoHyperbolicExpr z w)`, a reparametrisation of the
pseudo-hyperbolic expression `p = ‖(z - w) / (1 - conj w * z)‖`. That definition is the one that
makes the Schwarz--Pick contraction property and the triangle inequality easy, but it hides the
quantity behind an inverse hyperbolic tangent. This file evaluates the elementary functions of
`hyperbolicDist` in closed form, in terms of the three Euclidean quantities

* the numerator `‖z - w‖`,
* the Moebius denominator `‖1 - conj w * z‖`, and
* the product of hyperbolic defects `(1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)`.

Everything rests on the **Poincaré defect identity**
`‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)`
(`TauCeti.norm_sq_one_sub_conj_mul_sub_norm_sq_sub`), which says exactly that
`1 - p ^ 2 = (1 - ‖z‖ ^ 2) (1 - ‖w‖ ^ 2) / ‖1 - conj w * z‖ ^ 2`. Feeding that into Mathlib's
`Real.sinh_artanh`, `Real.cosh_artanh` and `Real.artanh_eq_half_log` turns the Moebius
denominator into the common factor that the quotient `p` and the defect `1 - p ^ 2` share, and it
cancels: what is left involves only `‖z - w‖`, `‖1 - conj w * z‖` and the defect product.

## Main results

* `TauCeti.one_sub_pseudoHyperbolicExpr_sq` and
  `TauCeti.sqrt_one_sub_pseudoHyperbolicExpr_sq` — the defect identity in the form the closed
  forms consume;
* `TauCeti.sinh_hyperbolicDist`, `TauCeti.cosh_hyperbolicDist`, `TauCeti.tanh_hyperbolicDist`,
  `TauCeti.exp_hyperbolicDist` — the four elementary functions of the hyperbolic distance;
* `TauCeti.cosh_two_mul_hyperbolicDist` — the double-angle form
  `cosh (2 d) = 1 + 2 ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2)(1 - ‖w‖ ^ 2))`, the identity usually quoted as
  *the* formula for the Poincaré distance;
* `TauCeti.hyperbolicDist_eq_half_log` and `TauCeti.hyperbolicDist_zero_right_eq_half_log` — the
  logarithmic form, in general and against the origin;
* `TauCeti.hyperbolicDist_le_iff_le_sinh` and `TauCeti.hyperbolicDist_le_div_sqrt` — the
  comparison with the Euclidean distance that the closed forms make available;
* `TauCeti.exists_mem_ball_lt_hyperbolicDist` — the disc has infinite hyperbolic diameter.

## Normalisation

`hyperbolicDist` is normalised to the infinitesimal metric `|dz| / (1 - |z| ^ 2)`, half the
curvature `-1` metric `2 |dz| / (1 - |z| ^ 2)`; this is the normalisation already fixed by
`Conformal/Hyperbolic/Distance.lean` and used throughout `Conformal/Poincare/`. Under the Cayley
transform it corresponds to *half* the distance that Mathlib's `UpperHalfPlane.dist` records on
the upper half-plane, so the statements below are the disc analogues of Mathlib's
`UpperHalfPlane.sinh_half_dist`, `UpperHalfPlane.cosh_half_dist`, `UpperHalfPlane.tanh_half_dist`,
`UpperHalfPlane.exp_half_dist` and `UpperHalfPlane.cosh_dist` — the half-distance formulas there
are the plain ones here. The Cayley transform itself is not used: the disc formulas are proved
directly from the defect identity, which is shorter than transporting the half-plane ones and
avoids the `im`-versus-defect bookkeeping.

This advances the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on `𝔻`"
(see `ConformalMapping/README.md`), completing the basic API of `hyperbolicDist` with the closed
forms that the geometric statements of `Conformal/Poincare/` are usually quoted in. As with the
rest of the L0--L3 conformal-mapping material it is coordinated with the upstream Mathlib RMT
effort leanprover-community/mathlib4#33505, which contains no Poincaré metric on the disc: should
a human-curated disc metric land in Mathlib, these formulas are to be refactored onto it.
-/

public section

namespace TauCeti

open _root_.Complex Metric Set
open scoped ComplexConjugate

variable {z w : ℂ}

private lemma one_sub_sq_norm_pos (hz : ‖z‖ < 1) : 0 < 1 - ‖z‖ ^ 2 := by
  nlinarith [norm_nonneg z]

private lemma defect_pos (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
  mul_pos (one_sub_sq_norm_pos hz) (one_sub_sq_norm_pos hw)

private lemma sqrt_defect_pos (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    0 < Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) :=
  Real.sqrt_pos.mpr (defect_pos hz hw)

private lemma norm_one_sub_conj_mul_pos (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
  norm_pos_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)

private lemma pseudoHyperbolicExpr_mem_Ioo (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w ∈ Ioo (-1 : ℝ) 1 :=
  ⟨by linarith [pseudoHyperbolicExpr_nonneg z w],
    pseudoHyperbolicExpr_lt_one_of_norm_lt_one hz hw⟩

/-- **The defect identity, squared form.** For two points of the open unit disc the deficiency
`1 - p ^ 2` of the pseudo-hyperbolic expression `p` is the product of the two hyperbolic defects
divided by the squared Moebius denominator. -/
theorem one_sub_pseudoHyperbolicExpr_sq (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - pseudoHyperbolicExpr z w ^ 2 =
      (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) / ‖1 - (starRingEnd ℂ) w * z‖ ^ 2 := by
  have hD : 0 < ‖1 - (starRingEnd ℂ) w * z‖ := norm_one_sub_conj_mul_pos hz hw
  have hid := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w
  rw [pseudoHyperbolicExpr_def, norm_div, div_pow]
  set D := ‖1 - (starRingEnd ℂ) w * z‖
  have hD0 : D ≠ 0 := hD.ne'
  field_simp
  linear_combination hid

/-- **The defect identity, square-root form.** The square root of `1 - p ^ 2` occurring in the
closed forms of `Real.sinh` and `Real.cosh` at `Real.artanh p`. -/
theorem sqrt_one_sub_pseudoHyperbolicExpr_sq (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.sqrt (1 - pseudoHyperbolicExpr z w ^ 2) =
      Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) / ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [one_sub_pseudoHyperbolicExpr_sq hz hw, Real.sqrt_div (defect_pos hz hw).le,
    Real.sqrt_sq (norm_nonneg _)]

/-- **The hyperbolic sine of the hyperbolic distance.** The disc analogue of Mathlib's
`UpperHalfPlane.sinh_half_dist`. -/
theorem sinh_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.sinh (hyperbolicDist z w) =
      ‖z - w‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  have hD : 0 < ‖1 - (starRingEnd ℂ) w * z‖ := norm_one_sub_conj_mul_pos hz hw
  have hS : 0 < Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := sqrt_defect_pos hz hw
  rw [hyperbolicDist_def, Real.sinh_artanh (pseudoHyperbolicExpr_mem_Ioo hz hw),
    sqrt_one_sub_pseudoHyperbolicExpr_sq hz hw, pseudoHyperbolicExpr_def, norm_div]
  set D := ‖1 - (starRingEnd ℂ) w * z‖
  have hD0 : D ≠ 0 := hD.ne'
  have hS0 : Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) ≠ 0 := hS.ne'
  field_simp

/-- **The hyperbolic cosine of the hyperbolic distance.** The disc analogue of Mathlib's
`UpperHalfPlane.cosh_half_dist`. -/
theorem cosh_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.cosh (hyperbolicDist z w) =
      ‖1 - (starRingEnd ℂ) w * z‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  rw [hyperbolicDist_def, Real.cosh_artanh (pseudoHyperbolicExpr_mem_Ioo hz hw),
    sqrt_one_sub_pseudoHyperbolicExpr_sq hz hw, one_div_div]

/-- **The hyperbolic tangent of the hyperbolic distance** is the pseudo-hyperbolic expression:
`hyperbolicDist` and `pseudoHyperbolicExpr` are two readings of the same geometry, the first
additive and the second multiplicative. The disc analogue of Mathlib's
`UpperHalfPlane.tanh_half_dist`. -/
theorem tanh_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.tanh (hyperbolicDist z w) = pseudoHyperbolicExpr z w := by
  rw [hyperbolicDist_def, Real.tanh_artanh (pseudoHyperbolicExpr_mem_Ioo hz hw)]

/-- **The exponential of the hyperbolic distance.** The disc analogue of Mathlib's
`UpperHalfPlane.exp_half_dist`. -/
theorem exp_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.exp (hyperbolicDist z w) =
      (‖1 - (starRingEnd ℂ) w * z‖ + ‖z - w‖) /
        Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  rw [← Real.cosh_add_sinh, cosh_hyperbolicDist hz hw, sinh_hyperbolicDist hz hw, ← add_div]

/-- **The double-angle closed form**, the identity usually quoted as *the* formula for the
Poincaré distance of the disc:
`cosh (2 d) = 1 + 2 ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2) (1 - ‖w‖ ^ 2))`.
Only Euclidean data appear on the right, and the Moebius denominator has disappeared. The disc
analogue of Mathlib's `UpperHalfPlane.cosh_dist` (the factor `2` reflecting the normalisation:
`2 * hyperbolicDist` is the curvature `-1` distance). -/
theorem cosh_two_mul_hyperbolicDist (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    Real.cosh (2 * hyperbolicDist z w) =
      1 + 2 * ‖z - w‖ ^ 2 / ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  have hP : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := defect_pos hz hw
  have hid := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w
  rw [Real.cosh_two_mul, cosh_hyperbolicDist hz hw, sinh_hyperbolicDist hz hw, div_pow, div_pow,
    Real.sq_sqrt hP.le]
  set P := (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)
  have hP0 : P ≠ 0 := hP.ne'
  field_simp
  linear_combination hid

/-- **The logarithmic closed form.** Writing `N = ‖z - w‖` for the numerator and
`D = ‖1 - conj w * z‖` for the Moebius denominator, the hyperbolic distance is
`(1 / 2) log ((D + N) / (D - N))`; the denominator `D - N` is positive on the disc precisely
because the defect identity makes `D ^ 2 - N ^ 2` positive there. -/
theorem hyperbolicDist_eq_half_log (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hyperbolicDist z w =
      1 / 2 * Real.log ((‖1 - (starRingEnd ℂ) w * z‖ + ‖z - w‖) /
        (‖1 - (starRingEnd ℂ) w * z‖ - ‖z - w‖)) := by
  have hD : 0 < ‖1 - (starRingEnd ℂ) w * z‖ := norm_one_sub_conj_mul_pos hz hw
  have hDN : 0 < ‖1 - (starRingEnd ℂ) w * z‖ - ‖z - w‖ :=
    sub_pos.mpr (norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz hw)
  have hmem := pseudoHyperbolicExpr_mem_Ioo hz hw
  have hp : pseudoHyperbolicExpr z w = ‖z - w‖ / ‖1 - (starRingEnd ℂ) w * z‖ := by
    rw [pseudoHyperbolicExpr_def, norm_div]
  rw [hyperbolicDist_def, Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hp]
  set D := ‖1 - (starRingEnd ℂ) w * z‖
  set N := ‖z - w‖
  have hD0 : D ≠ 0 := hD.ne'
  have hlt : N / D < 1 := (div_lt_one hD).mpr (by linarith)
  congr 2
  have h1 : (0 : ℝ) < 1 - N / D := by linarith
  rw [div_eq_div_iff h1.ne' hDN.ne']
  field_simp

/-- **The logarithmic closed form against the origin**, `(1 / 2) log ((1 + ‖z‖) / (1 - ‖z‖))`. -/
theorem hyperbolicDist_zero_right_eq_half_log (hz : ‖z‖ < 1) :
    hyperbolicDist z 0 = 1 / 2 * Real.log ((1 + ‖z‖) / (1 - ‖z‖)) := by
  rw [hyperbolicDist_zero_right,
    Real.artanh_eq_half_log ⟨by linarith [norm_nonneg z], hz.le⟩]

/-- The hyperbolic sine of the distance to the origin: the closed form
`sinh (hyperbolicDist z 0) = ‖z‖ / √(1 - ‖z‖ ^ 2)`. -/
theorem sinh_hyperbolicDist_zero_right (hz : ‖z‖ < 1) :
    Real.sinh (hyperbolicDist z 0) = ‖z‖ / Real.sqrt (1 - ‖z‖ ^ 2) := by
  simpa using sinh_hyperbolicDist hz (w := 0) (by norm_num)

/-- The hyperbolic cosine of the distance to the origin: the closed form
`cosh (hyperbolicDist z 0) = 1 / √(1 - ‖z‖ ^ 2)`. -/
theorem cosh_hyperbolicDist_zero_right (hz : ‖z‖ < 1) :
    Real.cosh (hyperbolicDist z 0) = 1 / Real.sqrt (1 - ‖z‖ ^ 2) := by
  simpa using cosh_hyperbolicDist hz (w := 0) (by norm_num)

/-- **Hyperbolic balls in Euclidean terms.** A bound on the hyperbolic distance is a bound on
the Euclidean distance weighted by the hyperbolic defects. The disc analogue of Mathlib's
`UpperHalfPlane.dist_le_iff_le_sinh`. -/
theorem hyperbolicDist_le_iff_le_sinh (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) {r : ℝ} :
    hyperbolicDist z w ≤ r ↔
      ‖z - w‖ ≤ Real.sinh r * Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  rw [← Real.sinh_le_sinh, sinh_hyperbolicDist hz hw,
    div_le_iff₀ (sqrt_defect_pos hz hw)]

/-- **The hyperbolic distance is at most the weighted Euclidean one.** The disc analogue of
Mathlib's `UpperHalfPlane.dist_le_dist_coe_div_sqrt`; in particular the hyperbolic distance of
two points is small when they are Euclidean-close and both stay in a fixed smaller disc. -/
theorem hyperbolicDist_le_div_sqrt (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    hyperbolicDist z w ≤ ‖z - w‖ / Real.sqrt ((1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)) := by
  rw [← sinh_hyperbolicDist hz hw]
  exact Real.self_le_sinh_iff.mpr (hyperbolicDist_nonneg z w)

/-- **The unit disc has infinite hyperbolic diameter.** Points of Euclidean norm `Real.tanh t`
are at hyperbolic distance exactly `t` from the origin, so no bound holds on the hyperbolic
distance to the origin; the Euclidean boundary is infinitely far away in the Poincaré metric. -/
theorem exists_mem_ball_lt_hyperbolicDist (C : ℝ) :
    ∃ z ∈ ball (0 : ℂ) 1, C < hyperbolicDist z 0 := by
  set t : ℝ := |C| + 1
  have htpos : 0 < t := by positivity
  have htanh_pos : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr htpos) (Real.cosh_pos t)
  have hnorm : ‖((Real.tanh t : ℝ) : ℂ)‖ = Real.tanh t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htanh_pos]
  refine ⟨((Real.tanh t : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_ball_zero_iff, hnorm]
    exact Real.tanh_lt_one t
  · rw [hyperbolicDist_zero_right, hnorm, Real.artanh_tanh]
    have : C ≤ |C| := le_abs_self C
    linarith

end TauCeti
