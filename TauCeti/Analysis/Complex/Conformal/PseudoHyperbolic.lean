/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.UnitDisc.Basic

/-!
# The pseudo-hyperbolic expression on the unit disc

This file records the scalar pseudo-hyperbolic expression
`‖(z - w) / (1 - conj w * z)‖` used in the Schwarz--Pick layer of the conformal-mapping
roadmap.  The main API proves that the denominator is nonzero on the open unit disc, the
expression is symmetric, and it is strictly less than one for two points of the unit disc.
The Poincaré defect identity `TauCeti.norm_sq_one_sub_conj_mul_sub_norm_sq_sub` compares the
numerator and the denominator, and yields
`TauCeti.norm_sub_eq_of_pseudoHyperbolicExpr_eq`: between points of prescribed norms, the
pseudo-hyperbolic expression determines the Euclidean distance.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
any Tau Ceti overlap with the L0--L3 prerequisites is a temporary shim to be deleted or
refactored to Mathlib once the corresponding upstream API lands.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- The pseudo-hyperbolic expression on `ℂ`, written as a total real-valued function.

On the open unit disc this is the pseudo-hyperbolic expression.  Outside the disc the same
formula is still meaningful as a total expression in Lean, with division by zero evaluating
to zero as usual. -/
noncomputable def pseudoHyperbolicExpr (z w : ℂ) : ℝ :=
  ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖

/-- The defining formula for the pseudo-hyperbolic expression. -/
lemma pseudoHyperbolicExpr_def (z w : ℂ) :
    pseudoHyperbolicExpr z w = ‖(z - w) / (1 - (starRingEnd ℂ) w * z)‖ :=
  by rfl

/-- The pseudo-hyperbolic expression as a quotient of two real norms, the form in which it is
compared with the Euclidean distance `‖z - w‖`. -/
lemma pseudoHyperbolicExpr_eq_norm_div_norm (z w : ℂ) :
    pseudoHyperbolicExpr z w = ‖z - w‖ / ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [pseudoHyperbolicExpr_def, norm_div]

@[simp]
lemma pseudoHyperbolicExpr_nonneg (z w : ℂ) : 0 ≤ pseudoHyperbolicExpr z w :=
  norm_nonneg _

/-- The pseudo-hyperbolic expression from a point to itself is zero. -/
@[simp]
lemma pseudoHyperbolicExpr_self (z : ℂ) : pseudoHyperbolicExpr z z = 0 := by
  simp [pseudoHyperbolicExpr]

private lemma norm_one_sub_conj_mul_comm (z w : ℂ) :
    ‖1 - (starRingEnd ℂ) w * z‖ = ‖1 - (starRingEnd ℂ) z * w‖ := by
  calc
    ‖1 - (starRingEnd ℂ) w * z‖ =
        ‖(starRingEnd ℂ) (1 - (starRingEnd ℂ) w * z)‖ := by rw [norm_conj]
    _ = ‖1 - (starRingEnd ℂ) z * w‖ := by
      congr 1
      simp [mul_comm]

/-- The pseudo-hyperbolic expression is symmetric in its two arguments. -/
lemma pseudoHyperbolicExpr_comm (z w : ℂ) :
    pseudoHyperbolicExpr z w = pseudoHyperbolicExpr w z := by
  unfold pseudoHyperbolicExpr
  rw [norm_div, norm_div, norm_sub_rev, norm_one_sub_conj_mul_comm]

/-- **Conjugation invariance.** Conjugating both arguments leaves the pseudo-hyperbolic
expression unchanged: conjugation is the orientation-reversing symmetry of the disc. -/
@[simp]
lemma pseudoHyperbolicExpr_conj (z w : ℂ) :
    pseudoHyperbolicExpr ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) = pseudoHyperbolicExpr z w := by
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def,
    ← norm_conj ((z - w) / (1 - (starRingEnd ℂ) w * z)), map_div₀]
  simp

/-- If the two points are equal, their pseudo-hyperbolic expression is zero. -/
lemma pseudoHyperbolicExpr_eq_zero_of_eq {z w : ℂ} (h : z = w) :
    pseudoHyperbolicExpr z w = 0 := by
  simp [h]

/-- The pseudo-hyperbolic expression with right endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicExpr_zero_right (z : ℂ) : pseudoHyperbolicExpr z 0 = ‖z‖ := by
  simp [pseudoHyperbolicExpr]

/-- The pseudo-hyperbolic expression with left endpoint zero is the norm. -/
@[simp]
lemma pseudoHyperbolicExpr_zero_left (w : ℂ) : pseudoHyperbolicExpr 0 w = ‖w‖ := by
  simp [pseudoHyperbolicExpr]

/-- **Rotation invariance.** Multiplying both arguments by a unit-modulus constant leaves the
pseudo-hyperbolic expression unchanged.  This is a purely algebraic identity valid for all
`z`, `w`; it is the rotation half of the disc-automorphism group. -/
@[simp]
lemma pseudoHyperbolicExpr_const_mul {c : ℂ} (hc : ‖c‖ = 1) (z w : ℂ) :
    pseudoHyperbolicExpr (c * z) (c * w) = pseudoHyperbolicExpr z w := by
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hden : (starRingEnd ℂ) (c * w) * (c * z) = (starRingEnd ℂ) w * z := by
    rw [map_mul]
    calc (starRingEnd ℂ) c * (starRingEnd ℂ) w * (c * z)
        = ((starRingEnd ℂ) c * c) * ((starRingEnd ℂ) w * z) := by ring
      _ = (starRingEnd ℂ) w * z := by rw [hcc, one_mul]
  have hnum : c * z - c * w = c * (z - w) := by ring
  have hden' : (1 : ℂ) - (starRingEnd ℂ) (c * w) * (c * z) =
      1 - (starRingEnd ℂ) w * z := by
    rw [hden]
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def, hnum, hden',
    mul_div_assoc, norm_mul, hc, one_mul]

/-- If the denominator is nonzero, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_den_ne_zero {z w : ℂ}
    (hden : 1 - (starRingEnd ℂ) w * z ≠ 0) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w := by
  rw [pseudoHyperbolicExpr, norm_eq_zero, div_eq_zero_iff]
  simp only [hden, or_false]
  exact sub_eq_zero

/-- On the open unit disc, the denominator in the pseudo-hyperbolic expression is nonzero. -/
lemma one_sub_conj_mul_ne_zero_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  (isUnit_one_sub_of_norm_lt_one (x := (starRingEnd ℂ) w * z)
    (by
      rw [norm_mul, norm_conj]
      exact mul_lt_one_of_nonneg_of_lt_one_right hw.le (norm_nonneg _) hz)).ne_zero

/-- For points in the open unit ball, the denominator in the pseudo-hyperbolic expression is
nonzero. -/
lemma one_sub_conj_mul_ne_zero_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    1 - (starRingEnd ℂ) w * z ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- For bundled unit-disc points, the denominator in the pseudo-hyperbolic expression is
nonzero. -/
lemma one_sub_conj_mul_ne_zero_unitDisc (z w : Complex.UnitDisc) :
    1 - (starRingEnd ℂ) (w : ℂ) * (z : ℂ) ≠ 0 :=
  one_sub_conj_mul_ne_zero_of_norm_lt_one z.norm_lt_one w.norm_lt_one

/-- For a point of norm at most one, the denominator of the Moebius factor evaluated at the
factor's own center has norm `1 - ‖w‖ ^ 2`. -/
lemma norm_one_sub_conj_mul_self_of_norm_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(1 : ℂ) - (starRingEnd ℂ) w * w‖ = 1 - ‖w‖ ^ 2 := by
  have hconj : (starRingEnd ℂ) w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hconj, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by nlinarith [norm_nonneg w])]

/-- On the open unit disc, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w := by
  exact pseudoHyperbolicExpr_eq_zero_iff_of_den_ne_zero
    (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)

/-- For points in the open unit ball, zero pseudo-hyperbolic expression characterizes equality. -/
lemma pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr z w = 0 ↔ z = w :=
  pseudoHyperbolicExpr_eq_zero_iff_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- For bundled unit-disc points, zero pseudo-hyperbolic expression characterizes equality. -/
@[simp]
lemma pseudoHyperbolicExpr_eq_zero_iff_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) = 0 ↔ z = w := by
  rw [pseudoHyperbolicExpr_eq_zero_iff_of_norm_lt_one z.norm_lt_one w.norm_lt_one]
  exact Subtype.ext_iff.symm

private lemma normSq_one_sub_conj_mul_sub_normSq_sub (z w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) w * z) - Complex.normSq (z - w) =
      (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_conj,
    Complex.normSq_one]
  have hre : (1 * (starRingEnd ℂ) ((starRingEnd ℂ) w * z)).re =
      (z * (starRingEnd ℂ) w).re := by
    simp [mul_comm]
  rw [hre]
  ring_nf

/-- **Poincaré defect identity (norm form).** The difference of the squared norms of the Moebius
denominator and numerator factors is the product of the two hyperbolic defects:
`‖1 - conj w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2)`. -/
lemma norm_sq_one_sub_conj_mul_sub_norm_sq_sub (z w : ℂ) :
    ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ^ 2 - ‖z - w‖ ^ 2 = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  simpa only [Complex.normSq_eq_norm_sq] using normSq_one_sub_conj_mul_sub_normSq_sub z w

/-- **Equal norms plus equal pseudo-hyperbolic expression force equal distance.** For four points
of the open unit disc with `‖z'‖ = ‖z‖` and `‖w'‖ = ‖w‖`, the pseudo-hyperbolic expression
determines the Euclidean distance. -/
lemma norm_sub_eq_of_pseudoHyperbolicExpr_eq {z w z' w' : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) (hnz : ‖z'‖ = ‖z‖) (hnw : ‖w'‖ = ‖w‖)
    (h : pseudoHyperbolicExpr z' w' = pseudoHyperbolicExpr z w) :
    ‖z' - w'‖ = ‖z - w‖ := by
  have hz' : ‖z'‖ < 1 := by rw [hnz]; exact hz
  have hw' : ‖w'‖ < 1 := by rw [hnw]; exact hw
  have hc : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have h1 : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h2 : (0 : ℝ) < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact mul_pos h1 h2
  have hden : ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw)
  have hden' : ‖(1 : ℂ) - (starRingEnd ℂ) w' * z'‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (one_sub_conj_mul_ne_zero_of_norm_lt_one hz' hw')
  -- The Poincaré defect identity writes each squared denominator as the squared numerator plus a
  -- correction depending only on the two norms, which the two pairs share.
  have hB : ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ^ 2
      = ‖z - w‖ ^ 2 + (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z w
    linarith
  have hB' : ‖(1 : ℂ) - (starRingEnd ℂ) w' * z'‖ ^ 2
      = ‖z' - w'‖ ^ 2 + (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
    have := norm_sq_one_sub_conj_mul_sub_norm_sq_sub z' w'
    rw [hnz, hnw] at this
    linarith
  have hquot : ‖z' - w'‖ * ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖
      = ‖z - w‖ * ‖(1 : ℂ) - (starRingEnd ℂ) w' * z'‖ := by
    have h' : ‖z' - w'‖ / ‖(1 : ℂ) - (starRingEnd ℂ) w' * z'‖
        = ‖z - w‖ / ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ := by
      simpa only [pseudoHyperbolicExpr_def, norm_div] using h
    exact (div_eq_div_iff hden' hden).mp h'
  have hsq : ‖z' - w'‖ ^ 2 * ‖(1 : ℂ) - (starRingEnd ℂ) w * z‖ ^ 2
      = ‖z - w‖ ^ 2 * ‖(1 : ℂ) - (starRingEnd ℂ) w' * z'‖ ^ 2 := by
    rw [← mul_pow, ← mul_pow, hquot]
  rw [hB, hB'] at hsq
  have hAA : ‖z' - w'‖ ^ 2 = ‖z - w‖ ^ 2 := by nlinarith [hsq, hc]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hAA

/-- For two points of norm less than one, the numerator norm is smaller than the denominator
norm in the pseudo-hyperbolic expression. -/
lemma norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖z - w‖ < ‖1 - (starRingEnd ℂ) w * z‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  have hpos : 0 < (1 - Complex.normSq z) * (1 - Complex.normSq w) := by
    have hzpos : 0 < 1 - Complex.normSq z := sub_pos.mpr <| by
      rw [Complex.normSq_eq_norm_sq]
      rw [sq_lt_one_iff_abs_lt_one, abs_norm]
      exact hz
    have hwpos : 0 < 1 - Complex.normSq w := sub_pos.mpr <| by
      rw [Complex.normSq_eq_norm_sq]
      rw [sq_lt_one_iff_abs_lt_one, abs_norm]
      exact hw
    exact mul_pos hzpos hwpos
  have hdiff := normSq_one_sub_conj_mul_sub_normSq_sub z w
  nlinarith

/-- The pseudo-hyperbolic expression of two points of norm less than one is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_of_norm_lt_one {z w : ℂ}
    (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pseudoHyperbolicExpr z w < 1 := by
  have hden_ne : 1 - (starRingEnd ℂ) w * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one hz hw
  have hden : 0 < ‖1 - (starRingEnd ℂ) w * z‖ := norm_pos_iff.mpr hden_ne
  have hlt := norm_sub_lt_norm_one_sub_conj_mul_of_norm_lt_one hz hw
  rw [pseudoHyperbolicExpr, norm_div]
  rwa [div_lt_one hden]

/-- The pseudo-hyperbolic expression of two points in the open unit ball is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_of_mem_ball {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr z w < 1 :=
  pseudoHyperbolicExpr_lt_one_of_norm_lt_one (by simpa [mem_ball_zero_iff] using hz)
    (by simpa [mem_ball_zero_iff] using hw)

/-- The pseudo-hyperbolic expression of two bundled unit-disc points is strictly less
than one. -/
lemma pseudoHyperbolicExpr_lt_one_unitDisc (z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (z : ℂ) (w : ℂ) < 1 :=
  pseudoHyperbolicExpr_lt_one_of_norm_lt_one z.norm_lt_one w.norm_lt_one

end TauCeti
