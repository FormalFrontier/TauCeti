/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic

/-!
# Power bounds for contraction-semigroup resolvents

This file proves the contraction case of the iterated Hille--Yosida estimate. If `S` is a
contraction semigroup and `lambda > 0`, then every natural power of its Laplace-transform
resolvent satisfies

`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`.

The corresponding pointwise estimate and the equivalent bound for the scaled resolvent
`lambda R(lambda)` are also recorded. These estimates are the contraction specialization of
the power bounds used in the Hille--Yosida generation theorem.

## References

The estimates are the contraction case of Engel--Nagel, *One-Parameter Semigroups for Linear
Evolution Equations*, Theorem II.3.5.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace ContractionSemigroup

/-- The iterated Hille--Yosida bound for a contraction semigroup:
`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`. -/
theorem resolvent_pow_norm_le (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda)
    (n : ℕ) :
    ‖S.resolvent lambda hlambda ^ n‖ ≤ (1 / lambda) ^ n := by
  cases n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n =>
      exact (norm_pow_le' _ n.succ_pos).trans
        (pow_le_pow_left₀ (norm_nonneg _) (S.resolvent_norm_le lambda hlambda) (n + 1))

/-- Pointwise form of the iterated contraction resolvent bound. -/
theorem norm_resolvent_pow_apply_le (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) (x : X) :
    ‖(S.resolvent lambda hlambda ^ n) x‖ ≤ (1 / lambda) ^ n * ‖x‖ := by
  exact (S.resolvent lambda hlambda ^ n).le_of_opNorm_le
    (S.resolvent_pow_norm_le lambda hlambda n) x

/-- Every power of the scaled contraction resolvent `lambda R(lambda)` has norm at most one. -/
theorem norm_smul_resolvent_pow_le_one (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) :
    ‖(lambda • S.resolvent lambda hlambda) ^ n‖ ≤ 1 := by
  rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlambda.le n)]
  calc
    lambda ^ n * ‖S.resolvent lambda hlambda ^ n‖
        ≤ lambda ^ n * (1 / lambda) ^ n := by
          gcongr
          exact S.resolvent_pow_norm_le lambda hlambda n
    _ = 1 := by rw [← mul_pow, one_div, mul_inv_cancel₀ hlambda.ne', one_pow]

/-- Pointwise form of the power bound for the scaled contraction resolvent. -/
theorem norm_smul_resolvent_pow_apply_le (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) (x : X) :
    ‖((lambda • S.resolvent lambda hlambda) ^ n) x‖ ≤ ‖x‖ := by
  simpa using ((lambda • S.resolvent lambda hlambda) ^ n).le_of_opNorm_le
    (S.norm_smul_resolvent_pow_le_one lambda hlambda n) x

end ContractionSemigroup

end TauCeti.Semigroups

end
