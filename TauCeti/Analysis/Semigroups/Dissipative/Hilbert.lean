/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Dissipative.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Hilbert-space characterization of dissipativity

On a real inner-product space the Banach-space definition of dissipativity,
`lambda * ‖x‖ ≤ ‖lambda • x - A x‖` for all `lambda > 0`, collapses to the familiar
inner-product condition

`⟪A x, x⟫ ≤ 0` for all `x ∈ D(A)`.

Both implications come from the polarization identity
`‖lambda • x - A x‖² = (lambda ‖x‖)² - 2 lambda ⟪x, A x⟫ + ‖A x‖²`: the sign condition makes
the correction term nonnegative, and conversely dividing the resulting inequality
`2 lambda ⟪A x, x⟫ ≤ ‖A x‖²` by `lambda` and letting `lambda → ∞` forces `⟪A x, x⟫ ≤ 0`.

Combined with `TauCeti.Semigroups.ContractionSemigroup.isDissipative_generator`, this gives the
Hilbert-space form of the converse of the Lumer--Phillips theorem: the generator of a
contraction semigroup on a real Hilbert space satisfies `⟪A x, x⟫ ≤ 0`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Example II.3.24 and
Proposition II.3.23; Pazy, *Semigroups of Linear Operators and Applications to Partial
Differential Equations*, Chapter 1, Section 4.
-/

public section

open scoped InnerProductSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Expansion of `‖lambda • x - y‖²` on a real inner-product space, with the scalar `lambda`
pulled out of both the norm and the inner product. -/
private theorem norm_smul_sub_sq_real {lambda : ℝ} (hlambda : 0 ≤ lambda) (x y : X) :
    ‖lambda • x - y‖ ^ 2 = (lambda * ‖x‖) ^ 2 - 2 * (lambda * ⟪x, y⟫_ℝ) + ‖y‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hlambda]

/-- **Dissipativity on a real inner-product space.** An unbounded operator is dissipative
exactly when `⟪A x, x⟫ ≤ 0` on its domain. -/
theorem isDissipative_iff_real_inner_nonpos (A : X →ₗ.[ℝ] X) :
    IsDissipative A ↔ ∀ x : A.domain, ⟪A x, (x : X)⟫_ℝ ≤ 0 := by
  constructor
  · -- Dissipativity gives `2 lambda ⟪A x, x⟫ ≤ ‖A x‖²` for every `lambda > 0`, which is
    -- impossible for large `lambda` unless `⟪A x, x⟫ ≤ 0`.
    intro hA x
    by_contra hcon
    rw [not_le] at hcon
    have hcomm : ⟪(x : X), A x⟫_ℝ = ⟪A x, (x : X)⟫_ℝ := real_inner_comm _ _
    have key : ∀ lambda : ℝ, 0 < lambda →
        2 * (lambda * ⟪A x, (x : X)⟫_ℝ) ≤ ‖A x‖ ^ 2 := by
      intro lambda hlambda
      have hsq : (lambda * ‖(x : X)‖) ^ 2 ≤ ‖lambda • (x : X) - A x‖ ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hlambda.le (norm_nonneg _)) (hA lambda hlambda x) 2
      rw [norm_smul_sub_sq_real hlambda.le, hcomm] at hsq
      linarith
    have hbig := key ((‖A x‖ ^ 2 + 1) / (2 * ⟪A x, (x : X)⟫_ℝ))
      (div_pos (by positivity) (by linarith))
    have hcancel : 2 * ((‖A x‖ ^ 2 + 1) / (2 * ⟪A x, (x : X)⟫_ℝ) * ⟪A x, (x : X)⟫_ℝ) =
        ‖A x‖ ^ 2 + 1 := by
      field_simp
    linarith
  · -- The sign condition makes the cross term in the polarization identity nonnegative.
    intro h lambda hlambda x
    have hcomm : ⟪(x : X), A x⟫_ℝ = ⟪A x, (x : X)⟫_ℝ := real_inner_comm _ _
    have hsq : (lambda * ‖(x : X)‖) ^ 2 ≤ ‖lambda • (x : X) - A x‖ ^ 2 := by
      rw [norm_smul_sub_sq_real hlambda.le, hcomm]
      have hcross : 0 ≤ lambda * -⟪A x, (x : X)⟫_ℝ :=
        mul_nonneg hlambda.le (neg_nonneg.mpr (h x))
      nlinarith [sq_nonneg ‖A x‖]
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

namespace ContractionSemigroup

variable [CompleteSpace X]

/-- **The converse of the Lumer--Phillips theorem on a Hilbert space.** The generator of a
contraction semigroup on a real Hilbert space satisfies `⟪A x, x⟫ ≤ 0` on its domain. -/
theorem real_inner_generator_nonpos (S : ContractionSemigroup X)
    (x : S.toStronglyContinuousSemigroup.generator.domain) :
    ⟪S.toStronglyContinuousSemigroup.generator x, (x : X)⟫_ℝ ≤ 0 :=
  (isDissipative_iff_real_inner_nonpos _).mp S.isDissipative_generator x

end ContractionSemigroup

end TauCeti.Semigroups

end
