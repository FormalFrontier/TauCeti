/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum

/-!
# The Rayleigh principle for a coercive variational problem

Let `B` be a bounded coercive symmetric bilinear form on a real Hilbert space `V` and let
`J : V →L[ℝ] H` be a continuous linear map into a second real Hilbert space.  When `J` is nonzero
and compact, the **variational eigenvalues** of the pair are the reciprocals of the nonzero
eigenvalues of the solution operator `S = IsCoercive.formSolutionOperator`, and the *least*
variational eigenvalue `‖S‖⁻¹` is the minimum of the **Rayleigh quotient**

`B v v / ‖J v‖²`,

taken over the `v : V` with `J v ≠ 0`.  Without compactness, this file proves that `‖S‖⁻¹` is
still the largest constant `C` for which `C ‖J v‖² ≤ B v v` holds for every `v : V`, provided
`J ≠ 0`.

For the Dirichlet problem of a divergence-form elliptic operator, with `V = H¹₀(Ω)`,
`H = L²(Ω)` and `J` the inclusion, this says that the first eigenvalue is the minimum of the
energy over the `L²`-unit sphere, and that it is exactly the optimal constant in the Poincaré
inequality `C‖u‖²_{L²} ≤ a(u, u)`.

## The two halves of the argument

The lower bound `‖S‖⁻¹ ‖J v‖² ≤ B v v` needs no compactness and no attainment.  It comes from
**Cauchy--Schwarz in the energy form**: solving `B w u = ⟪J v, J u⟫` for `w` gives
`‖J v‖² = B w v` and `B w w = ⟪J v, S (J v)⟫ ≤ ‖S‖ ‖J v‖²`, and
`(B w v)² ≤ B w w · B v v` closes the loop.  Coercivity supplies the solution operator through
Lax--Milgram and the nonnegativity of the diagonal, which is what makes the energy form obey
Cauchy--Schwarz; that inequality is `LinearMap.BilinForm.apply_sq_le_of_symm`, applied to the
continuous form's underlying bilinear form.

The *attainment* is where compactness enters: `‖S‖` is an eigenvalue of the compact symmetric
positive operator `S` (`IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`), and its
eigenfunction realizes the quotient.  Without compactness the infimum can fail to be attained,
so the `IsLeast` statement carries `IsCompactOperator J`; the optimal-constant `IsGreatest`
statement does not require attainment.

## Main declarations

* `IsCoercive.norm_apply_sq_le_norm_formSolutionOperator_mul`: the estimate
  `‖J v‖² ≤ ‖S‖ B v v`, and `IsCoercive.inv_norm_formSolutionOperator_mul_norm_apply_sq_le` its
  reciprocal form `‖S‖⁻¹ ‖J v‖² ≤ B v v`.
* `IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`: `‖S‖⁻¹` is a variational
  eigenvalue, the least one.
* `IsCoercive.isLeast_rayleighQuotient`: **the Rayleigh principle**, `‖S‖⁻¹` is the minimum of
  the Rayleigh quotient.
* `IsCoercive.isGreatest_inv_norm_formSolutionOperator`: `‖S‖⁻¹` is the optimal constant in
  the inequality `C ‖J v‖² ≤ B v v`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.5.1, Theorem 2 (the variational
principle for the principal eigenvalue); H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Section 6.4.
-/

public section

noncomputable section

open Module.End
open scoped InnerProduct InnerProductSpace

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

/-! ### The Rayleigh lower bound -/

/-- **The energy form dominates the `H`-norm, with constant the norm of the solution
operator**: `‖J v‖² ≤ ‖S‖ · B v v`.  This is Cauchy--Schwarz in the energy form, applied to `v`
and to the solution `w` of `B w u = ⟪J v, J u⟫`; no compactness of `J` is used. -/
theorem norm_apply_sq_le_norm_formSolutionOperator_mul (hB : IsCoercive B) (J : V →L[ℝ] H)
    (hsymm : ∀ u v : V, B u v = B v u) (v : V) :
    ‖J v‖ ^ 2 ≤ ‖hB.formSolutionOperator J‖ * B v v := by
  set w := hB.formSolutionMap J (J v) with hw
  have hwv : B w v = ‖J v‖ ^ 2 := by
    rw [hw, apply_formSolutionMap, real_inner_self_eq_norm_sq]
  have hww : B w w ≤ ‖hB.formSolutionOperator J‖ * ‖J v‖ ^ 2 := by
    have hself : B w w = ⟪J v, hB.formSolutionOperator J (J v)⟫_ℝ := by
      rw [hw, apply_formSolutionMap, formSolutionOperator_apply]
    calc B w w = ⟪J v, hB.formSolutionOperator J (J v)⟫_ℝ := hself
      _ ≤ ‖J v‖ * ‖hB.formSolutionOperator J (J v)‖ := real_inner_le_norm _ _
      _ ≤ ‖J v‖ * (‖hB.formSolutionOperator J‖ * ‖J v‖) :=
          mul_le_mul_of_nonneg_left ((hB.formSolutionOperator J).le_opNorm _) (norm_nonneg _)
      _ = ‖hB.formSolutionOperator J‖ * ‖J v‖ ^ 2 := by ring
  have hcs : B w v ^ 2 ≤ B w w * B v v :=
    B.toBilinForm.apply_sq_le_of_symm hB.apply_self_nonneg ⟨hsymm⟩ w v
  rw [hwv] at hcs
  rcases eq_or_lt_of_le (norm_nonneg (J v)) with hzero | hpos
  · rw [← hzero]
    have : (0 : ℝ) ≤ ‖hB.formSolutionOperator J‖ * B v v :=
      mul_nonneg (norm_nonneg _) (hB.apply_self_nonneg v)
    simpa using this
  · refine le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < ‖J v‖ ^ 2)
    calc ‖J v‖ ^ 2 * ‖J v‖ ^ 2 = (‖J v‖ ^ 2) ^ 2 := by ring
      _ ≤ B w w * B v v := hcs
      _ ≤ (‖hB.formSolutionOperator J‖ * ‖J v‖ ^ 2) * B v v :=
          mul_le_mul_of_nonneg_right hww (hB.apply_self_nonneg v)
      _ = ‖hB.formSolutionOperator J‖ * B v v * ‖J v‖ ^ 2 := by ring

/-- **The Rayleigh lower bound**: `‖S‖⁻¹ ‖J v‖² ≤ B v v` for every `v : V`.  For the Dirichlet
problem this is the Poincaré inequality with the reciprocal solution-operator norm as its
constant.  Beyond coercivity, only symmetry is needed: when `S = 0` the left-hand side vanishes
and the bound is the nonnegativity of the energy. -/
theorem inv_norm_formSolutionOperator_mul_norm_apply_sq_le (hB : IsCoercive B) (J : V →L[ℝ] H)
    (hsymm : ∀ u v : V, B u v = B v u) (v : V) :
    ‖hB.formSolutionOperator J‖⁻¹ * ‖J v‖ ^ 2 ≤ B v v := by
  rcases eq_or_lt_of_le (norm_nonneg (hB.formSolutionOperator J)) with hzero | hpos
  · rw [← hzero]
    simpa using hB.apply_self_nonneg v
  · rw [inv_mul_le_iff₀ hpos]
    linarith [hB.norm_apply_sq_le_norm_formSolutionOperator_mul J hsymm v]

/-! ### The Rayleigh principle -/

/-- **The Rayleigh principle**: the least variational eigenvalue `‖S‖⁻¹` is the *minimum* of the
Rayleigh quotient `B v v / ‖J v‖²` over the vectors with `J v ≠ 0`.  The minimum is attained at
an eigenfunction, which is why compactness of `J` is assumed. -/
theorem isLeast_rayleighQuotient (hB : IsCoercive B) {J : V →L[ℝ] H} (hJ : IsCompactOperator J)
    (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    IsLeast {r : ℝ | ∃ v : V, J v ≠ 0 ∧ B v v / ‖J v‖ ^ 2 = r}
      ‖hB.formSolutionOperator J‖⁻¹ := by
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner hJ hsymm hJne
  have hJu : J u ≠ 0 := hB.apply_ne_zero_of_forall_apply_eq_smul_inner J hu heq
  constructor
  · refine ⟨u, hJu, ?_⟩
    rw [heq u, real_inner_self_eq_norm_sq, mul_div_assoc,
      div_self (by positivity : ‖J u‖ ^ 2 ≠ 0), mul_one]
  · rintro r ⟨v, hJv, rfl⟩
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖J v‖ ^ 2)]
    exact hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le J hsymm v

/-- **The reciprocal solution-operator norm is the optimal constant** in the inequality
`C ‖J v‖² ≤ B v v`: it satisfies the inequality, and no larger constant does.  For the Dirichlet
problem this identifies the quantity defined as `firstDirichletEigenvalue` with the best Poincaré
constant.  Unlike attainment of the Rayleigh minimum, this characterization does not require
compactness of `J`. -/
theorem isGreatest_inv_norm_formSolutionOperator (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    IsGreatest {C : ℝ | ∀ v : V, C * ‖J v‖ ^ 2 ≤ B v v} ‖hB.formSolutionOperator J‖⁻¹ := by
  obtain ⟨w, hw⟩ : ∃ w : V, J w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hJne
  have _ : Nontrivial H := nontrivial_of_ne (J w) 0 hw
  set S := hB.formSolutionOperator J with hS
  have hSne : S ≠ 0 := by
    rw [hS]
    exact hB.formSolutionOperator_ne_zero hJne
  have hnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hSne
  refine ⟨fun v => hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le J hsymm v, fun C hC => ?_⟩
  rcases le_or_gt C 0 with hCnonpos | hCpos
  · exact hCnonpos.trans (inv_nonneg.mpr (norm_nonneg S))
  · have hop : ‖C • S‖ ≤ 1 := (C • S).opNorm_le_bound zero_le_one fun h => by
      rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hCpos]
      rcases eq_or_ne (S h) 0 with hzero | hne
      · simp [hzero]
      · have henergy : C * ‖S h‖ ^ 2 ≤ ⟪h, S h⟫_ℝ := calc
          C * ‖S h‖ ^ 2 = C * ‖J (hB.formSolutionMap J h)‖ ^ 2 := by
            rw [hS, formSolutionOperator_apply]
          _ ≤ B (hB.formSolutionMap J h) (hB.formSolutionMap J h) :=
            hC (hB.formSolutionMap J h)
          _ = ⟪h, S h⟫_ℝ := by
            rw [hS, inner_formSolutionOperator_self]
        have hinner : ⟪h, S h⟫_ℝ ≤ ‖h‖ * ‖S h‖ := real_inner_le_norm _ _
        exact le_of_mul_le_mul_right (by nlinarith) (norm_pos_iff.mpr hne)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hCpos] at hop
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hnorm_pos).mpr hop

end IsCoercive
