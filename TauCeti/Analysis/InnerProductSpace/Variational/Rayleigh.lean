/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Variational.Spectrum
public import TauCeti.LinearAlgebra.BilinearForm.PosSemidef

/-!
# The Rayleigh principle for a coercive variational problem

Let `B` be a bounded coercive symmetric bilinear form on a real Hilbert space `V` and let
`J : V →L[ℝ] H` be a continuous linear map into a second real Hilbert space.  The **variational
eigenvalues** of the pair are the reciprocals of the nonzero eigenvalues of the solution
operator `S = IsCoercive.formSolutionOperator`, so the *least* variational eigenvalue is
`‖S‖⁻¹`.  This file proves that this number is the minimum of the **Rayleigh quotient**

`B v v / ‖J v‖²`,

taken over the `v : V` with `J v ≠ 0`, and — the same statement read as an inequality — that it
is the largest constant `C` for which `C ‖J v‖² ≤ B v v` holds for every `v : V`.

For the Dirichlet problem of a divergence-form elliptic operator, with `V = H¹₀(Ω)`,
`H = L²(Ω)` and `J` the inclusion, this says that the first eigenvalue is the minimum of the
energy over the `L²`-unit sphere, and that it is exactly the optimal constant in the Poincaré
inequality `C‖u‖²_{L²} ≤ a(u, u)`.

## The two halves of the argument

The lower bound `‖S‖⁻¹ ‖J v‖² ≤ B v v` needs no compactness and no attainment.  It comes from
**Cauchy--Schwarz in the energy form**: solving `B w u = ⟪J v, J u⟫` for `w` gives
`‖J v‖² = B w v` and `B w w = ⟪J v, S (J v)⟫ ≤ ‖S‖ ‖J v‖²`, and
`(B w v)² ≤ B w w · B v v` closes the loop.  Coercivity enters only through the
nonnegativity of the diagonal, which is what makes the energy form obey Cauchy--Schwarz;
that inequality is `LinearMap.BilinForm.IsPosSemidef.sq_apply_le_mul_apply_self`, transferred
to continuous bilinear forms here by
`ContinuousLinearMap.sq_apply_le_apply_self_mul_apply_self`.

The *attainment* is where compactness enters: `‖S‖` is an eigenvalue of the compact symmetric
positive operator `S` (`IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`), and its
eigenfunction realizes the quotient.  Without compactness the infimum can fail to be attained,
so the `IsLeast`/`IsGreatest` statements carry `IsCompactOperator J` while the inequality does
not.

## Main declarations

* `ContinuousLinearMap.sq_apply_le_apply_self_mul_apply_self`: Cauchy--Schwarz for a symmetric
  continuous bilinear form with nonnegative diagonal.
* `IsCoercive.norm_apply_sq_le_norm_formSolutionOperator_mul`: the estimate
  `‖J v‖² ≤ ‖S‖ B v v`, and `IsCoercive.inv_norm_formSolutionOperator_mul_norm_apply_sq_le` its
  reciprocal form `‖S‖⁻¹ ‖J v‖² ≤ B v v`.
* `IsCoercive.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner`: `‖S‖⁻¹` is a variational
  eigenvalue, the least one.
* `IsCoercive.isLeast_rayleighQuotient`: **the Rayleigh principle**, `‖S‖⁻¹` is the minimum of
  the Rayleigh quotient.
* `IsCoercive.isGreatest_setOf_forall_mul_norm_apply_sq_le`: `‖S‖⁻¹` is the optimal constant in
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

section CauchySchwarz

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : V →L[ℝ] V →L[ℝ] ℝ}

/-- **Cauchy--Schwarz for a symmetric continuous bilinear form with nonnegative diagonal**:
`(B u v)² ≤ B u u · B v v`.  This transfers
`LinearMap.BilinForm.IsPosSemidef.sq_apply_le_mul_apply_self` — where the inequality is proved,
by a discriminant, with no continuity in sight — to the bundled continuous bilinear forms that
carry a variational problem. -/
theorem ContinuousLinearMap.sq_apply_le_apply_self_mul_apply_self
    (hsymm : ∀ u v : V, B u v = B v u) (hnonneg : ∀ w : V, 0 ≤ B w w) (u v : V) :
    B u v ^ 2 ≤ B u u * B v v := by
  let B' : LinearMap.BilinForm ℝ V :=
    LinearMap.mk₂ ℝ (fun u v => B u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have hB' : B'.IsPosSemidef :=
    (LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg B'
      (LinearMap.BilinForm.isSymm_def.2 hsymm)).2 hnonneg
  exact hB'.sq_apply_le_mul_apply_self u v

end CauchySchwarz

namespace IsCoercive

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {B : V →L[ℝ] V →L[ℝ] ℝ}

omit [CompleteSpace V] in
/-- A coercive form has nonnegative diagonal. -/
theorem apply_self_nonneg (hB : IsCoercive B) (v : V) : 0 ≤ B v v := by
  obtain ⟨C, hC, hle⟩ := id hB
  refine le_trans ?_ (hle v)
  positivity

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
    ContinuousLinearMap.sq_apply_le_apply_self_mul_apply_self hsymm hB.apply_self_nonneg w v
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
problem this is the Poincaré inequality with the first eigenvalue as its constant.  No
hypothesis beyond symmetry is needed: when `S = 0` the left-hand side vanishes and the bound is
the nonnegativity of the energy. -/
theorem inv_norm_formSolutionOperator_mul_norm_apply_sq_le (hB : IsCoercive B) (J : V →L[ℝ] H)
    (hsymm : ∀ u v : V, B u v = B v u) (v : V) :
    ‖hB.formSolutionOperator J‖⁻¹ * ‖J v‖ ^ 2 ≤ B v v := by
  rcases eq_or_lt_of_le (norm_nonneg (hB.formSolutionOperator J)) with hzero | hpos
  · rw [← hzero]
    simpa using hB.apply_self_nonneg v
  · rw [inv_mul_le_iff₀ hpos]
    linarith [hB.norm_apply_sq_le_norm_formSolutionOperator_mul J hsymm v]

/-! ### Attainment at the first variational eigenvalue -/

/-- **The reciprocal of the norm of the solution operator is a variational eigenvalue.**  It is
the least one, by `IsCoercive.isLeast_rayleighQuotient`.  Compactness of `J` is what makes `‖S‖`
itself an eigenvalue of `S`, and positivity of `S` is what excludes `-‖S‖`. -/
theorem exists_ne_zero_forall_apply_eq_inv_norm_smul_inner (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    ∃ u : V, u ≠ 0 ∧
      ∀ v : V, B u v = ‖hB.formSolutionOperator J‖⁻¹ * ⟪J u, J v⟫_ℝ := by
  obtain ⟨w, hw⟩ : ∃ w : V, J w ≠ 0 := by
    simpa only [zero_apply] using DFunLike.ne_iff.mp hJne
  have _ : Nontrivial H := nontrivial_of_ne (J w) 0 hw
  set S := hB.formSolutionOperator J with hS
  have hSne : S ≠ 0 := fun hzero =>
    hw (inner_self_eq_zero.mp ((hB.formSolutionOperator_apply_eq_zero_iff J (J w)).mp
      (by rw [← hS, hzero, zero_apply]) w))
  have hnorm_pos : 0 < ‖S‖ := norm_pos_iff.mpr hSne
  have hcompact : IsCompactOperator S := hB.isCompactOperator_formSolutionOperator hJ
  have hsym : LinearMap.IsSymmetric (S : H →ₗ[ℝ] H) := hB.isSymmetric_formSolutionOperator J hsymm
  have hnorm_or_neg : ‖S‖ ∈ spectrum ℝ S ∨ -‖S‖ ∈ spectrum ℝ S := by
    simp_rw [spectrum, Set.mem_compl_iff]
    by_contra! h
    obtain ⟨d, hd, hle⟩ := S.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
    have hsup := ciSup_le hle
    have heq := ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hsym
    linarith
  have hnorm_mem : ‖S‖ ∈ spectrum ℝ S := hnorm_or_neg.resolve_right fun hneg => by
    have hneg_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) (-‖S‖) :=
      (hcompact.hasEigenvalue_iff_mem_spectrum (neg_ne_zero.mpr hnorm_pos.ne')).mpr hneg
    have hnonneg : 0 ≤ -‖S‖ := eigenvalue_nonneg_of_nonneg hneg_eigen fun f => by
      simpa [hS] using hB.inner_formSolutionOperator_self_nonneg J f
    linarith
  have hnorm_eigen : HasEigenvalue (S : H →ₗ[ℝ] H) ‖S‖ :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hnorm_pos.ne').mpr hnorm_mem
  refine (hB.hasEigenvalue_formSolutionOperator_iff J (inv_ne_zero hnorm_pos.ne')).mp ?_
  simpa using hnorm_eigen

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

/-- **The first variational eigenvalue is the optimal constant** in the inequality
`C ‖J v‖² ≤ B v v`: it satisfies the inequality, and no larger constant does.  For the Dirichlet
problem this identifies the first eigenvalue with the best Poincaré constant. -/
theorem isGreatest_setOf_forall_mul_norm_apply_sq_le (hB : IsCoercive B) {J : V →L[ℝ] H}
    (hJ : IsCompactOperator J) (hsymm : ∀ u v : V, B u v = B v u) (hJne : J ≠ 0) :
    IsGreatest {C : ℝ | ∀ v : V, C * ‖J v‖ ^ 2 ≤ B v v} ‖hB.formSolutionOperator J‖⁻¹ := by
  obtain ⟨u, hu, heq⟩ := hB.exists_ne_zero_forall_apply_eq_inv_norm_smul_inner hJ hsymm hJne
  have hJu : J u ≠ 0 := hB.apply_ne_zero_of_forall_apply_eq_smul_inner J hu heq
  refine ⟨fun v => hB.inv_norm_formSolutionOperator_mul_norm_apply_sq_le J hsymm v, fun C hC => ?_⟩
  have hself : B u u = ‖hB.formSolutionOperator J‖⁻¹ * ‖J u‖ ^ 2 := by
    rw [heq u, real_inner_self_eq_norm_sq]
  exact le_of_mul_le_mul_right (by rw [← hself]; exact hC u) (by positivity : (0 : ℝ) < ‖J u‖ ^ 2)

end IsCoercive
