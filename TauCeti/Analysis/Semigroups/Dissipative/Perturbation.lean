/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.LinearPMap.Shift
public import TauCeti.Analysis.Normed.Operator.Resolvent.Perturbation
public import TauCeti.Analysis.Semigroups.Dissipative.Basic

/-!
# Dissipativity under a bounded perturbation

Adding a bounded operator `B` to an unbounded operator `A` costs at most `‖B‖` of dissipativity:
if `A` is dissipative then `B + A - ‖B‖ I` is again dissipative, because the triangle inequality
absorbs `B x` into the extra `‖B‖ ‖x‖` gained by shifting the spectral parameter. Maximality is
inherited too: the range condition for the perturbed operator comes from the Neumann
perturbation of a resolvent point
(`TauCeti.LinearPMap.mem_resolventSet_vadd`), applied at a spectral parameter large enough that
`‖B‖ ‖R(lambda, A)‖ < 1`.

Together these say that the Lumer--Phillips hypothesis set is stable under bounded
perturbations, which is what makes the bounded perturbation theorem for generators
(`TauCeti.Semigroups.IsMDissipative.exists_stronglyContinuousSemigroup_generator_eq_vadd`) a
consequence of Lumer--Phillips.

## Main results

* `TauCeti.Semigroups.IsDissipative.subScalar_vadd`: `B + A - ‖B‖ I` is dissipative.
* `TauCeti.Semigroups.IsMDissipative.subScalar_vadd`: `B + A - ‖B‖ I` is m-dissipative.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section III.1;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 3, Theorem 1.1.
-/

public section

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : X →ₗ.[ℝ] X}

/-- **Dissipativity survives a bounded perturbation**, at the cost of shifting by `‖B‖`: if `A`
is dissipative and `B` is bounded, then `B + A - ‖B‖ I` is dissipative. -/
theorem IsDissipative.subScalar_vadd (hA : IsDissipative A) (B : X →L[ℝ] X) :
    IsDissipative (LinearPMap.subScalar ((B : X →ₗ[ℝ] X) +ᵥ A) ‖B‖) := by
  rw [LinearPMap.subScalar_vadd]
  intro mu hmu x
  have hstep : mu • (x : X) -
      (((B : X →ₗ[ℝ] X) - ‖B‖ • LinearMap.id) +ᵥ A) x
      = ((mu + ‖B‖) • (x : X) - A x) - B (x : X) := by
    rw [LinearPMap.vadd_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hdis : (mu + ‖B‖) * ‖(x : X)‖ ≤ ‖(mu + ‖B‖) • (x : X) - A x‖ :=
    hA (mu + ‖B‖) (by linarith [norm_nonneg B]) ⟨(x : X), x.2⟩
  rw [add_mul] at hdis
  have hBx : ‖B (x : X)‖ ≤ ‖B‖ * ‖(x : X)‖ := B.le_opNorm _
  rw [hstep]
  calc mu * ‖(x : X)‖
      ≤ ‖(mu + ‖B‖) • (x : X) - A x‖ - ‖B (x : X)‖ := by linarith
    _ ≤ ‖((mu + ‖B‖) • (x : X) - A x) - B (x : X)‖ := norm_sub_norm_le _ _

variable [CompleteSpace X]

/-- **Maximal dissipativity survives a bounded perturbation.** If `A` is m-dissipative and `B` is
bounded, then `B + A - ‖B‖ I` is m-dissipative. -/
theorem IsMDissipative.subScalar_vadd (hA : IsMDissipative A) (B : X →L[ℝ] X) :
    IsMDissipative (LinearPMap.subScalar ((B : X →ₗ[ℝ] X) +ᵥ A) ‖B‖) := by
  have hdis := hA.isDissipative.subScalar_vadd B
  rw [LinearPMap.subScalar_vadd] at hdis ⊢
  refine hdis.isMDissipative (lambda := ‖B‖ + 1) (by positivity) fun y => ?_
  have hmupos : (0 : ℝ) < 2 * ‖B‖ + 1 := by positivity
  have hres : (2 * ‖B‖ + 1) ∈ LinearPMap.resolventSet A := hA.mem_resolventSet hmupos
  have hbound : ‖LinearPMap.resolvent A (2 * ‖B‖ + 1)‖ ≤ (2 * ‖B‖ + 1)⁻¹ :=
    hA.norm_resolvent_le hmupos
  have hsmall : ‖B‖ * (2 * ‖B‖ + 1)⁻¹ < 1 := by
    rw [mul_inv_lt_iff₀ hmupos, one_mul]
    linarith [norm_nonneg B]
  obtain ⟨z, hz⟩ := (LinearPMap.smul_sub_bijective
    (LinearPMap.mem_resolventSet_vadd B hres hbound hsmall)).surjective y
  have hgoal : (‖B‖ + 1) • (z : X) - (((B : X →ₗ[ℝ] X) - ‖B‖ • LinearMap.id) +ᵥ A) z
      = (2 * ‖B‖ + 1) • (z : X) - ((B : X →ₗ[ℝ] X) +ᵥ A) z := by
    rw [LinearPMap.vadd_apply, LinearPMap.vadd_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    module
  exact ⟨z, hgoal.trans hz⟩

end TauCeti.Semigroups

end
