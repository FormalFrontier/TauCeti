/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The bounded part of Stone's theorem

This file begins the converse direction of Stone's theorem.  A bounded self-adjoint operator
`A` on a complex Hilbert space gives the unitary group `exp (t i A)`; its real-linear generator is
the expected operator `i A`.
-/

public section

noncomputable section

open scoped InnerProductSpace Topology

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded Stone group associated to a self-adjoint operator. -/
def ofBoundedSelfAdjoint (A : H →L[ℂ] H) : StronglyContinuousGroup H :=
  ofBounded ((Complex.I • A).restrictScalars ℝ)

private theorem restrictScalars_exp (A : H →L[ℂ] H) (t : ℝ) :
    NormedSpace.exp (t • A.restrictScalars ℝ) =
      (NormedSpace.exp ((t : ℂ) • A)).restrictScalars ℝ := by
  let _i : Module ℚ H := Module.compHom H (algebraMap ℚ ℂ)
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  let +nondep : NormedAlgebra ℚ (H →L[ℝ] H) := .restrictScalars ℚ ℝ _
  let φ : (H →L[ℂ] H) →+* (H →L[ℝ] H) :=
    { toFun := fun B => B.restrictScalars ℝ
      map_one' := by ext x; rfl
      map_mul' := by intro B C; ext x; rfl
      map_zero' := by ext x; rfl
      map_add' := by intro B C; ext x; rfl }
  have hφ : Continuous φ := by
    change Continuous (fun B : H →L[ℂ] H => B.restrictScalars ℝ)
    exact (ContinuousLinearMap.restrictScalarsIsometry ℂ H H ℝ ℝ).continuous
  have h := NormedSpace.map_exp φ hφ ((t : ℂ) • A)
  have hsmul : φ ((t : ℂ) • A) = t • φ A := by
    ext x
    rfl
  rw [hsmul] at h
  exact h.symm

/-- At time `t`, the bounded Stone group is the complex exponential regarded as real-linear. -/
@[simp]
theorem ofBoundedSelfAdjoint_apply (A : H →L[ℂ] H) (t : ℝ) :
    ofBoundedSelfAdjoint A t =
      (NormedSpace.exp ((t : ℂ) • (Complex.I • A))).restrictScalars ℝ := by
  rw [ofBoundedSelfAdjoint, ofBounded_apply, restrictScalars_exp]

/-- The bounded Stone group is unitary. -/
theorem ofBoundedSelfAdjoint_isUnitary (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary (ofBoundedSelfAdjoint A) := by
  apply (TauCeti.Semigroups.StronglyContinuousGroup.isUnitary_iff_inner_map_map _).mpr
  refine fun t x y => ?_
  rw [ofBoundedSelfAdjoint_apply]
  let _i : Module ℚ H := Module.compHom H (algebraMap ℚ ℂ)
  let +nondep : NormedAlgebra ℚ (H →L[ℂ] H) := .restrictScalars ℚ ℂ _
  have hskew : Complex.I • A ∈ skewAdjoint (H →L[ℂ] H) := by
    rw [Complex.I_smul_mem_skewAdjoint_iff_isSelfAdjoint]
    exact hA
  have hscaled : t • (Complex.I • A) ∈ skewAdjoint (H →L[ℂ] H) :=
    skewAdjoint.smul_mem t hskew
  have hu0 : NormedSpace.exp (t • (Complex.I • A)) ∈ unitary (H →L[ℂ] H) :=
    NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hscaled
  have hu : NormedSpace.exp ((t : ℂ) • (Complex.I • A)) ∈ unitary (H →L[ℂ] H) := by
    simpa only [Complex.coe_smul] using hu0
  have hu' := Unitary.star_mul_self_of_mem hu
  rw [ContinuousLinearMap.star_eq_adjoint] at hu'
  have hu'' := congrArg (fun B : H →L[ℂ] H => ⟪B x, y⟫_ℂ) hu'
  rw [mul_apply_eq_comp, one_apply_eq_self,
    ContinuousLinearMap.adjoint_inner_left] at hu''
  exact hu''

/-- The generator of the bounded Stone group is `i A`, regarded as a real partial linear map. -/
@[simp]
theorem ofBoundedSelfAdjoint_generator (A : H →L[ℂ] H) :
    (ofBoundedSelfAdjoint A).generator =
      ((Complex.I • A).restrictScalars ℝ).toLinearMap.toPMap ⊤ := by
  exact ofBounded_generator _

end StronglyContinuousGroup

end TauCeti.Semigroups

end
