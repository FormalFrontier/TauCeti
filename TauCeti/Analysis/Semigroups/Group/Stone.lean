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

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

/-- The exponential group associated to a bounded operator. It is unitary when the operator is
self-adjoint. -/
def ofBoundedExp (A : H →L[ℂ] H) : StronglyContinuousGroup H :=
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
    -- The local normed-algebra instances give `φ` a bundled topology; expose its underlying
    -- function so that the restriction isometry supplies continuity for the normed topologies.
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
theorem ofBoundedExp_apply (A : H →L[ℂ] H) (t : ℝ) :
    ofBoundedExp A t =
      (NormedSpace.exp ((t : ℂ) • (Complex.I • A))).restrictScalars ℝ := by
  rw [ofBoundedExp, ofBounded_apply, restrictScalars_exp]

/-- The generator of the bounded exponential group is `i A`, regarded as a real partial linear
map. -/
@[simp]
theorem ofBoundedExp_generator (A : H →L[ℂ] H) :
    (ofBoundedExp A).generator =
      ((Complex.I • A).restrictScalars ℝ).toLinearMap.toPMap ⊤ := by
  exact ofBounded_generator _

end StronglyContinuousGroup

section

namespace StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded exponential group is unitary when its operator is self-adjoint. -/
theorem isUnitary_ofBoundedExp (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary (ofBoundedExp A) := by
  refine IsUnitary.intro fun t x y => ?_
  rw [ofBoundedExp_apply]
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
  exact (NormedSpace.exp ((t : ℂ) • (Complex.I • A))).inner_map_map_of_mem_unitary hu x y

end StronglyContinuousGroup

end

end TauCeti.Semigroups

end
