/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Sobolev.WeakDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Test functions as elements of `Lp`

This file provides the generic bridge from compactly supported test functions on an open set to
`Lp` classes. A test function belongs to every `Lᵖ` space for any measure finite on compact sets.
The construction is used by the closed-graph presentations of weak Sobolev spaces.

The bridge is linear: `TauCeti.testFunctionLp_add` and `TauCeti.testFunctionLp_smul` record that
passing to the `Lᵖ` class commutes with the vector space structure of the test functions. For an
inner product space, `TauCeti.gradientTestFunctionLp` provides the parallel construction for the
gradient. These facts make the image of `C_c^∞(Ω)` in an `Lᵖ`-based function space a subspace.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [OpensMeasurableSpace E] {mu : Measure E} [IsFiniteMeasureOnCompacts mu] {Omega : Opens E}

/-- A test function on `Omega` lies in every `Lᵠ(Omega)`: it is continuous with compact support. -/
theorem memLp_testFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    MemLp (phi : E → ℝ) q (mu.restrict Omega) :=
  phi.continuous.memLp_of_hasCompactSupport phi.hasCompactSupport

/-- A test function on `Omega` as an element of `Lᵠ(Omega)`. -/
def testFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) : Lp ℝ q (mu.restrict Omega) :=
  (memLp_testFunction (mu := mu) q phi).toLp phi

@[simp]
theorem testFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, testFunctionLp (mu := mu) q phi x = phi x :=
  (memLp_testFunction (mu := mu) q phi).coeFn_toLp

/-- The norm of a test function's `Lᵖ` class is its `eLpNorm`, converted to `ℝ`. -/
theorem norm_testFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := mu) q phi‖ =
      (eLpNorm (phi : E → ℝ) q (mu.restrict Omega)).toReal :=
  Lp.norm_toLp _ _

@[simp]
theorem testFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (phi + psi) =
      testFunctionLp (mu := mu) q phi + testFunctionLp (mu := mu) q psi := by
  rw [testFunctionLp, testFunctionLp, testFunctionLp, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (FunLike.coe_add phi psi) x

@[simp]
theorem testFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (c • phi) = c • testFunctionLp (mu := mu) q phi := by
  rw [testFunctionLp, testFunctionLp, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (FunLike.coe_smul c phi) x

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Omega : Opens E}

/-! ### The gradient of a test function -/

/-- The gradient of a test function is continuous. -/
@[fun_prop]
theorem continuous_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    Continuous fun x => ∇ (phi : E → ℝ) x :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (phi.contDiff.continuous_fderiv (by simp))

/-- The gradient of a test function has compact support. -/
theorem hasCompactSupport_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    HasCompactSupport fun x => ∇ (phi : E → ℝ) x :=
  (phi.hasCompactSupport.fderiv ℝ).comp_left (map_zero _)

/-- The gradient of a test function on `Ω` vanishes outside `Ω`. -/
theorem support_gradient_testFunction_subset (phi : 𝓓(Omega, ℝ)) :
    Function.support (fun x => ∇ (phi : E → ℝ) x) ⊆ (Omega : Set E) :=
  (Function.support_comp_subset (map_zero (InnerProductSpace.toDual ℝ E).symm) _).trans <|
    (subset_tsupport _).trans <| (tsupport_fderiv_subset ℝ).trans phi.tsupport_subset

variable [MeasurableSpace E] [OpensMeasurableSpace E] {mu : Measure E}
  [IsFiniteMeasureOnCompacts mu]

/-- The gradient of a test function on `Ω` is continuous with compact support, so it lies in every
`Lᵠ(Ω)`. -/
theorem memLp_gradient_testFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    MemLp (fun x => ∇ (phi : E → ℝ) x) q (mu.restrict Omega) :=
  (continuous_gradient_testFunction phi).memLp_of_hasCompactSupport
    (hasCompactSupport_gradient_testFunction phi)

/-- The gradient of a test function on `Ω`, as an element of `Lᵠ(Ω, E)`. -/
def gradientTestFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) : Lp E q (mu.restrict Omega) :=
  (memLp_gradient_testFunction (mu := mu) q phi).toLp _

@[simp]
theorem gradientTestFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, gradientTestFunctionLp (mu := mu) q phi x = ∇ (phi : E → ℝ) x :=
  (memLp_gradient_testFunction (mu := mu) q phi).coeFn_toLp

/-- The norm of a test function gradient's `Lᵖ` class is its `eLpNorm`, converted to `ℝ`. -/
theorem norm_gradientTestFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := mu) q phi‖ =
      (eLpNorm (fun x => ∇ (phi : E → ℝ) x) q (mu.restrict Omega)).toReal :=
  Lp.norm_toLp _ _

@[simp]
theorem gradientTestFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (phi + psi) =
      gradientTestFunctionLp (mu := mu) q phi + gradientTestFunctionLp (mu := mu) q psi := by
  rw [gradientTestFunctionLp, gradientTestFunctionLp, gradientTestFunctionLp,
    ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => gradient_add ((phi.contDiff.differentiable (by simp)) x)
    ((psi.contDiff.differentiable (by simp)) x)

@[simp]
theorem gradientTestFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (c • phi) =
      c • gradientTestFunctionLp (mu := mu) q phi := by
  rw [gradientTestFunctionLp, gradientTestFunctionLp, ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => by simpa using gradient_const_smul (f := (phi : E → ℝ)) (x := x) c

end Gradient

end TauCeti
