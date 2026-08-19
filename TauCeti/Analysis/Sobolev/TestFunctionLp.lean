/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Test functions as elements of `Lp`

This file provides the generic bridge from compactly supported test functions on an open set to
`Lp` classes. A test function belongs to every `Lᵖ` space for any measure finite on compact sets.
The construction is used by the closed-graph presentations of weak Sobolev spaces.

The bridge is linear: `TauCeti.testFunctionLp_add` and `TauCeti.testFunctionLp_smul` record that
passing to the `Lᵖ` class commutes with the vector space structure of the test functions, which is
what makes the image of `C_c^∞(Ω)` in an `Lᵖ`-based function space a subspace.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace
open scoped ContDiff Distributions ENNReal

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

@[simp]
theorem testFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (phi + psi) =
      testFunctionLp (mu := mu) q phi + testFunctionLp (mu := mu) q psi := by
  apply Lp.ext
  filter_upwards [testFunctionLp_apply_ae (mu := mu) q (phi + psi),
    testFunctionLp_apply_ae (mu := mu) q phi, testFunctionLp_apply_ae (mu := mu) q psi,
    Lp.coeFn_add (testFunctionLp (mu := mu) q phi) (testFunctionLp (mu := mu) q psi)]
    with x hsum hphi hpsi hadd
  rw [hsum, hadd, Pi.add_apply, hphi, hpsi]
  simp

@[simp]
theorem testFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    testFunctionLp (mu := mu) q (c • phi) = c • testFunctionLp (mu := mu) q phi := by
  apply Lp.ext
  filter_upwards [testFunctionLp_apply_ae (mu := mu) q (c • phi),
    testFunctionLp_apply_ae (mu := mu) q phi,
    Lp.coeFn_smul c (testFunctionLp (mu := mu) q phi)] with x hsmul hphi hc
  rw [hsmul, hc, Pi.smul_apply, hphi]
  simp

end TauCeti
