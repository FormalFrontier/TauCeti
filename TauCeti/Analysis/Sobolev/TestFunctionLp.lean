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

end TauCeti
