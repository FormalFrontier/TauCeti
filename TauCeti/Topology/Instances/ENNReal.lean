/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Limits of `ℝ≥0∞`-valued functions

This file collects squeeze arguments for functions valued in `ℝ≥0∞`, where the usual
subtraction-based estimates are unavailable.

## Main declarations

* `TauCeti.tendsto_nhds_zero_of_le_enorm_mul`: a quantity dominated by `‖h‖ₑ` times a finite
  constant vanishes as `h → 0`.
-/

public section

namespace TauCeti

open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- A quantity dominated by `‖h‖ₑ` times a finite constant vanishes as `h → 0`. This is the form
in which a linear modulus of continuity yields the qualitative limit. -/
theorem tendsto_nhds_zero_of_le_enorm_mul {G : E → ℝ≥0∞} {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hG : ∀ h : E, G h ≤ ‖h‖ₑ * C) :
    Filter.Tendsto G (nhds 0) (nhds 0) := by
  have h0 : Filter.Tendsto (fun h : E => ‖h‖ₑ) (nhds 0) (nhds 0) :=
    continuous_enorm.tendsto' 0 0 (by simp)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hC)) (fun _ => zero_le) hG

end TauCeti
