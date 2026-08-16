/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Killing pairings of root spaces

This file records consequences of the non-degeneracy of the Killing form for root spaces of a
splitting Cartan subalgebra.

## Main results

* `TauCeti.killingForm_ne_zero_of_mem_rootSpace`: nonzero vectors in opposite root spaces have
  nonzero Killing pairing.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- Nonzero vectors in opposite root spaces have nonzero Killing pairing. -/
theorem killingForm_ne_zero_of_mem_rootSpace {α : Weight K H L} (hα : α.IsNonZero) {e f : L}
    (he : e ∈ rootSpace H α) (he₀ : e ≠ 0) (hf : f ∈ rootSpace H (-α)) (hf₀ : f ≠ 0) :
    killingForm K L e f ≠ 0 := by
  intro hef
  have hspan := LieAlgebra.IsKilling.toSubmodule_rootSpace_eq_span (-α) hα.neg f hf₀ hf
  have heker := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H he fun y hy ↦ by
    have hspan' : (rootSpace H (-((α : Weight K H L) : H → K))).toSubmodule = K ∙ f := by
      simpa only [Weight.coe_neg] using hspan
    -- Passing from a Lie submodule to its underlying submodule is definitional.
    change y ∈ (rootSpace H (-((α : Weight K H L) : H → K))).toSubmodule at hy
    rw [hspan'] at hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [hef]
  rw [ker_killingForm_eq_bot] at heker
  exact he₀ heker

end TauCeti
