/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Integrality in the rational circle group

A rational number reduces to zero in `ℚ/ℤ`, realized as `AddCircle (1 : ℚ)`, exactly when it
lies in `(1 : Submodule ℤ ℚ)`, the copy of `ℤ` inside `ℚ`. This bridges the two spellings of
integrality used by the discriminant-form theory: vanishing in the circle group and membership
in the unit `ℤ`-submodule.

## Main declarations

* `AddCircle.coe_eq_zero_iff_mem_one`: vanishing in `AddCircle (1 : ℚ)` is membership in
  `(1 : Submodule ℤ ℚ)`.
-/

public section

namespace AddCircle

/-- A rational number reduces to zero in `ℚ/ℤ` exactly when it is an integer. -/
theorem coe_eq_zero_iff_mem_one (q : ℚ) :
    (q : AddCircle (1 : ℚ)) = 0 ↔ q ∈ (1 : Submodule ℤ ℚ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (coe_eq_zero_iff (1 : ℚ)).mp h
    exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
    exact (coe_eq_zero_iff (1 : ℚ)).mpr ⟨n, by simpa using hn⟩

end AddCircle
