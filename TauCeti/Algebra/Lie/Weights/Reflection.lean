/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

public section

/-!
# Reflections of the root system of a Cartan subalgebra

For a finite-dimensional Lie algebra `L` with non-degenerate Killing form over a field of
characteristic zero, and a splitting Cartan subalgebra `H`, Mathlib packages the roots of `H` as a
root system `LieAlgebra.IsKilling.rootSystem H` inside the dual `Module.Dual K H`. This file reads
its reflections back in Lie-theoretic terms: the reflection in a root `α` sends a form `χ` to
`χ - χ(α^∨) • α`, where `α^∨` is the coroot `LieAlgebra.IsKilling.coroot α`.

## Main results

* `TauCeti.coe_rootSystem_reflection_apply`: the reflection of the root system in a root, read as a
  function on the Cartan subalgebra.
-/

namespace TauCeti

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- The reflection of the root system of `H` in a root `i`, read as a function on the Cartan
subalgebra, is `χ ↦ χ - χ(αᵢ^∨) • αᵢ`. -/
@[simp] theorem coe_rootSystem_reflection_apply (i : H.root) (χ : Dual K H) :
    ⇑((IsKilling.rootSystem H).reflection i χ) =
      ⇑χ - χ (IsKilling.coroot (i : Weight K H L)) • ⇑(i : Weight K H L) := by
  ext x
  simp [RootPairing.reflection_apply, Weight.toLinear_apply]

end TauCeti
