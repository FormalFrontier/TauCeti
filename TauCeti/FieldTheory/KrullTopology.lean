/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology

/-!
# Stabilizers for the Krull topology are open

`Mathlib/FieldTheory/KrullTopology.lean` supplies the Krull topology on `Gal(L/K)` together with
`stabilizer_isOpen_of_isIntegral`, the fact that a point of an integral extension `L/K` has an
**open** stabilizer. This file draws the consequence for a *unit* of `L`, an automorphism fixing
a unit being exactly one that fixes the underlying element.

Through Mathlib's `continuousSMul_iff_stabilizer_isOpen` this is what makes the units of an
algebraic extension a *discrete module* over the Galois group, in the sense continuous cohomology
asks for; `TauCeti.unitsCoeff_continuousSMul` is that consequence for a separable closure.

## Main results

* `TauCeti.stabilizer_isOpen_units`: the stabilizer of a unit of `L` is an open subgroup of
  `Gal(L/K)`.
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The stabilizer of a unit of an integral extension is open: an automorphism fixes a unit
exactly when it fixes the underlying element. -/
theorem stabilizer_isOpen_units [Algebra.IsIntegral K L] (u : Lˣ) :
    IsOpen (MulAction.stabilizer Gal(L/K) u : Set Gal(L/K)) := by
  convert stabilizer_isOpen_of_isIntegral (K := K) (u : L) using 2
  ext σ
  simp [MulAction.mem_stabilizer_iff, Units.ext_iff]

end TauCeti
