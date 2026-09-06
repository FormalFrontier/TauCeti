/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Scalar towers one step below an intermediate field

Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an intermediate
field `E` of `L / K`.  The same statement holds one step further down: any commutative semiring
acting compatibly below `K` also acts compatibly through `E`.

## Main results

* `TauCeti.instIsScalarTowerIntermediateField`: `IsScalarTower k E L` for an intermediate field
  `E` of `L / K` and a base `k` below `K`.
-/

public section

namespace TauCeti

/-- Mathlib's `IntermediateField.isScalarTower_mid` supplies `IsScalarTower K E L` for an
intermediate field `E` of `L / K`; this is the same statement for a base `k` sitting below `K`,
which is what an object of `L` defined over `k` needs in order to be restricted to `E`. -/
instance instIsScalarTowerIntermediateField {k K L : Type*} [CommSemiring k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    (E : IntermediateField K L) : IsScalarTower k E L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end TauCeti
