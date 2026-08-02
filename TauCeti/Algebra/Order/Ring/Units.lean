/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Ring.Units

/-!
# Finite index of the positive-units subgroup

For a linearly ordered ring, the positive units `Units.posSubgroup R` form an index-`2` subgroup, so
it has finite index. Together with the general finite-index-preimage instance
(`Subgroup.instFiniteIndexComap`), this yields the finiteness of the totally positive units of a
number field, hence of its narrow class group.
-/

public section

namespace Units

/-- The positive units of a linearly ordered ring form an index-`2`, hence finite-index,
subgroup. -/
instance instFiniteIndexPosSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (Units.posSubgroup R).FiniteIndex :=
  ⟨by rw [Units.index_posSubgroup]; decide⟩

end Units
