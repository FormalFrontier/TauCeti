/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Ring.Units
public import Mathlib.GroupTheory.Index

/-!
# Finite index of the positive-units subgroup

For a linearly ordered ring, the positive units `Units.posSubgroup R` form an index-`2` subgroup, so
it has finite index; and its preimage under any group homomorphism into `Rˣ` (for a linearly ordered
commutative ring `R`) has finite index too. These are the general facts behind the finiteness of the
totally positive units of a number field, hence of its narrow class group.
-/

public section

/-- The positive units of a linearly ordered ring form an index-`2`, hence finite-index,
subgroup. -/
instance instFiniteIndexPosSubgroup (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R] :
    (Units.posSubgroup R).FiniteIndex :=
  ⟨by rw [Units.index_posSubgroup]; decide⟩

/-- The preimage of the positive units under any homomorphism into `Rˣ` (for a linearly ordered
commutative ring `R`) has finite index: it is the kernel of the composite into the two-element sign
group `Rˣ ⧸ Units.posSubgroup R`. -/
instance instFiniteIndexComapPosSubgroup {G R : Type*} [Group G] [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (f : G →* Rˣ) : ((Units.posSubgroup R).comap f).FiniteIndex := by
  rw [← QuotientGroup.ker_mk' (Units.posSubgroup R), MonoidHom.comap_ker]
  infer_instance
