/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Finite index of a preimage subgroup

The preimage `H.comap f` of a finite-index subgroup along a group homomorphism again has finite
index: its index is the relative index of `H` in the range of `f`, which is finite.
-/

public section

namespace Subgroup

/-- The preimage of a finite-index subgroup under a group homomorphism has finite index. -/
instance instFiniteIndexComap {G G' : Type*} [Group G] [Group G'] (H : Subgroup G) [H.FiniteIndex]
    (f : G' →* G) : (H.comap f).FiniteIndex :=
  ⟨by rw [index_comap]; exact FiniteIndex.index_ne_zero⟩

end Subgroup
