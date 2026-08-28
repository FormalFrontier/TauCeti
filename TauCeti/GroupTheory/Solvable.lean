/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable

/-!
# Solvability of a direct product

The two projections out of a direct product are surjective, and solvability transports along a
surjection, so a solvable product has solvable factors. In the other direction a product of two
solvable groups is solvable. This file packages the two directions as a single characterisation.

## Main results

* `TauCeti.isSolvable_prod_iff`: `G × H` is solvable if and only if both `G` and `H` are.
-/

public section

namespace TauCeti

/-- A direct product of groups is solvable exactly when both of its factors are. -/
@[simp]
theorem isSolvable_prod_iff {G H : Type*} [Group G] [Group H] :
    Group.IsSolvable (G × H) ↔ Group.IsSolvable G ∧ Group.IsSolvable H :=
  ⟨fun _ ↦ ⟨Group.isSolvable_of_surjective (f := MonoidHom.fst G H) fun x ↦ ⟨(x, 1), rfl⟩,
      Group.isSolvable_of_surjective (f := MonoidHom.snd G H) fun x ↦ ⟨(1, x), rfl⟩⟩,
    fun ⟨_, _⟩ ↦ inferInstance⟩

end TauCeti
