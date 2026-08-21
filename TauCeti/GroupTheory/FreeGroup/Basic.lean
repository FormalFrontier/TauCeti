/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Elementary lemmas about free groups

This file records general-purpose facts about evaluating words in free-group generators.
-/

public section

namespace TauCeti

/-- A monoid homomorphism out of a free group spells out a word in the generators letter by
letter. This is `map_list_prod` packaged for words `ω : List B` read through `FreeGroup.of`. -/
theorem map_prod_map_freeGroupOf {B N : Type*} [Monoid N] (φ : FreeGroup B →* N) (ω : List B) :
    φ ((ω.map FreeGroup.of).prod) = (ω.map fun i ↦ φ (FreeGroup.of i)).prod := by
  rw [map_list_prod, List.map_map]
  rfl

end TauCeti
