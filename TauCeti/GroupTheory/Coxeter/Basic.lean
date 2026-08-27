/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Elementary facts about Coxeter words

This file gives convenient evaluations of Mathlib's alternating words of lengths two and three,
and records the degenerate rank-zero case: a Coxeter system whose simple reflections are indexed
by an empty type has a trivial group.

## Main results

* `TauCeti.subsingleton_of_isEmpty_index`: a Coxeter system of rank zero has a trivial group.
-/

public section

namespace TauCeti

variable {B N : Type*} [Monoid N]

/-- The alternating word of length `2`. -/
private theorem alternatingWord_two (i i' : B) :
    CoxeterSystem.alternatingWord i i' 2 = [i, i'] := rfl

/-- The alternating word of length `3`. -/
private theorem alternatingWord_three (i i' : B) :
    CoxeterSystem.alternatingWord i i' 3 = [i', i, i'] := rfl

/-- An alternating word of length `2`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_two (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 2).map f).prod = f i * f i' := by
  rw [alternatingWord_two]
  simp

/-- An alternating word of length `3`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_three (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 3).map f).prod = f i' * f i * f i' := by
  rw [alternatingWord_three]
  simp [mul_assoc]

/-! ### Rank zero -/

variable {W : Type*} [Group W] {M : CoxeterMatrix B}

/-- A Coxeter system whose simple reflections are indexed by an empty type has a trivial group:
every element is the product of a word in the generators, and the only such word is empty. -/
theorem subsingleton_of_isEmpty_index (cs : CoxeterSystem M W) [IsEmpty B] : Subsingleton W :=
  cs.wordProd_surjective.subsingleton

end TauCeti
