/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Elementary facts about Coxeter words

This file gives convenient evaluations of Mathlib's alternating words: those of lengths two and
three, and those of even length, which are the ones the braid relations are read off. It also
records the degenerate rank-zero case: a Coxeter system whose simple reflections are indexed by an
empty type has a trivial group.

## Main results

* `TauCeti.prod_map_alternatingWord_two_mul`: an alternating word of length `2 * m`, evaluated
  through any family `f`, is the `m`-th power of `f i * f i'`. This is the shape in which a braid
  relation is checked against a family that is not yet known to satisfy it, so it cannot be routed
  through `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple
  reflections themselves.
* `TauCeti.reverse_alternatingWord_two_mul`: reversing an alternating word of even length swaps its
  two letters.
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

/-! ### Alternating words of even length -/

/-- An alternating word of even length grows by one letter at each end: `2 * (m + 1)` letters are
the two letters `i`, `i'` followed by the alternating word of length `2 * m`. -/
private theorem alternatingWord_two_mul_succ (i i' : B) (m : ℕ) :
    CoxeterSystem.alternatingWord i i' (2 * (m + 1))
      = i :: i' :: CoxeterSystem.alternatingWord i i' (2 * m) := by
  have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [h, CoxeterSystem.alternatingWord_succ', CoxeterSystem.alternatingWord_succ']
  simp

/-- The same word read from the other end: the alternating word of length `2 * (m + 1)` is the
alternating word of length `2 * m` followed by the two letters `i`, `i'`. -/
private theorem alternatingWord_two_mul_succ' (i i' : B) (m : ℕ) :
    CoxeterSystem.alternatingWord i i' (2 * (m + 1))
      = CoxeterSystem.alternatingWord i i' (2 * m) ++ [i, i'] := by
  have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  rw [h, CoxeterSystem.alternatingWord_succ, CoxeterSystem.alternatingWord_succ]
  simp

/-- An alternating word of length `2 * m`, evaluated through any family `f`, is the `m`-th power of
`f i * f i'`. Unlike `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates the word at
the simple reflections of a Coxeter system, this holds for an arbitrary family, so it is available
while checking that a family satisfies the braid relations. -/
theorem prod_map_alternatingWord_two_mul (f : B → N) (i i' : B) (m : ℕ) :
    ((CoxeterSystem.alternatingWord i i' (2 * m)).map f).prod = (f i * f i') ^ m := by
  induction m with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih => rw [alternatingWord_two_mul_succ' i i' m]; simp [ih, pow_succ]

/-- Reversing an alternating word of even length swaps its two letters. -/
theorem reverse_alternatingWord_two_mul (i i' : B) (m : ℕ) :
    (CoxeterSystem.alternatingWord i i' (2 * m)).reverse
      = CoxeterSystem.alternatingWord i' i (2 * m) := by
  induction m with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    rw [alternatingWord_two_mul_succ' i i' m, alternatingWord_two_mul_succ i' i m]
    simp [ih]

/-! ### Rank zero -/

variable {W : Type*} [Group W] {M : CoxeterMatrix B}

/-- A Coxeter system whose simple reflections are indexed by an empty type has a trivial group:
every element is the product of a word in the generators, and the only such word is empty. -/
theorem subsingleton_of_isEmpty_index (cs : CoxeterSystem M W) [IsEmpty B] : Subsingleton W :=
  cs.wordProd_surjective.subsingleton

end TauCeti
