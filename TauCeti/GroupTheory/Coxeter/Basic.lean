/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Elementary facts about Coxeter words

This file evaluates Mathlib's alternating words through an arbitrary family, and specialises that
evaluation to the lengths the braid relations are read off at. It also records the degenerate
rank-zero case: a Coxeter system whose simple reflections are indexed by an empty type has a
trivial group.

## Main results

* `TauCeti.prod_map_alternatingWord`: an alternating word of length `m`, evaluated through any
  family `f`. This is the shape in which a braid relation is checked against a family that is not
  yet known to satisfy it, so it cannot be routed through
  `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple reflections
  themselves. The evaluations at lengths `2`, `3` and `2 * m` are special cases.
* `TauCeti.reverse_alternatingWord_two_mul`: reversing an alternating word of even length swaps its
  two letters.
* `TauCeti.subsingleton_of_isEmpty_index`: a Coxeter system of rank zero has a trivial group.
-/

public section

namespace TauCeti

variable {B N : Type*} [Monoid N]

/-- An alternating word of length `m`, evaluated through any family `f`. Unlike
`CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates the word at the simple reflections
of a Coxeter system, this holds for an arbitrary family, so it is available while checking that a
family satisfies the braid relations. -/
theorem prod_map_alternatingWord (f : B → N) (i i' : B) (m : ℕ) :
    ((CoxeterSystem.alternatingWord i i' m).map f).prod
      = (if Even m then 1 else f i') * (f i * f i') ^ (m / 2) := by
  induction m with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    rw [CoxeterSystem.alternatingWord_succ', List.map_cons, List.prod_cons, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]

/-- An alternating word of length `2`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_two (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 2).map f).prod = f i * f i' := by
  simp [prod_map_alternatingWord]

/-- An alternating word of length `3`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_three (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 3).map f).prod = f i' * f i * f i' := by
  simp [prod_map_alternatingWord, Nat.even_iff, mul_assoc]

/-! ### Alternating words of even length -/

/-- The alternating word of length `2 * (m + 1)` is the two letters `i`, `i'` followed by the
alternating word of length `2 * m`. -/
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
`f i * f i'`. -/
theorem prod_map_alternatingWord_two_mul (f : B → N) (i i' : B) (m : ℕ) :
    ((CoxeterSystem.alternatingWord i i' (2 * m)).map f).prod = (f i * f i') ^ m := by
  simp [prod_map_alternatingWord]

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
