/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length

/-!
# The parity of the length function of a Coxeter system

Let `cs : CoxeterSystem M W` be a Coxeter system. Left multiplication by a fixed simple reflection
changes the length of an element by exactly one (`CoxeterSystem.length_mul_mod_two`), so it flips
the parity of the length. This file packages that pairing as an explicit equivalence
`TauCeti.lengthParityEquiv` between the elements of even length and the elements of odd length, and
records its two immediate consequences: the two parity classes are equinumerous, and a Coxeter
group with at least one simple reflection has even order.

The opposite degenerate case is recorded here as well: a Coxeter system whose simple reflections
are indexed by an empty type has a trivial group.

## Main definitions

* `TauCeti.lengthParityEquiv`: left multiplication by a simple reflection, as an equivalence
  between the even-length and the odd-length elements.

## Main results

* `TauCeti.subsingleton_of_isEmpty_index`: a Coxeter system of rank zero has a trivial group.
* `TauCeti.natCard_length_even_eq_natCard_length_odd`: as many elements have even length as odd
  length, provided there is at least one simple reflection.
* `TauCeti.even_natCard_of_nonempty_index`: hence a Coxeter group of positive rank has even order.

## References

These are the ingredients of the "length generating function ... the Poincaré polynomial" item
among the consequences of Layer 3 ("the missing Coxeter combinatorics") in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`; see
`TauCeti/GroupTheory/Coxeter/Poincare.lean`.

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 1.4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.11.
-/

public section

namespace TauCeti

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-! ### Rank zero -/

include cs in
/-- A Coxeter system whose simple reflections are indexed by an empty type has a trivial group:
every element is the product of a word in the generators, and the only such word is empty. -/
theorem subsingleton_of_isEmpty_index [IsEmpty B] : Subsingleton W := by
  constructor
  have hone : ∀ w : W, w = 1 := by
    intro w
    obtain ⟨ω, -, rfl⟩ := cs.exists_isReduced w
    cases ω with
    | nil => simp
    | cons i _ => exact (IsEmpty.false i).elim
  intro u v
  rw [hone u, hone v]

/-! ### Left multiplication by a simple reflection flips the parity of the length -/

/-- Multiplying on the left by a simple reflection changes the length by one, hence changes its
residue modulo two. -/
theorem length_simple_mul_mod_two (i : B) (w : W) :
    cs.length (cs.simple i * w) % 2 = (cs.length w + 1) % 2 := by
  rw [cs.length_mul_mod_two, cs.length_simple, Nat.add_comm]

/-- Left multiplication by a simple reflection turns an element of even length into one of odd
length, and only those. -/
@[simp]
theorem odd_length_simple_mul_iff (i : B) (w : W) :
    Odd (cs.length (cs.simple i * w)) ↔ Even (cs.length w) := by
  rw [Nat.odd_iff, Nat.even_iff, length_simple_mul_mod_two]
  omega

/-- Left multiplication by a simple reflection turns an element of odd length into one of even
length, and only those. -/
@[simp]
theorem even_length_simple_mul_iff (i : B) (w : W) :
    Even (cs.length (cs.simple i * w)) ↔ Odd (cs.length w) := by
  rw [Nat.even_iff, Nat.odd_iff, length_simple_mul_mod_two]
  omega

/-- **Left multiplication by a simple reflection matches the two parity classes.** It is an
involution of `W` exchanging the elements of even length with those of odd length. -/
def lengthParityEquiv (i : B) :
    {w : W // Even (cs.length w)} ≃ {w : W // Odd (cs.length w)} where
  toFun w := ⟨cs.simple i * (w : W), (odd_length_simple_mul_iff cs i _).mpr w.2⟩
  invFun w := ⟨cs.simple i * (w : W), (even_length_simple_mul_iff cs i _).mpr w.2⟩
  left_inv _ := Subtype.ext (cs.simple_mul_simple_cancel_left i)
  right_inv _ := Subtype.ext (cs.simple_mul_simple_cancel_left i)

/-- `lengthParityEquiv` is left multiplication by the simple reflection. -/
@[simp]
theorem lengthParityEquiv_apply_coe (i : B) (x : {w : W // Even (cs.length w)}) :
    (lengthParityEquiv cs i x : W) = cs.simple i * (x : W) := (rfl)

/-- The inverse of `lengthParityEquiv` is again left multiplication by the simple reflection. -/
@[simp]
theorem lengthParityEquiv_symm_apply_coe (i : B) (x : {w : W // Odd (cs.length w)}) :
    ((lengthParityEquiv cs i).symm x : W) = cs.simple i * (x : W) := (rfl)

/-- **The two parity classes of a Coxeter group of positive rank are equinumerous**: there are as
many elements of even length as of odd length. No finiteness is needed, since the two classes are
matched by an explicit bijection. -/
theorem natCard_length_even_eq_natCard_length_odd [Nonempty B] :
    Nat.card {w : W // Even (cs.length w)} = Nat.card {w : W // Odd (cs.length w)} :=
  Nat.card_congr (lengthParityEquiv cs (Classical.arbitrary B))

include cs in
/-- **A Coxeter group of positive rank has even order**: a simple reflection is an element of order
two, so two divides the order of the group. (For infinite `W` this reads `Even 0`, since
`Nat.card W = 0`; the content is the finite case.) -/
theorem even_natCard_of_nonempty_index [Nonempty B] : Even (Nat.card W) := by
  obtain ⟨i⟩ := ‹Nonempty B›
  have hne : cs.simple i ≠ 1 := fun h => by simpa [h] using cs.length_simple i
  obtain ⟨k, hk⟩ := orderOf_eq_prime (cs.simple_sq i) hne ▸ orderOf_dvd_natCard (cs.simple i)
  exact ⟨k, by omega⟩

end TauCeti
