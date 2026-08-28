/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length

/-!
# The parity and the functoriality of the length function of a Coxeter system

Let `cs : CoxeterSystem M W` be a Coxeter system. Left multiplication by a fixed simple reflection
changes the length of an element by exactly one (`CoxeterSystem.length_mul_mod_two`), so it flips
the parity of the length. This file packages that pairing as an explicit equivalence
`TauCeti.lengthParityEquiv` between the elements of even length and the elements of odd length, and
records its two immediate consequences: the two parity classes are equinumerous, and a Coxeter
group with at least one simple reflection has even order.

Finally, the length function is transported along the two canonical constructions on Coxeter
systems, `CoxeterSystem.reindex` and `CoxeterSystem.map`: relabelling the simple reflections or
pushing the system through a group isomorphism leaves lengths unchanged.

## Main definitions

* `TauCeti.lengthParityEquiv`: left multiplication by a simple reflection, as an equivalence
  between the even-length and the odd-length elements.

## Main results

* `TauCeti.natCard_length_even_eq_natCard_length_odd`: as many elements have even length as odd
  length, provided there is at least one simple reflection.
* `TauCeti.even_natCard_of_nonempty_index`: hence a Coxeter group of positive rank has even order.
* `TauCeti.length_reindex` and `TauCeti.length_map`: the length function is unchanged by
  `CoxeterSystem.reindex` and by `CoxeterSystem.map`.

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
    {w : W // Even (cs.length w)} ≃ {w : W // Odd (cs.length w)} :=
  (Equiv.mulLeft (cs.simple i)).subtypeEquiv fun w => (odd_length_simple_mul_iff cs i w).symm

/-- `lengthParityEquiv` is left multiplication by the simple reflection. -/
@[simp]
theorem lengthParityEquiv_apply_coe (i : B) (x : {w : W // Even (cs.length w)}) :
    (lengthParityEquiv cs i x : W) = cs.simple i * (x : W) := (rfl)

/-- The inverse of `lengthParityEquiv` is again left multiplication by the simple reflection: the
simple reflection is its own inverse. -/
@[simp]
theorem lengthParityEquiv_symm_apply_coe (i : B) (x : {w : W // Odd (cs.length w)}) :
    ((lengthParityEquiv cs i).symm x : W) = cs.simple i * (x : W) := by
  have h := congrArg Subtype.val ((lengthParityEquiv cs i).apply_symm_apply x)
  rw [lengthParityEquiv_apply_coe] at h
  rw [← h, ← mul_assoc, cs.simple_mul_simple_self, one_mul]

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

/-! ### Transport along a reindexing or a group isomorphism -/

section Transport

variable {B' H : Type*} [Group H]

/-- A word in the reindexed simple reflections is the corresponding word in the original ones. -/
private theorem wordProd_reindex (e : B ≃ B') (ω : List B') :
    (cs.reindex e).wordProd ω = cs.wordProd (ω.map e.symm) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, ih, List.map_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.reindex_simple]

/-- Pushing a word through the isomorphism computes the corresponding word for the transported
Coxeter system. -/
private theorem wordProd_map (e : W ≃* H) (ω : List B) :
    (cs.map e).wordProd ω = e (cs.wordProd ω) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, ih, CoxeterSystem.wordProd_cons, map_mul,
      CoxeterSystem.map_simple]

/-- **The length function is unchanged by reindexing the simple reflections**: a bijection of the
indexing set carries words to words of the same length. -/
@[simp]
theorem length_reindex (e : B ≃ B') (w : W) : (cs.reindex e).length w = cs.length w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    calc (cs.reindex e).length (cs.wordProd ω)
        = (cs.reindex e).length ((cs.reindex e).wordProd (ω.map e)) := by
          rw [wordProd_reindex]; simp
      _ ≤ (ω.map e).length := CoxeterSystem.length_wordProd_le _ _
      _ = cs.length (cs.wordProd ω) := by rw [List.length_map, hω.eq]
  · obtain ⟨ω, hω, rfl⟩ := (cs.reindex e).exists_isReduced w
    calc cs.length ((cs.reindex e).wordProd ω)
        = cs.length (cs.wordProd (ω.map e.symm)) := by rw [wordProd_reindex]
      _ ≤ (ω.map e.symm).length := CoxeterSystem.length_wordProd_le _ _
      _ = (cs.reindex e).length ((cs.reindex e).wordProd ω) := by
          rw [List.length_map, hω.eq]

/-- **The length function is transported by a group isomorphism**: an isomorphism `e : W ≃* H`
matches the simple reflections of `cs` with those of `cs.map e`, hence their lengths. -/
@[simp]
theorem length_map (e : W ≃* H) (w : W) : (cs.map e).length (e w) = cs.length w := by
  refine le_antisymm ?_ ?_
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    calc (cs.map e).length (e (cs.wordProd ω))
        = (cs.map e).length ((cs.map e).wordProd ω) := by rw [wordProd_map]
      _ ≤ ω.length := CoxeterSystem.length_wordProd_le _ _
      _ = cs.length (cs.wordProd ω) := hω.eq.symm
  · obtain ⟨ω, hω, hw⟩ := (cs.map e).exists_isReduced (e w)
    have hw' : w = cs.wordProd ω := e.injective (by rw [hw, wordProd_map])
    calc cs.length w = cs.length (cs.wordProd ω) := by rw [hw']
      _ ≤ ω.length := CoxeterSystem.length_wordProd_le _ _
      _ = (cs.map e).length (e w) := by rw [hw, hω.eq]

end Transport

end TauCeti
