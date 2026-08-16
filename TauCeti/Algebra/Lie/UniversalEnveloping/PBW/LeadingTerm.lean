/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.List.Sort
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Basic

/-!
# Permuting PBW words modulo lower filtration

This file proves the first consequence of the defining relation of a universal enveloping algebra
for its associated graded. If two words in the canonical generators differ only by a permutation,
then their difference has filtration degree strictly below their common word length. In particular,
the leading term of a word is unchanged when the word is sorted.

An adjacent exchange is the mathematical heart of the proof:

```text
ι(x) * ι(y) - ι(y) * ι(x) = ι([x,y]).
```

The left side has word length two while the right side has word length one. Multiplying by the
unchanged suffix preserves this one-degree drop. Induction on `List.Perm` then gives the result for
an arbitrary permutation.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial`: the product of a word in a chosen family of
  Lie-algebra elements.
* `TauCeti.UniversalEnvelopingAlgebra.prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm`:
  permuted words in canonical generators differ by a lower-filtration term.
* `pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm`:
  the same statement for words in an indexed family.
* `TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`:
  every word has the same leading term as its ordered version.

This is the first part of the associated-graded-map target in Layer 3, "PBW, a substantial
sub-project", of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. The next stage
uses these permutation-invariant leading terms to define the map from `SymmetricAlgebra R L` to the
associated graded of `U(L)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

/-- Exchanging the two leading generators of a word lowers the PBW filtration degree of the
difference by one. -/
private theorem prod_map_ι_sub_swap_mem_pbwFiltrationPrevious (x y : L) (l : List L) :
    ((x :: y :: l).map ⇑ι).prod - ((y :: x :: l).map ⇑ι).prod ∈
      pbwFiltrationPrevious R L (x :: y :: l).length := by
  simp only [List.length_cons, pbwFiltrationPrevious_succ, List.map_cons, List.prod_cons]
  rw [← mul_assoc, ← mul_assoc, ← sub_mul,
    ← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]
  simpa only [Nat.add_comm] using
    mul_mem_pbwFiltration (R := R) (L := L) (ι_mem_pbwFiltration_one R L ⁅x, y⁆)
      (prod_map_ι_mem_pbwFiltration R L le_rfl)

/-- **Permuting a word does not change its leading PBW term.** The products of two permuted lists
of canonical generators differ by an element of degree strictly below their common length. -/
theorem prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm {l₁ l₂ : List L}
    (h : l₁.Perm l₂) :
    (l₁.map ⇑ι).prod - (l₂.map ⇑ι).prod ∈ pbwFiltrationPrevious R L l₁.length := by
  induction h with
  | nil => simp
  | cons x h ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [← mul_sub]
      simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
        mul_mem_pbwFiltrationPrevious_right (R := R) (L := L)
          (ι_mem_pbwFiltration_one R L x) ih
  | swap x y l => exact prod_map_ι_sub_swap_mem_pbwFiltrationPrevious R L y x l
  | trans h₁ h₂ ih₁ ih₂ =>
      rw [← h₁.length_eq] at ih₂
      simpa only [sub_add_sub_cancel] using
        (pbwFiltrationPrevious R L _).add_mem ih₁ ih₂

variable {ιIndex : Type w}

/-- The PBW monomial attached to a word of indices in a family `e : ιIndex → L`. No ordering or
linear-independence hypothesis on the family is needed. -/
def pbwMonomial (e : ιIndex → L) (word : List ιIndex) :
    _root_.UniversalEnvelopingAlgebra R L :=
  ((word.map e).map ⇑ι).prod

@[simp]
theorem pbwMonomial_nil (e : ιIndex → L) : pbwMonomial R L e [] = 1 := by
  simp [pbwMonomial]

@[simp]
theorem pbwMonomial_cons (e : ιIndex → L) (i : ιIndex) (word : List ιIndex) :
    pbwMonomial R L e (i :: word) = ι (e i) * pbwMonomial R L e word := by
  simp [pbwMonomial]

/-- A PBW monomial is the product of the corresponding canonical Lie generators. -/
theorem pbwMonomial_def (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word = ((word.map e).map ⇑ι).prod := by
  induction word with
  | nil => exact pbwMonomial_nil R L e
  | cons i word ih => simp only [pbwMonomial_cons, List.map_cons, List.prod_cons, ih]

@[simp]
theorem pbwMonomial_append (e : ιIndex → L) (word₁ word₂ : List ιIndex) :
    pbwMonomial R L e (word₁ ++ word₂) =
      pbwMonomial R L e word₁ * pbwMonomial R L e word₂ := by
  simp [pbwMonomial]

/-- A PBW monomial belongs to the filtration step given by the length of its word. -/
theorem pbwMonomial_mem_pbwFiltration (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word ∈ pbwFiltration R L word.length := by
  rw [pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_mem_pbwFiltration R L (l := word.map e) (by simp)

/-- Permuted words in any indexed family give PBW monomials with the same leading term. -/
theorem pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm
    (e : ιIndex → L) {word₁ word₂ : List ιIndex} (h : word₁.Perm word₂) :
    pbwMonomial R L e word₁ - pbwMonomial R L e word₂ ∈
      pbwFiltrationPrevious R L word₁.length := by
  rw [pbwMonomial_def, pbwMonomial_def]
  simpa only [List.length_map] using
    prod_map_ι_sub_prod_map_ι_mem_pbwFiltrationPrevious_of_perm R L (h.map e)

/-- Sorting the indices of a PBW monomial by a decidable relation preserves its leading term. This
is the form used to span the associated graded by ordered monomials. -/
theorem pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
    (r : ιIndex → ιIndex → Prop) [DecidableRel r] (e : ιIndex → L) (word : List ιIndex) :
    pbwMonomial R L e word - pbwMonomial R L e (word.insertionSort r) ∈
      pbwFiltrationPrevious R L word.length :=
  pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm R L e
    (List.perm_insertionSort r word).symm

end TauCeti.UniversalEnvelopingAlgebra
