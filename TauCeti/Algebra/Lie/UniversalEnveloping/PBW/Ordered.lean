/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm

/-!
# Ordered monomials span the PBW filtration

Let `e : ι → L` be a linearly ordered spanning family of a Lie algebra. This file proves that the
degree-`k` Poincaré--Birkhoff--Witt filtration of `UniversalEnvelopingAlgebra R L` is spanned by the
monomials

```text
ι(e(i₁)) ⋯ ι(e(iₙ)),    i₁ ≤ ⋯ ≤ iₙ,    n ≤ k.
```

There are two steps. First, `span_prod_map_eq_wordFiltration` expands arbitrary Lie-algebra words in
the spanning family. Second, sorting a word in that family changes it only by a term in the
preceding filtration step, by
`pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`. Induction on the filtration degree then
absorbs this error into shorter ordered monomials.

This is the spanning half of the ordered-monomial basis target in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. Linear independence, and hence the
full PBW basis, still requires the symmetric-algebra comparison.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.orderedPBWMonomials`: the ordered monomials of length at
  most a specified degree.
* `TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`: these monomials
  span exactly the corresponding PBW filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.span_iUnion_orderedPBWMonomials_eq_top`: all ordered monomials
  span the universal enveloping algebra.

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

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section OrderedWords

variable {ι : Type w} [LE ι] (e : ι → L)

/-- Ordered PBW monomials in a family indexed by an ordered type, of word length at most `k`. -/
def orderedPBWMonomials (k : ℕ) : Set U :=
  {a | ∃ word : List ι,
    word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a}

/-- Membership in `orderedPBWMonomials`, in terms of an ordered word of family indices. -/
@[simp]
theorem mem_orderedPBWMonomials_iff {k : ℕ} {a : U} :
    a ∈ orderedPBWMonomials R L e k ↔
      ∃ word : List ι,
        word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L e word = a :=
  Iff.rfl

/-- An ordered family word of length at most `k` gives an ordered PBW monomial of degree at most
`k`. -/
theorem pbwMonomial_mem_orderedPBWMonomials {k : ℕ} {word : List ι}
    (hsorted : word.Pairwise (· ≤ ·)) (hword : word.length ≤ k) :
    pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
  ⟨word, hsorted, hword, rfl⟩

/-- Increasing the degree bound enlarges the set of ordered PBW monomials. -/
theorem orderedPBWMonomials_mono : Monotone (orderedPBWMonomials R L e) := by
  intro i j hij a
  rintro ⟨word, hsorted, hlength, rfl⟩
  exact ⟨word, hsorted, hlength.trans hij, rfl⟩

/-- Every ordered PBW monomial of degree at most `k` lies in the `k`-th PBW filtration step. -/
theorem orderedPBWMonomials_subset_pbwFiltration (k : ℕ) :
    orderedPBWMonomials R L e k ⊆ pbwFiltration R L k := by
  rintro a ⟨word, -, hword, rfl⟩
  exact (pbwFiltration_mono R L hword) (pbwMonomial_mem_pbwFiltration R L e word)

/-- The only ordered PBW monomial of degree zero is the empty monomial `1`. -/
@[simp]
theorem orderedPBWMonomials_zero : orderedPBWMonomials R L e 0 = {1} := by
  ext a
  constructor
  · rintro ⟨word, -, hword, rfl⟩
    rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hword), pbwMonomial_nil]
    exact Set.mem_singleton 1
  · rintro rfl
    exact ⟨[], List.Pairwise.nil, le_rfl, pbwMonomial_nil R L e⟩

end OrderedWords

section Spanning

variable {ι : Type w} [LinearOrder ι] (e : ι → L)

/-- **Ordered PBW monomials span the PBW filtration.** For a linearly ordered spanning family `e`
in `L`, the monomials in nondecreasing family elements of length at most `k` span precisely
filtration degree `k` of `UniversalEnvelopingAlgebra R L`.

This is the spanning half of PBW. The reverse information needed for a basis is linear independence,
which comes from identifying the associated graded algebra with `SymmetricAlgebra R L`. -/
theorem span_orderedPBWMonomials_eq_pbwFiltration
    (he : Submodule.span R (Set.range e) = ⊤) (k : ℕ) :
    Submodule.span R (orderedPBWMonomials R L e k) = pbwFiltration R L k := by
  refine le_antisymm (Submodule.span_le.mpr
    (orderedPBWMonomials_subset_pbwFiltration R L e k)) ?_
  induction k with
  | zero =>
      rw [pbwFiltration_zero, orderedPBWMonomials_zero, Submodule.one_le]
      exact Submodule.subset_span (Set.mem_singleton 1)
  | succ k ih =>
      -- Expand arbitrary generator words in the spanning family, then sort the resulting words.
      have hfiltration : TauCeti.Algebra.wordFiltration
          (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (k + 1) =
          pbwFiltration R L (k + 1) := by
        rw [TauCeti.Algebra.wordFiltration_eq_pow, pbwFiltration_eq_pow]
      rw [← hfiltration, ← TauCeti.Algebra.span_prod_map_eq_wordFiltration
        (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap e he (k + 1),
        Submodule.span_le]
      rintro a ⟨word, hword, rfl⟩
      have hp :
          (word.map fun i ↦
            (_root_.UniversalEnvelopingAlgebra.ι R (L := L)).toLinearMap (e i)).prod =
            pbwMonomial R L e word := by
        rw [pbwMonomial_def]
        simp only [List.map_map, Function.comp_def, LieHom.coe_toLinearMap]
      rw [hp]
      let sorted := word.insertionSort (· ≤ ·)
      have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
      have hlength : sorted.length ≤ k + 1 := by
        simpa [sorted] using hword
      have hsorted_mem : pbwMonomial R L e sorted ∈
          Submodule.span R (orderedPBWMonomials R L e (k + 1)) :=
        Submodule.subset_span
          (pbwMonomial_mem_orderedPBWMonomials R L e hsorted hlength)
      cases word with
      | nil =>
          simpa [sorted] using hsorted_mem
      | cons head tail =>
          have htail : tail.length ≤ k := by simpa using hword
          have hdiff :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                pbwFiltration R L tail.length := by
            have h := pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
              R L (· ≤ ·) e (head :: tail)
            rw [List.length_cons, pbwFiltrationPrevious_succ] at h
            exact h
          have hdiff' :
              pbwMonomial R L e (head :: tail) - pbwMonomial R L e sorted ∈
                Submodule.span R (orderedPBWMonomials R L e (k + 1)) := by
            have hdiffk := pbwFiltration_mono R L htail hdiff
            exact Submodule.span_mono (orderedPBWMonomials_mono R L e (Nat.le_succ k))
              (ih hdiffk)
          rw [← sub_add_cancel (pbwMonomial R L e (head :: tail))
            (pbwMonomial R L e sorted)]
          exact Submodule.add_mem _ hdiff' hsorted_mem

/-- The ordered PBW monomials in a linearly ordered spanning family span the whole universal
enveloping algebra. -/
theorem span_iUnion_orderedPBWMonomials_eq_top
    (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R (⋃ k, orderedPBWMonomials R L e k) = ⊤ := by
  rw [Submodule.span_iUnion]
  simp_rw [span_orderedPBWMonomials_eq_pbwFiltration R L e he]
  exact iSup_pbwFiltration_eq_top R L

end Spanning

end TauCeti.UniversalEnvelopingAlgebra
