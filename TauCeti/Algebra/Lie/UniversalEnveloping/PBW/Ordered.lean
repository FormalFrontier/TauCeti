/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm

/-!
# Ordered monomials span the PBW filtration

Let `b : Basis ι R L` be a linearly ordered basis of a Lie algebra. This file proves that the
degree-`k` Poincaré--Birkhoff--Witt filtration of `UniversalEnvelopingAlgebra R L` is spanned by the
monomials

```text
ι(b(i₁)) ⋯ ι(b(iₙ)),    i₁ ≤ ⋯ ≤ iₙ,    n ≤ k.
```

There are two steps. First, expanding each Lie-algebra element in the basis shows that arbitrary
words in the canonical generators are spanned by basis words of the same length. Second, sorting a
basis word changes it only by a term in the preceding filtration step, by
`pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious`. Induction on the filtration degree then
absorbs this error into shorter ordered monomials.

This is the spanning half of the ordered-monomial basis target in Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`. Linear independence, and hence the
full PBW basis, still requires the symmetric-algebra comparison.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.orderedPBWMonomials`: the ordered basis monomials of length at
  most a specified degree.
* `TauCeti.UniversalEnvelopingAlgebra.span_orderedPBWMonomials_eq_pbwFiltration`: these monomials
  span exactly the corresponding PBW filtration step.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

section BasisWords

variable {ι : Type w} (b : Module.Basis ι R L)

/-- The PBW monomials in basis vectors whose words have length at most `k`, without an ordering
condition. This auxiliary set mediates between arbitrary words in `L` and ordered basis words. -/
private def basisPBWMonomials (k : ℕ) : Set U :=
  {a | ∃ word : List ι, word.length ≤ k ∧ pbwMonomial R L b word = a}

private theorem pbwMonomial_mem_span_basisPBWMonomials (word : List ι) :
    pbwMonomial R L b word ∈
      Submodule.span R (basisPBWMonomials R L b word.length) := by
  apply Submodule.subset_span
  exact ⟨word, le_rfl, rfl⟩

/-- A product of arbitrary canonical generators is a linear combination of basis words of the
same length. -/
private theorem prod_map_ι_mem_span_basisPBWMonomials (word : List L) :
    (word.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
      Submodule.span R (basisPBWMonomials R L b word.length) := by
  induction word with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.length_nil]
      exact Submodule.subset_span ⟨[], le_rfl, pbwMonomial_nil R L b⟩
  | cons x word ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons, ← b.linearCombination_repr x,
        Finsupp.linearCombination_apply, Finsupp.sum]
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
      apply Submodule.sum_mem
      intro i hi
      apply Submodule.smul_mem
      refine Submodule.span_induction (p := fun y _ ↦
        _root_.UniversalEnvelopingAlgebra.ι R (b i) * y ∈
          Submodule.span R (basisPBWMonomials R L b (word.length + 1))) ?_ ?_ ?_ ?_ ih
      · intro y hy
        obtain ⟨tail, htail, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨i :: tail, ?_, ?_⟩
        · simpa using Nat.succ_le_succ htail
        · simp only [pbwMonomial_cons]
      · simp
      · intro y z _ _ hy hz
        simpa only [mul_add] using Submodule.add_mem _ hy hz
      · intro r y _ hy
        simpa only [mul_smul_comm] using Submodule.smul_mem _ r hy

/-- Basis words of length at most `k` span the `k`-th PBW filtration step. This is the basis
expansion part of ordered PBW spanning; no order on the basis is needed. -/
private theorem span_basisPBWMonomials_eq_pbwFiltration (k : ℕ) :
    Submodule.span R (basisPBWMonomials R L b k) = pbwFiltration R L k := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro a ⟨word, hword, rfl⟩
    exact (pbwFiltration_mono R L hword) (pbwMonomial_mem_pbwFiltration R L b word)
  · rw [pbwFiltration_le_iff]
    intro word hword
    apply Submodule.span_mono (s := basisPBWMonomials R L b word.length) (t :=
      basisPBWMonomials R L b k)
    · rintro a ⟨basisWord, hbasisWord, ha⟩
      exact ⟨basisWord, hbasisWord.trans hword, ha⟩
    · exact prod_map_ι_mem_span_basisPBWMonomials R L b word

end BasisWords

section OrderedWords

variable {ι : Type w} [LinearOrder ι] (b : Module.Basis ι R L)

/-- Ordered PBW monomials in a chosen linearly ordered basis, of word length at most `k`. -/
def orderedPBWMonomials (k : ℕ) : Set U :=
  {a | ∃ word : List ι,
    word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L b word = a}

/-- Membership in `orderedPBWMonomials`, in terms of an ordered word of basis indices. -/
@[simp]
theorem mem_orderedPBWMonomials_iff {k : ℕ} {a : U} :
    a ∈ orderedPBWMonomials R L b k ↔
      ∃ word : List ι,
        word.Pairwise (· ≤ ·) ∧ word.length ≤ k ∧ pbwMonomial R L b word = a :=
  Iff.rfl

/-- An ordered basis word of length at most `k` gives an ordered PBW monomial of degree at most
`k`. -/
theorem pbwMonomial_mem_orderedPBWMonomials {k : ℕ} {word : List ι}
    (hsorted : word.Pairwise (· ≤ ·)) (hword : word.length ≤ k) :
    pbwMonomial R L b word ∈ orderedPBWMonomials R L b k :=
  ⟨word, hsorted, hword, rfl⟩

/-- Increasing the degree bound enlarges the set of ordered PBW monomials. -/
theorem orderedPBWMonomials_mono : Monotone (orderedPBWMonomials R L b) := by
  intro i j hij a
  rintro ⟨word, hsorted, hlength, rfl⟩
  exact ⟨word, hsorted, hlength.trans hij, rfl⟩

/-- Every ordered PBW monomial of degree at most `k` lies in the `k`-th PBW filtration step. -/
theorem orderedPBWMonomials_subset_pbwFiltration (k : ℕ) :
    orderedPBWMonomials R L b k ⊆ pbwFiltration R L k := by
  rintro a ⟨word, -, hword, rfl⟩
  exact (pbwFiltration_mono R L hword) (pbwMonomial_mem_pbwFiltration R L b word)

/-- **Ordered PBW monomials span the PBW filtration.** For a linearly ordered basis `b` of `L`,
the monomials in nondecreasing basis vectors of length at most `k` span precisely filtration degree
`k` of `UniversalEnvelopingAlgebra R L`.

This is the spanning half of PBW. The reverse information needed for a basis is linear independence,
which comes from identifying the associated graded algebra with `SymmetricAlgebra R L`. -/
theorem span_orderedPBWMonomials_eq_pbwFiltration (k : ℕ) :
    Submodule.span R (orderedPBWMonomials R L b k) = pbwFiltration R L k := by
  induction k with
  | zero =>
      apply le_antisymm
      · exact Submodule.span_le.mpr (orderedPBWMonomials_subset_pbwFiltration R L b 0)
      -- In degree zero, both spanning sets consist only of the empty monomial.
      · rw [← span_basisPBWMonomials_eq_pbwFiltration R L b 0, Submodule.span_le]
        rintro a ⟨word, hword, rfl⟩
        have : word = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hword)
        subst word
        exact Submodule.subset_span ⟨[], by simp, by simp, rfl⟩
  | succ k ih =>
      apply le_antisymm
      · exact Submodule.span_le.mpr
          (orderedPBWMonomials_subset_pbwFiltration R L b (k + 1))
      -- Expand arbitrary generator words in the basis, then sort each resulting basis word.
      · rw [← span_basisPBWMonomials_eq_pbwFiltration R L b (k + 1), Submodule.span_le]
        rintro a ⟨word, hword, rfl⟩
        let sorted := word.insertionSort (· ≤ ·)
        have hsorted : sorted.Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
        have hlength : sorted.length ≤ k + 1 := by
          simpa [sorted] using hword
        have hsorted_mem : pbwMonomial R L b sorted ∈
            Submodule.span R (orderedPBWMonomials R L b (k + 1)) :=
          Submodule.subset_span
            (pbwMonomial_mem_orderedPBWMonomials R L b hsorted hlength)
        cases word with
        | nil =>
            have hsorted_eq : sorted = [] := by simp [sorted]
            rw [hsorted_eq, pbwMonomial_nil] at hsorted_mem
            rw [pbwMonomial_nil]
            exact hsorted_mem
        | cons head tail =>
            have htail : tail.length ≤ k := by simpa using hword
            have hdiff :
                pbwMonomial R L b (head :: tail) - pbwMonomial R L b sorted ∈
                  pbwFiltration R L tail.length := by
              simpa [sorted] using
                pbwMonomial_sub_insertionSort_mem_pbwFiltrationPrevious
                  R L (· ≤ ·) b (head :: tail)
            have hdiff' :
                pbwMonomial R L b (head :: tail) - pbwMonomial R L b sorted ∈
                  Submodule.span R (orderedPBWMonomials R L b (k + 1)) := by
              have hdiffk := pbwFiltration_mono R L htail hdiff
              rw [← ih] at hdiffk
              exact Submodule.span_mono (orderedPBWMonomials_mono R L b (Nat.le_succ k))
                hdiffk
            rw [← sub_add_cancel (pbwMonomial R L b (head :: tail))
              (pbwMonomial R L b sorted)]
            exact Submodule.add_mem _ hdiff' hsorted_mem

end OrderedWords

end TauCeti.UniversalEnvelopingAlgebra
