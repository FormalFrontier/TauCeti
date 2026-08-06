/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Chamber

public section

/-!
# The Weyl vector of a base

The **Weyl vector** `ρ` of a base of a root pairing is the half-sum of the positive roots. It is
the shift that turns the Weyl group action on weights into the dot action, and it appears in the
Weyl character, dimension and Kostant formulas as the correction `λ ↦ λ + ρ`.

Halving is not available over an arbitrary coefficient ring, so the sum of the positive roots is
introduced first, as `TauCeti.twoWeylVector`, and the Weyl vector itself only once `2` is
invertible. Every substantive statement is proved for the sum and then divided by two, so nothing
below depends on the coefficient ring beyond what the statement needs.

The one theorem the notion exists for is that `ρ` pairs to `1` with every simple coroot,
equivalently that the simple reflection `sᵢ` sends `ρ` to `ρ - αᵢ`. Its proof is the classical
one: `sᵢ` negates `αᵢ` and permutes the remaining positive roots, so the pairings of those
remaining roots with `αᵢ^∨` cancel in pairs and only `⟨αᵢ, αᵢ^∨⟩ = 2` survives.

## Main definitions

* `TauCeti.posRootsFinset` and `TauCeti.negRootsFinset`: the positive and the negative roots of a
  base as finsets, so that they can be summed over.
* `TauCeti.twoWeylVector`: the sum of the positive roots, that is `2ρ`.
* `TauCeti.weylVector`: the Weyl vector `ρ`, the half-sum of the positive roots, defined when `2`
  is invertible in the coefficient ring.

## Main results

* `TauCeti.coroot'_twoWeylVector` and `TauCeti.coroot'_weylVector`: `⟨2ρ, αᵢ^∨⟩ = 2` and
  `⟨ρ, αᵢ^∨⟩ = 1` for every simple root `αᵢ`.
* `TauCeti.reflection_twoWeylVector` and `TauCeti.reflection_weylVector`: `sᵢ(2ρ) = 2ρ - 2αᵢ` and
  `sᵢ(ρ) = ρ - αᵢ`.
* `TauCeti.sum_root_negRootsFinset`: the sum of the negative roots is `-2ρ`.
* `TauCeti.reflection_add_weylVector_sub`: the dot action of a simple reflection,
  `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`.
* `TauCeti.add_weylVector_mem_openDominantChamber` and
  `TauCeti.weylVector_mem_openDominantChamber`: over a linearly ordered coefficient ring the
  `ρ`-shift of a dominant weight is strictly dominant, and `ρ` itself is a regular weight.

## References

This file supplies the `weylVector` prerequisite of Layer 3 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`, which fixes the notation `ρ` for
the half-sum of the positive roots and states its dominance and integrality; the Weyl character
and dimension formulas of that roadmap's Layer 6 are stated in terms of it. It is built here at
the level of an abstract root pairing, where the positive-root combinatorics it needs already
lives.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.2 and §13.3.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable [CharZero R] (b : P.Base) [Finite ι]

/-- The positive roots of a base, as a finset. -/
noncomputable def posRootsFinset : Finset ι := (posRoots_finite P b).toFinset

/-- The negative roots of a base, as a finset. -/
noncomputable def negRootsFinset : Finset ι := (negRoots_finite P b).toFinset

@[simp]
lemma mem_posRootsFinset (i : ι) : i ∈ posRootsFinset P b ↔ i ∈ posRoots P b :=
  (posRoots_finite P b).mem_toFinset

@[simp]
lemma mem_negRootsFinset (i : ι) : i ∈ negRootsFinset P b ↔ i ∈ negRoots P b :=
  (negRoots_finite P b).mem_toFinset

/-- **Twice the Weyl vector**: the sum of the positive roots of a base.

The Weyl vector itself is `TauCeti.weylVector`, this element halved; it needs `2` to be invertible
in the coefficient ring, whereas the sum is always available and carries all the content. -/
@[expose]
noncomputable def twoWeylVector : M := ∑ i ∈ posRootsFinset P b, P.root i

/-- `2ρ` is the sum of the positive roots, by definition. -/
lemma twoWeylVector_eq_sum : twoWeylVector P b = ∑ i ∈ posRootsFinset P b, P.root i := rfl

section Reduced

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The pairings of the positive roots other than `αᵢ` with `αᵢ^∨` cancel.** The simple
reflection `sᵢ` permutes those roots and negates each of their pairings with `αᵢ^∨`, so the sum is
its own negative. -/
theorem sum_pairing_posRootsFinset_erase_eq_zero [DecidableEq ι] {i : ι} (hi : i ∈ b.support) :
    ∑ j ∈ (posRootsFinset P b).erase i, P.pairing j i = 0 := by
  set E := (posRootsFinset P b).erase i with hEdef
  have hstable : ∀ j : ι, j ∈ E ↔ P.reflectionPerm i j ∈ E := by
    intro j
    have h := reflectionPerm_mem_posRoots_diff_singleton_iff P b hi j
    simp only [Set.mem_sdiff, Set.mem_singleton_iff] at h
    simp only [hEdef, Finset.mem_erase, mem_posRootsFinset]
    tauto
  have key : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = ∑ j ∈ E, P.pairing j i :=
    Finset.sum_equiv (P.reflectionPerm i) hstable fun _ _ ↦ rfl
  have hneg : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = -∑ j ∈ E, P.pairing j i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [← P.pairing_reflectionPerm i j i, P.pairing_reflectionPerm_self_right]
  have hself : ∑ j ∈ E, P.pairing j i = -∑ j ∈ E, P.pairing j i := key.symm.trans hneg
  have htwo : (2 : R) * ∑ j ∈ E, P.pairing j i = 0 := by
    rw [two_mul]
    nth_rewrite 1 [hself]
    exact neg_add_cancel _
  have h2 : (2 : R) ≠ 0 := by exact_mod_cast (by norm_num : (2 : ℕ) ≠ 0)
  exact (mul_eq_zero.mp htwo).resolve_left h2

/-- **The sum of the positive roots pairs to `2` with every simple coroot.** All the positive roots
other than `αᵢ` cancel, leaving `⟨αᵢ, αᵢ^∨⟩ = 2`. -/
theorem coroot'_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.coroot' i (twoWeylVector P b) = 2 := by
  classical
  have hmem : i ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b i).mpr (support_subset_posRoots P b (Finset.mem_coe.mpr hi))
  rw [twoWeylVector_eq_sum, map_sum]
  simp only [RootPairing.root_coroot'_eq_pairing]
  rw [← Finset.add_sum_erase _ _ hmem, sum_pairing_posRootsFinset_erase_eq_zero P b hi, add_zero,
    RootPairing.pairing_same]

/-- **A simple reflection subtracts `2αᵢ` from the sum of the positive roots.** -/
theorem reflection_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.reflection i (twoWeylVector P b) = twoWeylVector P b - (2 : R) • P.root i := by
  rw [RootPairing.reflection_apply, coroot'_twoWeylVector P b hi]

end Reduced

/-- **The sum of the negative roots is `-2ρ`.** Root negation is a bijection from the negative
roots onto the positive ones. -/
theorem sum_root_negRootsFinset :
    ∑ i ∈ negRootsFinset P b, P.root i = -twoWeylVector P b := by
  have hinv : Function.Involutive fun j : ι ↦ P.reflectionPerm j j := by
    intro j
    let := P.indexNeg
    simp only [← RootPairing.indexNeg_neg, neg_neg]
  rw [twoWeylVector_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_equiv hinv.toPerm (fun j ↦ ?_) fun j _ ↦ ?_
  · rw [mem_negRootsFinset, mem_posRootsFinset, Function.Involutive.coe_toPerm]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b j).symm
  · simp

section Weyl

variable [Invertible (2 : R)]

/-- **The Weyl vector `ρ`**: the half-sum of the positive roots of a base. -/
noncomputable def weylVector : M := ⅟(2 : R) • twoWeylVector P b

/-- Doubling the Weyl vector recovers the sum of the positive roots. -/
@[simp]
lemma two_smul_weylVector : (2 : R) • weylVector P b = twoWeylVector P b := by
  rw [weylVector, smul_smul, mul_invOf_self, one_smul]

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The Weyl vector pairs to `1` with every simple coroot**, `⟨ρ, αᵢ^∨⟩ = 1`. This is the
defining property of `ρ`: it is the weight taking the value `1` on every simple coroot. -/
theorem coroot'_weylVector {i : ι} (hi : i ∈ b.support) : P.coroot' i (weylVector P b) = 1 := by
  rw [weylVector, map_smul, coroot'_twoWeylVector P b hi, smul_eq_mul, invOf_mul_self]

/-- **A simple reflection subtracts its simple root from the Weyl vector**, `sᵢ(ρ) = ρ - αᵢ`. -/
theorem reflection_weylVector {i : ι} (hi : i ∈ b.support) :
    P.reflection i (weylVector P b) = weylVector P b - P.root i := by
  rw [RootPairing.reflection_apply, coroot'_weylVector P b hi, one_smul]

/-- **The `ρ`-shift raises every simple coroot pairing by one.** This is the whole role of `ρ` in
the highest-weight theory: it converts the dominance condition `0 ≤ ⟨λ, αᵢ^∨⟩` into the strict one
`0 < ⟨λ + ρ, αᵢ^∨⟩`. -/
theorem coroot'_add_weylVector {i : ι} (hi : i ∈ b.support) (x : M) :
    P.coroot' i (x + weylVector P b) = P.coroot' i x + 1 := by
  rw [map_add, coroot'_weylVector P b hi]

/-- **The dot action of a simple reflection.** Conjugating the reflection `sᵢ` by the translation
by `ρ` gives `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`, the shifted Weyl group action under which the
Verma and irreducible highest-weight modules of a given central character are permuted. -/
theorem reflection_add_weylVector_sub {i : ι} (hi : i ∈ b.support) (x : M) :
    P.reflection i (x + weylVector P b) - weylVector P b
      = x - (P.coroot' i x + 1) • P.root i := by
  rw [RootPairing.reflection_apply, coroot'_add_weylVector P b hi]
  abel

end Weyl

section Ordered

variable [LinearOrder R] [IsStrictOrderedRing R] [Invertible (2 : R)]
  [P.IsCrystallographic] [P.IsReduced]

/-- **Shifting a dominant weight by `ρ` makes it strictly dominant.** -/
theorem add_weylVector_mem_openDominantChamber {x : M} (hx : x ∈ dominantChamber P b) :
    x + weylVector P b ∈ openDominantChamber P b := by
  rw [mem_openDominantChamber]
  intro i hi
  rw [coroot'_add_weylVector P b hi]
  exact lt_of_le_of_lt ((mem_dominantChamber P b x).mp hx i hi) (lt_add_one _)

/-- **The Weyl vector is strictly dominant**, hence a regular weight: it lies on no wall of the
dominant chamber. -/
theorem weylVector_mem_openDominantChamber :
    weylVector P b ∈ openDominantChamber P b := by
  simpa using add_weylVector_mem_openDominantChamber P b (zero_mem_dominantChamber P b)

end Ordered

end TauCeti
