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

Which roots are positive is defined only over a coefficient ring of characteristic zero, and
halving asks for `2` to be invertible on top of that. So the sum of the positive roots is
introduced first, as `TauCeti.twoWeylVector`, over a characteristic-zero coefficient ring, and the
Weyl vector itself only once `2` is invertible as well. The simple-coroot pairing and the simple
reflection identity are proved for the sum first and then divided by two; the statements that
speak of `ρ` alone — the dot action and the dominance results — are proved only in the halved
form. So nothing below assumes more of the coefficient ring than its own statement needs.

The one theorem the notion exists for is that `ρ` pairs to `1` with every simple coroot,
equivalently that the simple reflection `sᵢ` sends `ρ` to `ρ - αᵢ`. Its proof is the classical
one: `sᵢ` negates `αᵢ` and permutes the remaining positive roots, so the pairings of those
remaining roots with `αᵢ^∨` cancel in pairs and only `⟨αᵢ, αᵢ^∨⟩ = 2` survives.

## Main definitions

* `TauCeti.twoWeylVector`: the sum of the positive roots, that is `2ρ`.
* `TauCeti.weylVector`: the Weyl vector `ρ`, the half-sum of the positive roots, defined when `2`
  is invertible in the coefficient ring.

## Main results

* `TauCeti.coroot'_twoWeylVector` and `TauCeti.coroot'_weylVector`: `⟨2ρ, αᵢ^∨⟩ = 2` and
  `⟨ρ, αᵢ^∨⟩ = 1` for every simple root `αᵢ`.
* `TauCeti.reflection_twoWeylVector` and `TauCeti.reflection_weylVector`: `sᵢ(2ρ) = 2ρ - 2αᵢ` and
  `sᵢ(ρ) = ρ - αᵢ`.
* `TauCeti.sum_root_negRootsFinset`: the sum of the negative roots is `-2ρ`.
* `TauCeti.reflection_add_weylVector_sub_weylVector`: the dot action of a simple reflection,
  `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`.
* `TauCeti.add_weylVector_mem_openDominantChamber` and
  `TauCeti.weylVector_mem_openDominantChamber`: over a linearly ordered coefficient ring the
  `ρ`-shift of a dominant weight is strictly dominant, and `ρ` itself is a regular weight.
* `TauCeti.openDominantChamber_nonempty`: consequently the open dominant chamber has a point,
  which over a general coefficient ring is a genuine hypothesis rather than a formality.

## References

This file supplies the root-pairing-level prerequisite of the `ρ` item of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: Layer 1 there "only fixes the
notation `ρ` for the half-sum of positive roots and states dominance and integrality of weights",
and the Lie-algebra signature `weylVector (base : (LieAlgebra.IsKilling.rootSystem H).Base) :
Module.Dual K H` is stated in the Layer 5 section of that roadmap's `Suggested.lean`, where the
Casimir eigenvalue is the first consumer; the Weyl character and dimension formulas of Layer 6 are
stated in terms of the same `ρ`. Nothing here is a Lie-algebra-level declaration, and nothing here
uses the highest-weight machinery of Layers 2-4: `ρ` is built for an abstract root pairing, where
the positive-root combinatorics it needs already lives, so that the Lie-algebra target is a
specialization rather than a rebuild.

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.2 and §13.3.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

variable [CharZero R] (b : P.Base) [Finite ι]

/-- **Twice the Weyl vector**: the sum of the positive roots of a base.

The Weyl vector itself is `TauCeti.weylVector`, this element halved; it needs `2` to be invertible
in the coefficient ring, whereas the sum needs only the characteristic-zero hypothesis under which
the positive roots are defined at all, and carries all the content. -/
noncomputable def twoWeylVector : M := ∑ i ∈ posRootsFinset P b, P.root i

/-- `2ρ` is the sum of the positive roots, by definition. -/
lemma twoWeylVector_def : twoWeylVector P b = ∑ i ∈ posRootsFinset P b, P.root i := by
  rw [twoWeylVector]

section Reduced

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The pairings of the positive roots other than `αᵢ` with `αᵢ^∨` cancel.** The simple
reflection `sᵢ` permutes those roots and negates each of their pairings with `αᵢ^∨`, so the sum is
its own negative. -/
private theorem sum_pairing_posRootsFinset_erase_eq_zero [DecidableEq ι] {i : ι}
    (hi : i ∈ b.support) :
    ∑ j ∈ (posRootsFinset P b).erase i, P.pairing j i = 0 := by
  set E := (posRootsFinset P b).erase i
  have key : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = ∑ j ∈ E, P.pairing j i :=
    sum_posRootsFinset_erase_comp_reflectionPerm P b hi fun j ↦ P.pairing j i
  have hneg : ∑ j ∈ E, P.pairing (P.reflectionPerm i j) i = -∑ j ∈ E, P.pairing j i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by
      rw [← P.pairing_reflectionPerm i j i, P.pairing_reflectionPerm_self_right]
  have hself : ∑ j ∈ E, P.pairing j i = -∑ j ∈ E, P.pairing j i := key.symm.trans hneg
  exact CharZero.eq_neg_self_iff.mp hself

/-- **The sum of the positive roots pairs to `2` with every simple coroot.** All the positive roots
other than `αᵢ` cancel, leaving `⟨αᵢ, αᵢ^∨⟩ = 2`.

Not `@[simp]`: `RootPairing.coroot'` is an `abbrev`, so `simp` unfolds this left-hand side through
`LinearMap.flip_apply` and the `simpNF` linter rejects the tag. The `simp`-usable form of this
identity is `TauCeti.reflection_twoWeylVector` below. -/
theorem coroot'_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.coroot' i (twoWeylVector P b) = 2 := by
  classical
  have hmem : i ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b i).mpr (support_subset_posRoots P b (Finset.mem_coe.mpr hi))
  rw [twoWeylVector_def, map_sum]
  simp only [RootPairing.root_coroot'_eq_pairing]
  rw [← Finset.add_sum_erase _ _ hmem, sum_pairing_posRootsFinset_erase_eq_zero P b hi, add_zero,
    RootPairing.pairing_same]

/-- **A simple reflection subtracts `2αᵢ` from the sum of the positive roots.** -/
@[simp]
theorem reflection_twoWeylVector {i : ι} (hi : i ∈ b.support) :
    P.reflection i (twoWeylVector P b) = twoWeylVector P b - (2 : R) • P.root i := by
  rw [RootPairing.reflection_apply, coroot'_twoWeylVector P b hi]

end Reduced

/-- **The sum of the negative roots is `-2ρ`.** Root negation is a bijection from the negative
roots onto the positive ones. -/
theorem sum_root_negRootsFinset :
    ∑ i ∈ negRootsFinset P b, P.root i = -twoWeylVector P b := by
  have hinv := reflectionPerm_self_involutive P
  rw [twoWeylVector_def, ← Finset.sum_neg_distrib]
  refine Finset.sum_equiv hinv.toPerm (fun j ↦ ?_) fun j _ ↦ ?_
  · rw [mem_negRootsFinset, mem_posRootsFinset, Function.Involutive.coe_toPerm]
    exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b j).symm
  · simp

section Weyl

variable [Invertible (2 : R)]

/-- **The Weyl vector `ρ`**: the half-sum of the positive roots of a base. -/
noncomputable def weylVector : M := ⅟(2 : R) • twoWeylVector P b

/-- `ρ` is half the sum of the positive roots, by definition. -/
lemma weylVector_def : weylVector P b = ⅟(2 : R) • twoWeylVector P b := by
  rw [weylVector]

/-- Doubling the Weyl vector recovers the sum of the positive roots. -/
@[simp]
lemma two_smul_weylVector : (2 : R) • weylVector P b = twoWeylVector P b := by
  rw [weylVector, smul_smul, mul_invOf_self, one_smul]

variable [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The Weyl vector pairs to `1` with every simple coroot**, `⟨ρ, αᵢ^∨⟩ = 1`. This is the
characteristic pairing identity that `ρ` is introduced for; it records the values of `ρ` on the
simple coroots, and over an abstract root pairing those values need not pin `ρ` down, since
nothing here says the simple coroots separate the points of `M`.

Not `@[simp]`, for the same reason as `TauCeti.coroot'_twoWeylVector`. -/
theorem coroot'_weylVector {i : ι} (hi : i ∈ b.support) : P.coroot' i (weylVector P b) = 1 := by
  rw [weylVector, map_smul, coroot'_twoWeylVector P b hi, smul_eq_mul, invOf_mul_self]

/-- **A simple reflection subtracts its simple root from the Weyl vector**, `sᵢ(ρ) = ρ - αᵢ`. -/
@[simp]
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
by `ρ` gives `sᵢ ⬝ λ = λ - (⟨λ, αᵢ^∨⟩ + 1) αᵢ`. Only this formula on weights is proved here; it is
the shifted Weyl group action that the highest-weight theory uses in place of the linear one, but
the statement that it permutes the highest weights of a given central character belongs to that
setting and needs its hypotheses. -/
theorem reflection_add_weylVector_sub_weylVector {i : ι} (hi : i ∈ b.support) (x : M) :
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

/-- **The open dominant chamber is nonempty** once `2` is invertible: the Weyl vector `ρ` pairs to
`1` with every simple coroot, so it is strictly dominant. -/
theorem openDominantChamber_nonempty : (openDominantChamber P b).Nonempty :=
  ⟨weylVector P b, weylVector_mem_openDominantChamber P b⟩

end Ordered

end TauCeti
