/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import TauCeti.GroupTheory.Coxeter.Basic
public import TauCeti.GroupTheory.Coxeter.Length

/-!
# The Poincaré polynomial of a finite Coxeter system

For a Coxeter system `cs : CoxeterSystem M W` with `W` finite, the **length generating function**
`∑_{w ∈ W} q^{ℓ(w)}` is a genuine polynomial with integer coefficients, the **Poincaré polynomial**
of `cs`. This file introduces it and proves the elementary facts that make it a generating
function: its coefficient at `k` counts the elements of length `k`, its value at `1` is the order
of `W`, its constant term is `1`, and its degree is the largest length occurring in `W`.

The theorem with content beyond bookkeeping is the value at `-1`. Left multiplication by a fixed
simple reflection is a sign-reversing involution of `W`
(`TauCeti.length_simple_mul_mod_two`), so the alternating sum `∑_{w ∈ W} (-1)^{ℓ(w)}` vanishes as
soon as there is at least one simple reflection. The parity bookkeeping itself, together with the
equivalence between the two parity classes, lives in `TauCeti/GroupTheory/Coxeter/Length.lean`.

At the other extreme, a Coxeter system indexed by an empty type has a trivial group -- every
element is the product of a word in the generators, and there are no generators -- so its Poincaré
polynomial is `1`. That degenerate case is recorded as well, since it is what pins the
normalisation of the constant term.

## Main definitions

* `TauCeti.poincarePolynomial`: the Poincaré polynomial `∑_{w ∈ W} q^{ℓ(w)} ∈ ℤ[q]` of a Coxeter
  system on a finite group.

## Main results

* `TauCeti.coeff_poincarePolynomial`: the coefficient of `q^k` counts the elements of length `k`.
* `TauCeti.eval_one_poincarePolynomial`: the value at `1` is `|W|`.
* `TauCeti.eval_neg_one_poincarePolynomial`: the value at `-1` is `0` when the simple reflections
  are indexed by a nonempty type.
* `TauCeti.natDegree_poincarePolynomial` and `TauCeti.leadingCoeff_poincarePolynomial`: the degree
  is the maximal length, and the leading coefficient counts the elements attaining it.
* `TauCeti.poincarePolynomial_reindex` and `TauCeti.poincarePolynomial_map`: the polynomial is
  invariant under the two canonical transports of a Coxeter system.
* `TauCeti.poincarePolynomial_of_isEmpty` and `TauCeti.poincarePolynomial_of_unique_index`: the two
  smallest cases, `1` in rank `0` and `1 + q` in rank `1`.

## Implementation notes

The polynomial is defined and its intrinsic properties are stated under `[Finite W]`, the
enumeration being supplied internally by `Fintype.ofFinite`; only the lemmas whose right-hand side
is itself a `Finset.univ` expression (the two unfolding lemmas) ask for `[Fintype W]`. Counts are
stated with `Nat.card` on a subtype rather than with a `Finset.filter`, so that no `DecidableEq` or
`DecidablePred` argument leaks into the statements, and the degree is characterised by
`IsGreatest` on the range of the length function rather than by a `Finset.sup`.

`coeff_poincarePolynomial` carries `@[simp low]` rather than a plain `@[simp]`: the specialised
`coeff_poincarePolynomial_zero` must fire first, since at equal priority the general lemma rewrites
its left-hand side and the `simpNF` linter then reports the constant-term lemma as not being in
simp-normal form.

Nothing here needs the group to be finitely generated, crystallographic, or attached to a root
system: the statements are about an arbitrary Coxeter system, which is where the roadmap places
them.

## References

This is the "length generating function ... the Poincaré polynomial" item among the consequences
of Layer 3 ("the missing Coxeter combinatorics") in
`TauCetiRoadmap/RepresentationTheory/RootSystems/README.md`.

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Sections 1.4 and 7.1.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.11.
-/

public section

namespace TauCeti

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- The **Poincaré polynomial** of a Coxeter system on a finite group: the length generating
function `∑_{w ∈ W} q^{ℓ(w)}`, viewed as an element of `ℤ[q]`. -/
noncomputable def poincarePolynomial [Finite W] : Polynomial ℤ :=
  letI := Fintype.ofFinite W
  ∑ w : W, Polynomial.X ^ cs.length w

/-- The Poincaré polynomial, unfolded. -/
theorem poincarePolynomial_eq_sum [Fintype W] :
    poincarePolynomial cs = ∑ w : W, Polynomial.X ^ cs.length w := by
  -- the enumeration used in the definition and the ambient one agree, `Fintype W` being a
  -- subsingleton
  rw [poincarePolynomial, Subsingleton.elim (Fintype.ofFinite W) ‹Fintype W›]

/-- Evaluating the Poincaré polynomial at `q` gives the length generating function `∑ q^{ℓ(w)}`. -/
theorem eval_poincarePolynomial [Fintype W] (q : ℤ) :
    (poincarePolynomial cs).eval q = ∑ w : W, q ^ cs.length w := by
  rw [poincarePolynomial_eq_sum, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun w _ => by rw [Polynomial.eval_pow, Polynomial.eval_X]

/-- **The Poincaré polynomial is the length generating function**: its coefficient at `q^k` is the
number of elements of `W` of length `k`. -/
@[simp low]
theorem coeff_poincarePolynomial [Finite W] (k : ℕ) :
    (poincarePolynomial cs).coeff k = (Nat.card {w : W // cs.length w = k} : ℤ) := by
  classical
  have : Fintype W := Fintype.ofFinite W
  rw [poincarePolynomial_eq_sum, Polynomial.finsetSum_coeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Polynomial.coeff_X_pow]
  by_cases h : cs.length w = k
  · simp [h]
  · simp [h, Ne.symm h]

/-- The coefficients of the Poincaré polynomial are nonnegative, being cardinalities. -/
theorem coeff_poincarePolynomial_nonneg [Finite W] (k : ℕ) :
    0 ≤ (poincarePolynomial cs).coeff k := by
  rw [coeff_poincarePolynomial]
  exact Int.natCast_nonneg _

/-- The constant term of the Poincaré polynomial is `1`: the identity is the unique element of
length `0`. -/
@[simp]
theorem coeff_poincarePolynomial_zero [Finite W] : (poincarePolynomial cs).coeff 0 = 1 := by
  rw [coeff_poincarePolynomial]
  norm_cast
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨1, cs.length_one⟩⟩⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  simp only [Subtype.mk.injEq]
  rw [cs.length_eq_zero_iff.mp hu, cs.length_eq_zero_iff.mp hv]

/-- The Poincaré polynomial is nonzero. -/
theorem poincarePolynomial_ne_zero [Finite W] : poincarePolynomial cs ≠ 0 := by
  intro h
  have h0 := coeff_poincarePolynomial_zero cs
  rw [h] at h0
  simp at h0

/-- **The value at `1` is the order of the group**: every element contributes `1`. -/
@[simp]
theorem eval_one_poincarePolynomial [Finite W] :
    (poincarePolynomial cs).eval 1 = (Nat.card W : ℤ) := by
  have : Fintype W := Fintype.ofFinite W
  rw [eval_poincarePolynomial, Nat.card_eq_fintype_card]
  simp

/-- Left multiplication by a simple reflection reverses the sign of the term `(-1)^{ℓ(w)}` of the
alternating sum. -/
private theorem neg_one_pow_length_simple_mul (i : B) (w : W) :
    (-1 : ℤ) ^ cs.length (cs.simple i * w) = -((-1 : ℤ) ^ cs.length w) := by
  rw [neg_one_pow_eq_pow_mod_two, length_simple_mul_mod_two, ← neg_one_pow_eq_pow_mod_two,
    pow_succ]
  ring

/-- **The Poincaré polynomial vanishes at `-1`** as soon as there is at least one simple
reflection: left multiplication by it is a sign-reversing involution of `W`, so the terms of the
alternating sum cancel in pairs. -/
@[simp]
theorem eval_neg_one_poincarePolynomial [Finite W] [Nonempty B] :
    (poincarePolynomial cs).eval (-1) = 0 := by
  obtain ⟨i⟩ := ‹Nonempty B›
  have : Fintype W := Fintype.ofFinite W
  have hne : cs.simple i ≠ 1 := fun h => by simpa [h] using cs.length_simple i
  rw [eval_poincarePolynomial]
  refine Finset.sum_ninvolution (fun w => cs.simple i * w)
    (fun w => by rw [neg_one_pow_length_simple_mul]; ring) (fun w _ hw => hne ?_)
    (fun w => Finset.mem_univ _) fun w => cs.simple_mul_simple_cancel_left i
  simpa using hw

/-! ### Degree -/

/-- **The degree of the Poincaré polynomial is the largest length occurring in `W`**: it is attained
by some element, and no element is longer. -/
theorem natDegree_poincarePolynomial [Finite W] :
    IsGreatest (Set.range cs.length) (poincarePolynomial cs).natDegree := by
  constructor
  · have hne : (poincarePolynomial cs).coeff (poincarePolynomial cs).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr (poincarePolynomial_ne_zero cs)
    rw [coeff_poincarePolynomial] at hne
    have hcard : Nat.card {w : W // cs.length w = (poincarePolynomial cs).natDegree} ≠ 0 := by
      exact_mod_cast hne
    obtain ⟨w, hw⟩ := (Nat.card_ne_zero.mp hcard).1
    exact ⟨w, hw⟩
  · rintro n ⟨w, rfl⟩
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [coeff_poincarePolynomial]
    have hne : Nonempty {v : W // cs.length v = cs.length w} := ⟨⟨w, rfl⟩⟩
    exact_mod_cast Nat.card_pos.ne'

/-- **The leading coefficient counts the elements of maximal length.** -/
theorem leadingCoeff_poincarePolynomial [Finite W] :
    (poincarePolynomial cs).leadingCoeff
      = (Nat.card {w : W // cs.length w = (poincarePolynomial cs).natDegree} : ℤ) := by
  rw [← Polynomial.coeff_natDegree, coeff_poincarePolynomial]

/-! ### Transport along a reindexing or a group isomorphism -/

section Transport

variable {B' H : Type*} [Group H]

/-- **The Poincaré polynomial only depends on the Coxeter system up to relabelling the simple
reflections**, since the length function does (`TauCeti.length_reindex`). -/
@[simp]
theorem poincarePolynomial_reindex [Finite W] (e : B ≃ B') :
    poincarePolynomial (cs.reindex e) = poincarePolynomial cs := by
  have : Fintype W := Fintype.ofFinite W
  rw [poincarePolynomial_eq_sum, poincarePolynomial_eq_sum]
  exact Finset.sum_congr rfl fun w _ => by rw [length_reindex]

/-- **The Poincaré polynomial is invariant under transporting the Coxeter system along a group
isomorphism**, since the length function is (`TauCeti.length_map`). The hypothesis `[Finite H]`
follows from `[Finite W]`, but is needed to state the left-hand side. -/
@[simp]
theorem poincarePolynomial_map [Finite W] [Finite H] (e : W ≃* H) :
    poincarePolynomial (cs.map e) = poincarePolynomial cs := by
  have : Fintype W := Fintype.ofFinite W
  have : Fintype H := Fintype.ofFinite H
  rw [poincarePolynomial_eq_sum, poincarePolynomial_eq_sum]
  exact (Fintype.sum_bijective e e.bijective (fun w => Polynomial.X ^ cs.length w)
    (fun h => Polynomial.X ^ (cs.map e).length h) fun w => by rw [length_map]).symm

end Transport

/-! ### The two smallest cases -/

/-- **The rank-zero case**: with no simple reflections the group is trivial and the Poincaré
polynomial is `1`. -/
@[simp]
theorem poincarePolynomial_of_isEmpty [Finite W] [IsEmpty B] : poincarePolynomial cs = 1 := by
  have : Fintype W := Fintype.ofFinite W
  rw [poincarePolynomial_eq_sum, Finset.sum_eq_single (1 : W)]
  · simp
  · exact fun w _ hw => absurd ((subsingleton_of_isEmpty_index cs).allEq w 1) hw
  · exact fun h => absurd (Finset.mem_univ (1 : W)) h

/-- **The rank-one case**: a Coxeter system with a single simple reflection has Poincaré
polynomial `1 + q`, its group being the two-element group generated by that reflection. -/
@[simp]
theorem poincarePolynomial_of_unique_index [Finite W] [Unique B] :
    poincarePolynomial cs = 1 + Polynomial.X := by
  classical
  have : Fintype W := Fintype.ofFinite W
  have hmem : ∀ w : W, w = 1 ∨ w = cs.simple (default : B) := fun w =>
    cs.simple_induction_left (p := fun v => v = 1 ∨ v = cs.simple (default : B)) w (Or.inl rfl)
      fun v i hv => by
        rw [Subsingleton.elim i (default : B)]
        rcases hv with h | h
        · exact Or.inr (by rw [h, mul_one])
        · exact Or.inl (by rw [h, cs.simple_mul_simple_self])
  have hne : (1 : W) ≠ cs.simple (default : B) := by
    intro h
    have hlen := cs.length_simple (default : B)
    rw [← h, cs.length_one] at hlen
    exact absurd hlen (by norm_num)
  have huniv : (Finset.univ : Finset W) = {1, cs.simple (default : B)} := by
    ext w
    simpa using hmem w
  rw [poincarePolynomial_eq_sum, huniv, Finset.sum_insert (by simpa using hne),
    Finset.sum_singleton, cs.length_one, cs.length_simple, pow_zero, pow_one]

end TauCeti
