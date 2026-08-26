/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.Coxeter.Length

/-!
# The Poincaré polynomial of a finite Coxeter system

For a Coxeter system `cs : CoxeterSystem M W` with `W` finite, the **length generating function**
`∑_{w ∈ W} q^{ℓ(w)}` is a genuine polynomial with integer coefficients, the **Poincaré polynomial**
of `cs`. This file introduces it and proves the elementary facts that make it a generating
function: its coefficient at `k` counts the elements of length `k`, its value at `1` is the order
of `W`, its constant term is `1`, and its degree is the largest length occurring in `W`.

The theorem with content beyond bookkeeping is the value at `-1`. Left multiplication by a fixed
simple reflection is a bijection of `W` that flips the parity of the length
(`CoxeterSystem.length_mul_mod_two`), so it pairs the elements of even length with those of odd
length. Hence the alternating sum `∑_{w ∈ W} (-1)^{ℓ(w)}` vanishes as soon as there is at least one
simple reflection. That pairing is packaged as an explicit equivalence, so it also gives the
parity count with no finiteness hypothesis at all, and the evenness of the order of a Coxeter group
of positive rank.

At the other extreme, a Coxeter system indexed by an empty type has a trivial group -- every
element is the product of a word in the generators, and there are no generators -- so its Poincaré
polynomial is `1`. That degenerate case is recorded as well, since it is what pins the
normalisation of the constant term.

## Main definitions

* `TauCeti.lengthParityEquiv`: left multiplication by a simple reflection, as an equivalence
  between the even-length and the odd-length elements.
* `TauCeti.poincarePolynomial`: the Poincaré polynomial `∑_{w ∈ W} q^{ℓ(w)} ∈ ℤ[q]` of a Coxeter
  system on a finite group.

## Main results

* `TauCeti.natCard_length_even_eq_natCard_length_odd`: as many elements have even length as odd
  length, provided there is at least one simple reflection.
* `TauCeti.even_card_of_nonempty_index`: hence a Coxeter group of positive rank has even order.
* `TauCeti.coeff_poincarePolynomial`: the coefficient of `q^k` counts the elements of length `k`.
* `TauCeti.eval_one_poincarePolynomial`: the value at `1` is `|W|`.
* `TauCeti.eval_neg_one_poincarePolynomial`: the value at `-1` is `0` when the simple reflections
  are indexed by a nonempty type.
* `TauCeti.natDegree_poincarePolynomial` and `TauCeti.leadingCoeff_poincarePolynomial`: the degree
  is the maximal length, and the leading coefficient counts the elements attaining it.
* `TauCeti.poincarePolynomial_of_isEmpty` and `TauCeti.poincarePolynomial_of_unique_index`: the two
  smallest cases, `1` in rank `0` and `1 + q` in rank `1`.

## Implementation notes

The polynomial is defined by an honest `Finset` sum over `W`, so it needs `[Fintype W]` rather than
`[Finite W]`; the intended instances (Weyl groups of finite root systems, finite reflection groups)
carry one, and `Fintype.ofFinite` supplies it otherwise. Counts are stated with `Nat.card` on a
subtype rather than with a `Finset.filter`, so that no `DecidableEq` or `DecidablePred` argument
leaks into the statements.

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
private theorem length_simple_mul_mod_two (i : B) (w : W) :
    cs.length (cs.simple i * w) % 2 = (cs.length w + 1) % 2 := by
  rw [cs.length_mul_mod_two, cs.length_simple, Nat.add_comm]

/-- Left multiplication by a simple reflection turns an element of even length into one of odd
length, and only those. -/
theorem odd_length_simple_mul_iff (i : B) (w : W) :
    Odd (cs.length (cs.simple i * w)) ↔ Even (cs.length w) := by
  rw [Nat.odd_iff, Nat.even_iff, length_simple_mul_mod_two]
  omega

/-- Left multiplication by a simple reflection turns an element of odd length into one of even
length, and only those. -/
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

/-- **The two parity classes of a Coxeter group of positive rank are equinumerous**: there are as
many elements of even length as of odd length. No finiteness is needed, since the two classes are
matched by an explicit bijection. -/
theorem natCard_length_even_eq_natCard_length_odd [Nonempty B] :
    Nat.card {w : W // Even (cs.length w)} = Nat.card {w : W // Odd (cs.length w)} :=
  Nat.card_congr (lengthParityEquiv cs (Classical.arbitrary B))

include cs in
/-- **A Coxeter group of positive rank has even order**, the two parity classes of the length
splitting it in half. -/
theorem even_card_of_nonempty_index [Fintype W] [Nonempty B] : Even (Fintype.card W) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty B›
  have hsplit : Fintype.card {w : W // Even (cs.length w)}
      + Fintype.card {w : W // ¬ Even (cs.length w)} = Fintype.card W := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl fun w : W => Even (cs.length w))
  have hmatch : Fintype.card {w : W // ¬ Even (cs.length w)}
      = Fintype.card {w : W // Even (cs.length w)} :=
    Fintype.card_congr
      ((Equiv.subtypeEquivRight fun w : W => Nat.not_even_iff_odd).trans
        (lengthParityEquiv cs i).symm)
  exact ⟨Fintype.card {w : W // Even (cs.length w)}, by omega⟩

/-! ### The Poincaré polynomial -/

section Fintype

variable [Fintype W]

/-- The **Poincaré polynomial** of a Coxeter system on a finite group: the length generating
function `∑_{w ∈ W} q^{ℓ(w)}`, viewed as an element of `ℤ[q]`. -/
noncomputable def poincarePolynomial : Polynomial ℤ :=
  ∑ w : W, Polynomial.X ^ cs.length w

/-- The Poincaré polynomial, unfolded. -/
theorem poincarePolynomial_eq_sum :
    poincarePolynomial cs = ∑ w : W, Polynomial.X ^ cs.length w := (rfl)

/-- Evaluating the Poincaré polynomial at `q` gives the length generating function `∑ q^{ℓ(w)}`. -/
theorem eval_poincarePolynomial (q : ℤ) :
    (poincarePolynomial cs).eval q = ∑ w : W, q ^ cs.length w := by
  rw [poincarePolynomial_eq_sum, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun w _ => by rw [Polynomial.eval_pow, Polynomial.eval_X]

/-- **The Poincaré polynomial is the length generating function**: its coefficient at `q^k` is the
number of elements of `W` of length `k`. -/
theorem coeff_poincarePolynomial (k : ℕ) :
    (poincarePolynomial cs).coeff k = (Nat.card {w : W // cs.length w = k} : ℤ) := by
  classical
  rw [poincarePolynomial_eq_sum, Polynomial.finsetSum_coeff, Nat.card_eq_fintype_card,
    Fintype.card_subtype, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Polynomial.coeff_X_pow]
  by_cases h : cs.length w = k
  · simp [h]
  · simp [h, Ne.symm h]

/-- The coefficients of the Poincaré polynomial are nonnegative, being cardinalities. -/
theorem coeff_poincarePolynomial_nonneg (k : ℕ) : 0 ≤ (poincarePolynomial cs).coeff k := by
  rw [coeff_poincarePolynomial]
  exact Int.natCast_nonneg _

/-- The constant term of the Poincaré polynomial is `1`: the identity is the unique element of
length `0`. -/
theorem coeff_poincarePolynomial_zero : (poincarePolynomial cs).coeff 0 = 1 := by
  rw [coeff_poincarePolynomial]
  norm_cast
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨?_⟩, ⟨⟨1, cs.length_one⟩⟩⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  simp only [Subtype.mk.injEq]
  rw [cs.length_eq_zero_iff.mp hu, cs.length_eq_zero_iff.mp hv]

/-- The Poincaré polynomial is nonzero. -/
theorem poincarePolynomial_ne_zero : poincarePolynomial cs ≠ 0 := by
  intro h
  have h0 := coeff_poincarePolynomial_zero cs
  rw [h] at h0
  simp at h0

/-- **The value at `1` is the order of the group**: every element contributes `1`. -/
theorem eval_one_poincarePolynomial :
    (poincarePolynomial cs).eval 1 = (Fintype.card W : ℤ) := by
  rw [eval_poincarePolynomial]
  simp

/-- **The Poincaré polynomial vanishes at `-1`** as soon as there is at least one simple
reflection: left multiplication by it is a bijection of `W` reversing the sign of every term of the
alternating sum. -/
theorem eval_neg_one_poincarePolynomial [Nonempty B] :
    (poincarePolynomial cs).eval (-1) = 0 := by
  obtain ⟨i⟩ := ‹Nonempty B›
  rw [eval_poincarePolynomial]
  have hshift : ∑ w : W, (-1 : ℤ) ^ cs.length (cs.simple i * w)
      = ∑ w : W, (-1 : ℤ) ^ cs.length w :=
    Fintype.sum_equiv (Equiv.mulLeft (cs.simple i))
      (fun w => (-1 : ℤ) ^ cs.length (cs.simple i * w)) (fun w => (-1 : ℤ) ^ cs.length w)
      fun w => by rw [Equiv.coe_mulLeft]
  have hsign : ∀ w : W,
      (-1 : ℤ) ^ cs.length (cs.simple i * w) = -((-1 : ℤ) ^ cs.length w) := by
    intro w
    rw [neg_one_pow_eq_pow_mod_two, length_simple_mul_mod_two, ← neg_one_pow_eq_pow_mod_two,
      pow_succ]
    ring
  have hneg : ∑ w : W, (-1 : ℤ) ^ cs.length w = -∑ w : W, (-1 : ℤ) ^ cs.length w :=
    calc ∑ w : W, (-1 : ℤ) ^ cs.length w
        = ∑ w : W, (-1 : ℤ) ^ cs.length (cs.simple i * w) := hshift.symm
      _ = ∑ w : W, -((-1 : ℤ) ^ cs.length w) := Finset.sum_congr rfl fun w _ => hsign w
      _ = -∑ w : W, (-1 : ℤ) ^ cs.length w := Finset.sum_neg_distrib _
  linarith

/-! ### Degree -/

/-- **The degree of the Poincaré polynomial is the largest length occurring in `W`.** -/
theorem natDegree_poincarePolynomial :
    (poincarePolynomial cs).natDegree = Finset.univ.sup fun w : W => cs.length w := by
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_poincarePolynomial]
    have hempty : IsEmpty {w : W // cs.length w = m} := by
      constructor
      rintro ⟨w, hw⟩
      have hle : cs.length w ≤ Finset.univ.sup fun v : W => cs.length v :=
        Finset.le_sup (f := fun v : W => cs.length v) (Finset.mem_univ w)
      omega
    rw [Nat.card_of_isEmpty]
    simp
  · obtain ⟨w, -, hw⟩ :=
      Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun v : W => cs.length v
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hw, coeff_poincarePolynomial]
    have hne : Nonempty {v : W // cs.length v = cs.length w} := ⟨⟨w, rfl⟩⟩
    exact_mod_cast Nat.card_pos.ne'

/-- **The leading coefficient counts the elements of maximal length.** -/
theorem leadingCoeff_poincarePolynomial :
    (poincarePolynomial cs).leadingCoeff
      = (Nat.card {w : W // cs.length w = Finset.univ.sup fun v : W => cs.length v} : ℤ) := by
  rw [← Polynomial.coeff_natDegree, natDegree_poincarePolynomial, coeff_poincarePolynomial]

/-! ### The two smallest cases -/

/-- **The rank-zero case**: with no simple reflections the group is trivial and the Poincaré
polynomial is `1`. -/
theorem poincarePolynomial_of_isEmpty [IsEmpty B] : poincarePolynomial cs = 1 := by
  rw [poincarePolynomial_eq_sum, Finset.sum_eq_single (1 : W)]
  · simp
  · exact fun w _ hw => absurd ((subsingleton_of_isEmpty_index cs).allEq w 1) hw
  · exact fun h => absurd (Finset.mem_univ (1 : W)) h

/-- **The rank-one case**: a Coxeter system with a single simple reflection has Poincaré
polynomial `1 + q`, its group being the two-element group generated by that reflection. -/
theorem poincarePolynomial_of_unique_index [Unique B] :
    poincarePolynomial cs = 1 + Polynomial.X := by
  classical
  have hword : ∀ ω : List B,
      cs.wordProd ω = 1 ∨ cs.wordProd ω = cs.simple (default : B) := by
    intro ω
    induction ω with
    | nil => exact Or.inl (by simp)
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, Subsingleton.elim i (default : B)]
      rcases ih with h | h
      · exact Or.inr (by rw [h, mul_one])
      · exact Or.inl (by rw [h, cs.simple_mul_simple_self])
  have hmem : ∀ w : W, w = 1 ∨ w = cs.simple (default : B) := by
    intro w
    obtain ⟨ω, -, rfl⟩ := cs.exists_isReduced w
    exact hword ω
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

end Fintype

end TauCeti
