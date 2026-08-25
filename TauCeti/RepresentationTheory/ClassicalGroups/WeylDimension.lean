/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Vandermonde
public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight

/-!
# The Weyl dimension formula for `GL n`

The irreducible rational representation of `GL n` with dominant weight `λ₁ ≥ ⋯ ≥ λₙ` has dimension

`∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)`,

the Weyl dimension formula specialized to `GL n`.  This file builds the right-hand side as a
natural number, before any representation is attached to a weight.  That is a step in its own
right: the product is a quotient of integers term by term, and neither the integrality nor the
positivity of the value is visible from the formula as written.

The route through the file is the Vandermonde determinant.  Writing `λ + ρ` for the strictly
decreasing sequence `TauCeti.DominantWeight.rhoShift λ`, `i ↦ λᵢ - i`, the numerator
`TauCeti.weylDimensionNumerator` is the product of its differences, hence — after reversing the
index, so that the sequence increases — the determinant of a Vandermonde matrix
(`TauCeti.weylDimensionNumerator_eq_det_vandermonde`).  Mathlib's
`Matrix.superFactorial_dvd_vandermonde_det` then supplies exactly the divisibility the formula
needs, and the denominator `∏_{i < j} (j - i)` is the same determinant for the sequence
`0, 1, …, n - 1`, so it is the superfactorial `sf (n - 1)`
(`TauCeti.prod_Ioi_sub_eq_superFactorial`).  Dividing gives
`TauCeti.weylDimension`, and the division-free identity
`TauCeti.weylDimension_mul_superFactorial` is the form all later results are proved from; the
quotient form of the definition is recovered over `ℚ` in
`TauCeti.weylDimension_eq_prod_prod_div`.

The classical shift is `λᵢ + n - i` rather than `λᵢ - i`; the two differ by the constant `n`, so
they have the same differences and hence the same Weyl dimension.  Subtracting `i` avoids
truncated subtraction on `ℕ` and is what makes the reversed sequence literally a Vandermonde node
list.

## Main definitions

* `TauCeti.DominantWeight.rhoShift`: the strictly decreasing sequence `λᵢ - i`.
* `TauCeti.weylDimensionNumerator`: the product `∏_{i < j} (λᵢ - λⱼ + j - i)` of its differences.
* `TauCeti.weylDimension`: the dimension predicted by the Weyl dimension formula.

## Main results

* `TauCeti.weylDimension_mul_superFactorial`: the defining identity, division-free.
* `TauCeti.weylDimension_eq_prod_prod_div`: the quotient form of the formula, over `ℚ`.
* `TauCeti.weylDimension_pos`: the dimension is positive.
* `TauCeti.weylDimension_congr`: it depends on the weight only through the differences `λᵢ - λⱼ`,
  whence `TauCeti.weylDimension_shift`: it is unchanged by a determinant twist.
* `TauCeti.weylDimension_eq_one_of_forall_eq`: a constant weight — a power of the determinant — has
  dimension one.
* `TauCeti.weylDimension_fin_two`: for `GL 2` the formula reads `λ₁ - λ₂ + 1`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 5, “The Weyl dimension formula”.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Theorem 6.3 and
  Exercise 15.4.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ}

namespace DominantWeight

/-- The sequence `λᵢ - i` attached to a dominant weight `λ`.  It is the classical `λ + ρ` up to
the constant `n`: the traditional normalization is `λᵢ + n - i`, and only the differences of the
sequence are ever used. -/
def rhoShift (l : DominantWeight n) (i : Fin n) : ℤ := l.1 i - i

/-- The defining equation of `TauCeti.DominantWeight.rhoShift`, its pointwise normal form. -/
@[simp]
theorem rhoShift_apply (l : DominantWeight n) (i : Fin n) : l.rhoShift i = l.1 i - i := by
  simp only [rhoShift]

/-- Subtracting the staircase turns the weak decrease of a dominant weight into strict decrease.
This is what makes every factor of `TauCeti.weylDimensionNumerator` positive. -/
theorem rhoShift_strictAnti (l : DominantWeight n) : StrictAnti l.rhoShift := by
  intro i j hij
  have h : l.1 j ≤ l.1 i := l.antitone hij.le
  have : (i : ℤ) < j := by exact_mod_cast hij
  simp only [rhoShift_apply]
  omega

/-- The differences of `TauCeti.DominantWeight.rhoShift` are the factors of the Weyl dimension
formula. -/
theorem rhoShift_sub_rhoShift (l : DominantWeight n) (i j : Fin n) :
    l.rhoShift i - l.rhoShift j = l.1 i - l.1 j + ((j : ℤ) - i) := by
  simp only [rhoShift_apply]; ring

/-- The determinant twist `λ ↦ λ + m·(1, …, 1)` shifts `TauCeti.DominantWeight.rhoShift` by `m`.
Not a `simp` lemma: `TauCeti.DominantWeight.rhoShift_apply` already rewrites its left-hand side. -/
theorem rhoShift_shift_apply (l : DominantWeight n) (m : ℤ) (i : Fin n) :
    (l.shift m).rhoShift i = l.rhoShift i + m := by
  simp only [rhoShift_apply, shift_apply]; ring

end DominantWeight

/-- Reversing the index of a doubly indexed family turns a product over the pairs `i < j` into the
product over the same pairs of the transposed family.  The pair `(i, j)` with `i < j` is matched
with `(rev j, rev i)`, again in increasing order. -/
private theorem prod_Ioi_rev {M : Type*} [CommMonoid M] (f : Fin n → Fin n → M) :
    (∏ i : Fin n, ∏ j ∈ Ioi i, f (Fin.rev j) (Fin.rev i)) = ∏ i : Fin n, ∏ j ∈ Ioi i, f i j := by
  rw [Finset.prod_sigma' univ (fun i : Fin n => Ioi i) fun i j => f (Fin.rev j) (Fin.rev i),
    Finset.prod_sigma' univ (fun i : Fin n => Ioi i) fun i j => f i j]
  refine Finset.prod_nbij' (fun x => ⟨x.2.rev, x.1.rev⟩) (fun x => ⟨x.2.rev, x.1.rev⟩)
    ?_ ?_ ?_ ?_ ?_ <;>
    simp +contextual [Finset.mem_sigma, mem_Ioi, Fin.rev_lt_rev, Fin.rev_rev]

/-- The superfactorial is positive: it is a product of factorials.  Mathlib has the superfactorial
and its factorial-product expansions but not this consequence. -/
private theorem superFactorial_pos (n : ℕ) : 0 < n.superFactorial := by
  rw [← Nat.prod_range_succ_factorial n]
  exact Finset.prod_pos fun i _ => i.factorial_pos

/-- The denominator of the Weyl dimension formula, `∏_{i < j} (j - i)`, is the superfactorial
`sf (n - 1) = 0! · 1! ⋯ (n-1)!`: it is the Vandermonde determinant of the nodes
`0, 1, …, n - 1`.  Stated over an arbitrary commutative ring, since the formula is used both over
`ℤ`, where the quotient is taken, and over `ℚ`, where it is displayed. -/
theorem prod_Ioi_sub_eq_superFactorial (R : Type*) [CommRing R] (n : ℕ) :
    (∏ i : Fin n, ∏ j ∈ Ioi i, ((j : R) - i)) = ((n - 1).superFactorial : R) := by
  cases n with
  | zero => simp
  | succ m =>
    have h := Matrix.det_vandermonde_id_eq_superFactorial (R := R) m
    rw [Matrix.det_vandermonde] at h
    simpa using h

/-- The **numerator of the Weyl dimension formula**: the product `∏_{i < j} (λᵢ - λⱼ + j - i)` of
the differences of `TauCeti.DominantWeight.rhoShift`. -/
def weylDimensionNumerator (l : DominantWeight n) : ℤ :=
  ∏ i, ∏ j ∈ Ioi i, (l.rhoShift i - l.rhoShift j)

/-- **The numerator in weight coordinates**: expanding the differences of
`TauCeti.DominantWeight.rhoShift` rewrites `TauCeti.weylDimensionNumerator` as the product
`∏_{i < j} (λᵢ - λⱼ + j - i)` of the factors of the Weyl dimension formula.  This is the form every
computation with the numerator starts from. -/
theorem weylDimensionNumerator_eq_prod_prod (l : DominantWeight n) :
    weylDimensionNumerator l = ∏ i, ∏ j ∈ Ioi i, (l.1 i - l.1 j + ((j : ℤ) - i)) := by
  simp only [weylDimensionNumerator, DominantWeight.rhoShift_sub_rhoShift]

/-- Every factor of the numerator is positive, because `TauCeti.DominantWeight.rhoShift` is
strictly decreasing. -/
theorem weylDimensionNumerator_pos (l : DominantWeight n) : 0 < weylDimensionNumerator l :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hj =>
    sub_pos.2 (l.rhoShift_strictAnti (mem_Ioi.1 hj))

/-- **The numerator is a Vandermonde determinant**: reversing the index makes
`TauCeti.DominantWeight.rhoShift` increasing, and the product of the differences of an increasing
sequence is the determinant of the Vandermonde matrix on those nodes. -/
theorem weylDimensionNumerator_eq_det_vandermonde (l : DominantWeight n) :
    weylDimensionNumerator l = (Matrix.vandermonde fun i => l.rhoShift i.rev).det := by
  rw [Matrix.det_vandermonde]
  exact (prod_Ioi_rev fun a b => l.rhoShift a - l.rhoShift b).symm

/-- **Integrality of the Weyl dimension formula**: the denominator `sf (n - 1)` divides the
numerator.  This is Mathlib's divisibility for Vandermonde determinants at integer nodes. -/
theorem superFactorial_dvd_weylDimensionNumerator (l : DominantWeight n) :
    ((n - 1).superFactorial : ℤ) ∣ weylDimensionNumerator l := by
  cases n with
  | zero => simp [weylDimensionNumerator]
  | succ m =>
    rw [weylDimensionNumerator_eq_det_vandermonde]
    simpa using Matrix.superFactorial_dvd_vandermonde_det (v := fun i => l.rhoShift i.rev)

/-- **The Weyl dimension** of a dominant weight `λ` of `GL n`, the value

`∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)`

of the Weyl dimension formula.  It is the dimension of the irreducible rational representation
with highest weight `λ`; the identification with that dimension is downstream of the highest-weight
classification, and what is proved here is that the formula is a well-defined positive natural
number.  The quotient is taken once, of the numerator by the denominator `sf (n - 1)`, rather than
factor by factor; `TauCeti.weylDimension_eq_prod_prod_div` recovers the term-by-term form over
`ℚ`. -/
def weylDimension (l : DominantWeight n) : ℕ :=
  (weylDimensionNumerator l / ((n - 1).superFactorial : ℤ)).toNat

/-- **The defining identity of `TauCeti.weylDimension`**, in division-free form: the dimension
times the denominator `sf (n - 1)` is the numerator `∏_{i < j} (λᵢ - λⱼ + j - i)`. -/
theorem weylDimension_mul_superFactorial (l : DominantWeight n) :
    (weylDimension l : ℤ) * ((n - 1).superFactorial : ℤ) = weylDimensionNumerator l := by
  have hsf : (0 : ℤ) < ((n - 1).superFactorial : ℤ) := by
    exact_mod_cast superFactorial_pos (n - 1)
  have hnonneg : 0 ≤ weylDimensionNumerator l / ((n - 1).superFactorial : ℤ) :=
    Int.ediv_nonneg (weylDimensionNumerator_pos l).le hsf.le
  rw [weylDimension, Int.toNat_of_nonneg hnonneg,
    Int.ediv_mul_cancel (superFactorial_dvd_weylDimensionNumerator l)]

/-- **The Weyl dimension is positive**: the numerator is a product of positive factors, so the
quotient by `sf (n - 1)` cannot vanish. -/
theorem weylDimension_pos (l : DominantWeight n) : 0 < weylDimension l := by
  rcases Nat.eq_zero_or_pos (weylDimension l) with h0 | h
  · have h1 := weylDimension_mul_superFactorial l
    rw [h0] at h1
    simp only [Nat.cast_zero, zero_mul] at h1
    exact absurd h1 (weylDimensionNumerator_pos l).ne
  · exact h

/-- **The Weyl dimension formula in its quotient form**: over `ℚ`, the dimension is the product of
the term-by-term quotients `(λᵢ - λⱼ + j - i) / (j - i)`. -/
theorem weylDimension_eq_prod_prod_div (l : DominantWeight n) :
    (weylDimension l : ℚ) =
      ∏ i : Fin n, ∏ j ∈ Ioi i, ((l.1 i : ℚ) - l.1 j + ((j : ℚ) - i)) / ((j : ℚ) - i) := by
  have hden := prod_Ioi_sub_eq_superFactorial ℚ n
  have hnum : (∏ i : Fin n, ∏ j ∈ Ioi i, ((l.1 i : ℚ) - l.1 j + ((j : ℚ) - i))) =
      ((weylDimensionNumerator l : ℤ) : ℚ) := by
    rw [weylDimensionNumerator_eq_prod_prod]
    push_cast
    rfl
  have hsf : ((n - 1).superFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (superFactorial_pos (n - 1)).ne'
  simp only [Finset.prod_div_distrib]
  rw [hden, hnum, eq_div_iff hsf]
  exact_mod_cast weylDimension_mul_superFactorial l

/-- **The formula reads only the differences of a weight**: two weights with the same differences
`λᵢ - λⱼ` for `i < j` — the only ones the product ranges over — have the same numerator. -/
theorem weylDimensionNumerator_congr {l l' : DominantWeight n}
    (h : ∀ i j, i < j → l.1 i - l.1 j = l'.1 i - l'.1 j) :
    weylDimensionNumerator l = weylDimensionNumerator l' := by
  rw [weylDimensionNumerator_eq_prod_prod, weylDimensionNumerator_eq_prod_prod]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => by
    rw [h i j (mem_Ioi.1 hj)]

/-- **The Weyl dimension reads only the differences of a weight**: two weights with the same
differences `λᵢ - λⱼ` for `i < j` have the same dimension.  Cancelling `sf (n - 1)` in
`TauCeti.weylDimension_mul_superFactorial` reduces this to the numerator. -/
theorem weylDimension_congr {l l' : DominantWeight n}
    (h : ∀ i j, i < j → l.1 i - l.1 j = l'.1 i - l'.1 j) :
    weylDimension l = weylDimension l' := by
  have hsf : (0 : ℤ) < ((n - 1).superFactorial : ℤ) := by
    exact_mod_cast superFactorial_pos (n - 1)
  have h1 : (weylDimension l : ℤ) * ((n - 1).superFactorial : ℤ) =
      (weylDimension l' : ℤ) * ((n - 1).superFactorial : ℤ) :=
    (weylDimension_mul_superFactorial l).trans
      ((weylDimensionNumerator_congr h).trans (weylDimension_mul_superFactorial l').symm)
  exact_mod_cast mul_right_cancel₀ hsf.ne' h1

/-- The numerator is unchanged by the **determinant twist** `λ ↦ λ + m·(1, …, 1)`, since the twist
adds `m` to every entry and so leaves all differences alone. -/
@[simp]
theorem weylDimensionNumerator_shift (l : DominantWeight n) (m : ℤ) :
    weylDimensionNumerator (l.shift m) = weylDimensionNumerator l :=
  weylDimensionNumerator_congr fun i j _ => by simp only [DominantWeight.shift_apply]; ring

/-- Since only the differences of a weight matter, the Weyl dimension is unchanged by the
**determinant twist** `λ ↦ λ + m·(1, …, 1)`, which on representations is tensoring with `detᵐ`. -/
@[simp]
theorem weylDimension_shift (l : DominantWeight n) (m : ℤ) :
    weylDimension (l.shift m) = weylDimension l :=
  weylDimension_congr fun i j _ => by simp only [DominantWeight.shift_apply]; ring

/-- A **constant weight** `(c, …, c)` — the weight of the `c`-th power of the determinant — has
numerator exactly the denominator `sf (n - 1)`. -/
theorem weylDimensionNumerator_eq_superFactorial_of_forall_eq
    {l : DominantWeight n} {c : ℤ} (h : ∀ i, l.1 i = c) :
    weylDimensionNumerator l = ((n - 1).superFactorial : ℤ) := by
  rw [weylDimensionNumerator_eq_prod_prod, ← prod_Ioi_sub_eq_superFactorial ℤ n]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by
    rw [h i, h j]; ring

/-- **A power of the determinant is one-dimensional**: a constant dominant weight has Weyl
dimension `1`. -/
theorem weylDimension_eq_one_of_forall_eq {l : DominantWeight n} {c : ℤ} (h : ∀ i, l.1 i = c) :
    weylDimension l = 1 := by
  have hsf : (0 : ℤ) < ((n - 1).superFactorial : ℤ) := by
    exact_mod_cast superFactorial_pos (n - 1)
  have h1 := weylDimension_mul_superFactorial l
  rw [weylDimensionNumerator_eq_superFactorial_of_forall_eq h] at h1
  have h2 : (weylDimension l : ℤ) = 1 := mul_right_cancel₀ hsf.ne' (h1.trans (one_mul _).symm)
  exact_mod_cast h2

/-- `GL 0` has a single weight, of dimension `1`. -/
@[simp]
theorem weylDimension_fin_zero (l : DominantWeight 0) : weylDimension l = 1 :=
  weylDimension_eq_one_of_forall_eq (c := 0) fun i => i.elim0

/-- Every weight of `GL 1` is a power of the determinant, hence one-dimensional. -/
@[simp]
theorem weylDimension_fin_one (l : DominantWeight 1) : weylDimension l = 1 :=
  weylDimension_eq_one_of_forall_eq (c := l.1 0) fun i => by
    rw [Subsingleton.elim i 0]

/-- **The `GL 2` case**: the irreducible with highest weight `(λ₁, λ₂)` has dimension
`λ₁ - λ₂ + 1`.  For `λ = (d, 0)` this is the `(d+1)`-dimensional symmetric power `Symᵈ`. -/
theorem weylDimension_fin_two (l : DominantWeight 2) :
    (weylDimension l : ℤ) = l.1 0 - l.1 1 + 1 := by
  have hnum : weylDimensionNumerator l = l.1 0 - l.1 1 + 1 := by
    rw [weylDimensionNumerator_eq_prod_prod]
    rw [Fin.prod_univ_two]
    have h0 : (Ioi (0 : Fin 2)) = {1} := by decide
    have h1 : (Ioi (1 : Fin 2)) = ∅ := by decide
    rw [h0, h1]
    norm_num
  have h := weylDimension_mul_superFactorial l
  rw [hnum] at h
  simpa using h

end TauCeti
