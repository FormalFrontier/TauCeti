/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension
import TauCeti.LinearAlgebra.Vandermonde

/-!
# The Gelfand-Tsetlin dimension formula

The Gelfand-Tsetlin patterns with a given weakly decreasing top row `λ` are counted by the Weyl
dimension formula for `GL n`:

`#{P : GTPattern n | topRow P = λ} = ∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)`.

This is `TauCeti.GTPattern.card_topRow_eq_weylDimension`, and its `DominantWeight`-indexed form
`TauCeti.GTPattern.card_topWeight_eq_weylDimension`.  Both sides are already built: the left by
`TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count`, the right by
`TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension`.  What is proved here is that they
agree, so that the two candidate dimensions for the irreducible rational representation of `GL n`
of highest weight `λ` — the number of Gelfand-Tsetlin patterns, and the Weyl product formula —
are the same natural number.  That either of them *is* the dimension of a representation is not
proved here and cannot yet be stated: no representation and no Gelfand-Tsetlin basis is
constructed, and none is used.  This is an identity between a lattice-point count and a product
formula.

## The proof

The proof is the branching recursion, exactly as the roadmap asks: deleting the top row of a
pattern gives `TauCeti.GTPattern.card_topRow_succ`, which counts the patterns over `λ` by the
patterns over each sequence interlacing `λ`.  So it suffices to know that the Weyl dimension
satisfies the same recursion, `∑_{μ ≺ λ} dim V_μ = dim V_λ`.

In the shifted coordinates `xₖ = k - λₖ`, which turn a weakly decreasing sequence into a weakly
increasing one, the Weyl numerator `∏_{i<j} (λᵢ - λⱼ + j - i)` is the Vandermonde determinant of
`x`, and the interlacing condition becomes the box `xᵢ ≤ yᵢ ≤ xᵢ₊₁ - 1`.  The recursion is then
exactly the box-sum identity `TauCeti.factorial_mul_sum_det_vandermonde`, the factor `n !` being
the ratio of the two superfactorial denominators.

## Main results

* `TauCeti.GTPattern.card_topRow_eq_weylDimension`: **the Gelfand-Tsetlin dimension formula.**
* `TauCeti.GTPattern.card_topWeight_eq_weylDimension`: the same, indexed by a dominant weight.
* `TauCeti.weylDimension_two_one_zero`: the `GL 3` acceptance example, `dim V_{(2,1,0)} = 8`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "The Gelfand-Tsetlin dimension formula".
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3 and Exercise 15.4.
-/

public section

namespace TauCeti

open Finset

/-! ### Two reformulations -/

/-- The superfactorial denominators of consecutive Weyl dimension formulas differ by `n !`. -/
private theorem superFactorial_eq_factorial_mul (n : ℕ) :
    (n.superFactorial : ℤ) = (Nat.factorial n : ℤ) * ((n - 1).superFactorial : ℤ) := by
  cases n with
  | zero => simp
  | succ m => simp [Nat.superFactorial_succ]

/-- **The Weyl numerator is a Vandermonde determinant.**  Subtracting a weight from the staircase,
`k ↦ k - λₖ`, turns a weakly decreasing sequence into a weakly increasing one and rewrites
`∏_{i < j} (λᵢ - λⱼ + j - i)` as the Vandermonde determinant of the result.  This is the
reformulation in which the branching recursion is a statement about Vandermonde determinants.

The existing `TauCeti.weylDimensionNumerator_eq_det_vandermonde` reverses the index instead of
negating it; that reindexing does not carry the interlacing condition to a box of nested
intervals, which is what the recursion below needs. -/
private theorem prod_Ioi_eq_det_vandermonde {n : ℕ} (l : Fin n → ℤ) :
    (∏ i : Fin n, ∏ j ∈ Ioi i, (l i - l j + ((j : ℤ) - i)))
      = (Matrix.vandermonde fun k : Fin n => (k : ℤ) - l k).det := by
  rw [Matrix.det_vandermonde]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by ring

/-! ### The branching recursion for the Weyl numerator -/

/-- **The Weyl numerators satisfy the branching recursion.**  Summing the Weyl numerator over the
sequences interlacing `l` gives the Weyl numerator of `l`, up to the factor `n !` by which the two
superfactorial denominators differ.  Equivalently: `∑_{μ ≺ λ} dim V_μ = dim V_λ`, the numerical
shadow of the multiplicity-free branching `GL (n + 1) ↓ GL n`. -/
private theorem factorial_mul_sum_interlacing_prod {n : ℕ} (l : Fin (n + 1) → ℤ)
    (hl : Antitone l) :
    (Nat.factorial n : ℤ) * ∑ m ∈ interlacingFinset l,
        ∏ i : Fin n, ∏ j ∈ Ioi i, (m i - m j + ((j : ℤ) - i))
      = ∏ i : Fin (n + 1), ∏ j ∈ Ioi i, (l i - l j + ((j : ℤ) - i)) := by
  have hmono : ∀ i : Fin n,
      ((i.castSucc : Fin (n + 1)) : ℤ) - l i.castSucc
        ≤ ((i.succ : Fin (n + 1)) : ℤ) - l i.succ := by
    intro i
    have h := hl (Fin.castSucc_le_succ i)
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hmain := factorial_mul_sum_det_vandermonde (fun k : Fin (n + 1) => (k : ℤ) - l k) hmono
  rw [prod_Ioi_eq_det_vandermonde l, ← hmain,
    Finset.sum_congr rfl fun m (_ : m ∈ interlacingFinset l) => prod_Ioi_eq_det_vandermonde m]
  congr 1
  refine Finset.sum_nbij' (fun m => fun k : Fin n => (k : ℤ) - m k)
    (fun y => fun k : Fin n => (k : ℤ) - y k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_interlacingFinset] at hm
    rw [Finset.mem_Icc]
    refine ⟨fun k => ?_, fun k => ?_⟩
    · have := hm.le_castSucc k
      simp only [Fin.val_castSucc]
      omega
    · have := hm.succ_le k
      simp only [Fin.val_succ]
      omega
  · intro y hy
    rw [Finset.mem_Icc] at hy
    rw [mem_interlacingFinset, interlaces_iff]
    intro k
    have h1 := hy.1 k
    have h2 := hy.2 k
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
    omega
  · exact fun m _ => funext fun k => by ring
  · exact fun y _ => funext fun k => by ring
  · exact fun m _ => rfl

/-! ### The dimension formula -/

namespace GTPattern

/-- **The Gelfand-Tsetlin count times the Weyl denominator is the Weyl numerator.**  The
division-free form of the dimension formula, proved by induction on `n` from the branching
recursion `TauCeti.GTPattern.card_topRow_succ`.

The hypothesis that `l` is weakly decreasing is needed: a sequence that is not carries no pattern
at all, while the product on the right is generally nonzero. -/
private theorem card_topRow_mul_superFactorial :
    ∀ (n : ℕ) (l : Fin n → ℤ), Antitone l →
      (Nat.card {P : GTPattern n // P.topRow = l} : ℤ) * ((n - 1).superFactorial : ℤ)
        = ∏ i : Fin n, ∏ j ∈ Ioi i, (l i - l j + ((j : ℤ) - i)) := by
  intro n
  induction n with
  | zero =>
    intro l _
    have hcard : Nat.card {P : GTPattern 0 // P.topRow = l} = 1 :=
      Nat.card_eq_one_iff_unique.mpr
        ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨⟨default, funext fun i => i.elim0⟩⟩⟩
    rw [hcard]
    simp
  | succ n ih =>
    intro l hl
    have hstep : (Nat.card {P : GTPattern (n + 1) // P.topRow = l} : ℤ)
        = ∑ m ∈ interlacingFinset l, (Nat.card {Q : GTPattern n // Q.topRow = m} : ℤ) := by
      rw [card_topRow_succ, Nat.cast_sum]
    have hsf : ((n + 1 - 1).superFactorial : ℤ)
        = (Nat.factorial n : ℤ) * ((n - 1).superFactorial : ℤ) := by
      simpa using superFactorial_eq_factorial_mul n
    have hL : (Nat.card {P : GTPattern (n + 1) // P.topRow = l} : ℤ)
          * ((n + 1 - 1).superFactorial : ℤ)
        = (Nat.factorial n : ℤ) * ∑ m ∈ interlacingFinset l,
            (Nat.card {Q : GTPattern n // Q.topRow = m} : ℤ) * ((n - 1).superFactorial : ℤ) := by
      rw [hstep, hsf, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hL, Finset.sum_congr rfl fun m hm =>
      ih m (mem_interlacingFinset.mp hm).antitone]
    exact factorial_mul_sum_interlacing_prod l hl

/-- **The Gelfand-Tsetlin dimension formula.**  The Gelfand-Tsetlin patterns with top row a
weakly decreasing sequence `λ` are counted by the Weyl dimension formula
`∏_{i < j} (λᵢ - λⱼ + j - i) / (j - i)`.

Both sides are candidates for the dimension of the irreducible rational representation of `GL n`
with highest weight `λ`, but that representation and the Gelfand-Tsetlin basis are not built here
and do not enter the proof: what is proved is the identity of a lattice-point count with a product
formula, obtained by checking that both satisfy the branching recursion of `GL (n + 1) ↓ GL n`.

This is deliberately not a `simp` lemma: `{P : GTPattern n // P.topRow = l}` carries a `Fintype`
instance, so `Nat.card_eq_fintype_card` rewrites the left-hand side first and the `simpNF` linter
rejects the tag.  The `DominantWeight`-indexed
`TauCeti.GTPattern.card_topWeight_eq_weylDimension` below, whose subtype has no such instance, is
the `simp` form. -/
theorem card_topRow_eq_weylDimension {n : ℕ} (l : DominantWeight n) :
    Nat.card {P : GTPattern n // P.topRow = (l : Fin n → ℤ)} = weylDimension l := by
  have hsf : ((n - 1).superFactorial : ℤ) ≠ 0 := by
    intro h0
    have hmul := weylDimension_mul_superFactorial l
    rw [h0, mul_zero] at hmul
    exact (weylDimensionNumerator_pos l).ne hmul
  have h := (card_topRow_mul_superFactorial n l.1 l.2).trans
    (weylDimensionNumerator_eq_prod_prod l).symm
  have h' := h.trans (weylDimension_mul_superFactorial l).symm
  exact_mod_cast mul_right_cancel₀ hsf h'

/-- **The Gelfand-Tsetlin dimension formula, indexed by a dominant weight.**  The form the
downstream representation theory consumes: fixing the top weight rather than the top row. -/
@[simp]
theorem card_topWeight_eq_weylDimension {n : ℕ} (l : DominantWeight n) :
    Nat.card {P : GTPattern n // P.topWeight = l} = weylDimension l :=
  (card_topWeight_eq_card_topRow l).trans (card_topRow_eq_weylDimension l)

end GTPattern

/-- **The `GL 3` acceptance example**: the weight `(2, 1, 0)` has Weyl dimension `8`, the dimension
of the adjoint representation of `SL 3`.  Read off the eight Gelfand-Tsetlin patterns over that top
row (`TauCeti.GTPattern.card_topRow_three_two_one_zero`) through the dimension formula, rather than
by evaluating the product. -/
theorem weylDimension_two_one_zero :
    weylDimension (⟨![2, 1, 0], by decide⟩ : DominantWeight 3) = 8 :=
  (GTPattern.card_topRow_eq_weylDimension ⟨![2, 1, 0], by decide⟩).symm.trans
    GTPattern.card_topRow_three_two_one_zero

end TauCeti
