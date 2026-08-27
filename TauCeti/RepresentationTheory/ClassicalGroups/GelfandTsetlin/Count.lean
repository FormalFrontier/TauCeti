/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Pi.Interval
import Mathlib.Tactic.FinCases

/-!
# Counting Gelfand-Tsetlin patterns, from the branching side

Deleting the top row of a Gelfand-Tsetlin pattern with `n + 1` rows and top row `l` leaves a
pattern with `n` rows whose own top row interlaces `l`
(`TauCeti.GTPattern.truncateEquiv`).  Sorting those by the row they expose turns that bijection
into a **count**: the patterns over `l` are as many as the patterns over each interlacing `m`,
summed over `m`.  That recursion,

`#{P : GTPattern (n + 1) | top row l} = ∑_{m ≺ l} #{Q : GTPattern n | top row m}`,

is `TauCeti.GTPattern.card_topRow_succ`, and it is the combinatorial shadow of the
multiplicity-free branching `GL (n + 1) ↓ GL n`: a basis vector of `V_l` is a constituent of the
restriction together with a basis vector of it.  Iterating it down the chain
`GL 1 ⊂ ⋯ ⊂ GL n` is how the Gelfand-Tsetlin dimension formula is meant to be proved — from the
branching, by induction on `n`, and independently of the Weyl dimension formula.

The sum is indexed by `TauCeti.interlacingFinset`, the sequences interlacing `l` collected into a
`Finset`.  Interlacing is a two-sided bound at each index, so this is nothing but the interval
`Finset.Icc` of the pointwise order on `Fin n → ℤ`, and no new finiteness argument is needed.

Two further readings of the recursion are recorded.  Which top rows occur at all is settled by
`TauCeti.GTPattern.nonempty_topRow_eq_iff`: a sequence is the top row of some pattern exactly when
it is weakly decreasing, that is, exactly when it is a dominant weight.  Both directions are
one-line consequences of the machinery — reading a top row produces a weakly decreasing sequence,
and prepending a dominant `l` on top of the pattern built inductively over `l ∘ Fin.castSucc`
produces a pattern over `l`.  And unwinding the recursion twice gives the `GL 3` count
`TauCeti.GTPattern.card_topRow_three` as an explicit double sum over the two free entries of the
middle and bottom rows, which settles the roadmap's two `GL 3` acceptance examples: the polynomial
top row `(2, 1, 0)` and its determinant twist `(1, 0, -1)` both carry exactly `8` patterns.

## Main definitions

* `TauCeti.interlacingFinset`: the sequences interlacing a given one, as a `Finset`.

## Main results

* `TauCeti.card_interlacingFinset`: how many sequences interlace a given one.
* `TauCeti.GTPattern.truncateSigmaEquiv`: the patterns over `l` sorted by the row below the top.
* `TauCeti.GTPattern.card_topRow_succ`: **the branching recursion for the pattern count**.
* `TauCeti.GTPattern.nonempty_topRow_eq_iff` and `TauCeti.GTPattern.card_topRow_pos_iff`: a
  sequence is the top row of a pattern exactly when it is weakly decreasing.
* `TauCeti.GTPattern.card_topWeight_eq_card_topRow`: counting by top weight is counting by top row.
* `TauCeti.GTPattern.card_topRow_three`: the `GL 3` count as a double sum, and
  `TauCeti.GTPattern.card_topRow_three_two_one_zero`,
  `TauCeti.GTPattern.card_topRow_three_one_zero_neg_one`: the two `GL 3` acceptance examples.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "the Gelfand-Tsetlin dimension formula", which asks for the count to be proved from the
  branching side, and the two `GL 3` worked examples.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

namespace TauCeti

variable {n : ℕ}

/-! ### The interlacing sequences as a finite set -/

/-- The sequences interlacing `l`, collected into a `Finset`.

`TauCeti.Interlaces l m` bounds `m i` between `l i.succ` and `l i.castSucc` and says nothing else,
so the interlacing sequences are exactly the points of an interval of the pointwise order on
`Fin n → ℤ`; `TauCeti.mem_interlacingFinset` is that identification.  For a dominant `l` this is
the index set of the constituents of `V_l` restricted along `GL n ↪ GL (n + 1)`. -/
def interlacingFinset (l : Fin (n + 1) → ℤ) : Finset (Fin n → ℤ) :=
  Finset.Icc (fun i => l i.succ) (fun i => l i.castSucc)

/-- The members of `TauCeti.interlacingFinset l` are exactly the sequences interlacing `l`: the
two bounds defining the interval are the two interlacing inequalities, read at every index at
once. -/
@[simp]
theorem mem_interlacingFinset {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ} :
    m ∈ interlacingFinset l ↔ Interlaces l m := by
  simp only [interlacingFinset, Finset.mem_Icc, Pi.le_def, interlaces_iff, forall_and]
  exact and_comm

/-- **How many sequences interlace `l`**: the two-sided bounds are independent from index to
index, so the count is the product of the lengths of the intervals `[lᵢ₊₁, lᵢ]`.  For a dominant
`l` this is the number of constituents of `V_l` restricted along `GL n ↪ GL (n + 1)`, each of
which is multiplicity-free. -/
theorem card_interlacingFinset (l : Fin (n + 1) → ℤ) :
    (interlacingFinset l).card = ∏ i : Fin n, (l i.castSucc + 1 - l i.succ).toNat := by
  rw [interlacingFinset, Pi.card_Icc]
  exact Finset.prod_congr rfl fun i _ => Int.card_Icc _ _

namespace GTPattern

/-! ### The branching recursion -/

/-- **The patterns over `l`, sorted by the row below the top.**  Deleting the top row of a pattern
with `n + 1` rows and top row `l` leaves a pattern with `n` rows whose top row interlaces `l`
(`TauCeti.GTPattern.truncateEquiv`); recording that row as the index of a `Sigma` type splits the
patterns over `l` into the fibres of the exposed row.  This is the bookkeeping form of the
multiplicity-free branching `GL (n + 1) ↓ GL n`. -/
def truncateSigmaEquiv (l : Fin (n + 1) → ℤ) :
    {P : GTPattern (n + 1) // P.topRow = l} ≃
      Σ m : interlacingFinset l, {Q : GTPattern n // Q.topRow = (m : Fin n → ℤ)} :=
  (truncateEquiv l).trans
    { toFun Q := ⟨⟨Q.1.topRow, mem_interlacingFinset.mpr Q.2⟩, ⟨Q.1, rfl⟩⟩
      invFun x := ⟨x.2.1, by rw [x.2.2]; exact mem_interlacingFinset.mp x.1.2⟩
      left_inv _ := rfl
      right_inv := by
        rintro ⟨⟨m, hm⟩, ⟨Q, hQ⟩⟩
        have hm' : Q.topRow = m := hQ
        subst hm'
        rfl }

/-- **The branching recursion for the pattern count.**  The Gelfand-Tsetlin patterns with `n + 1`
rows and top row `l` are counted by the patterns with `n` rows, summed over the sequences
interlacing `l`.

For a dominant `l` this is the count of a basis of `V_l` read off the multiplicity-free
restriction `GL (n + 1) ↓ GL n`: each interlacing `m` contributes the dimension of `V_m`.  For an
arbitrary `l` it is a bijection between finite sets and nothing more; both sides vanish unless `l`
is weakly decreasing (`TauCeti.GTPattern.card_topRow_pos_iff`).  Iterated, this is the route the
roadmap asks for to the Gelfand-Tsetlin dimension formula: by induction on `n` from the branching,
not from the Weyl dimension formula. -/
theorem card_topRow_succ (l : Fin (n + 1) → ℤ) :
    Nat.card {P : GTPattern (n + 1) // P.topRow = l}
      = ∑ m ∈ interlacingFinset l, Nat.card {Q : GTPattern n // Q.topRow = m} := by
  rw [Nat.card_congr (truncateSigmaEquiv l), Nat.card_sigma]
  exact Finset.sum_attach (interlacingFinset l) fun m => Nat.card {Q : GTPattern n // Q.topRow = m}

/-! ### Which sequences are top rows -/

/-- **A sequence is the top row of a pattern exactly when it is weakly decreasing**, that is,
exactly when it is a dominant weight.  Reading a top row gives a weakly decreasing sequence
(`TauCeti.GTPattern.topRow_antitone`); conversely a weakly decreasing `l` interlaces its own
truncation `l ∘ Fin.castSucc`, so a pattern over `l` is built by prepending `l` to a pattern
supplied inductively. -/
theorem nonempty_topRow_eq_iff (l : Fin n → ℤ) :
    Nonempty {P : GTPattern n // P.topRow = l} ↔ Antitone l := by
  refine ⟨fun ⟨⟨P, hP⟩⟩ => hP ▸ P.topRow_antitone, ?_⟩
  induction n with
  | zero => exact fun _ => ⟨⟨default, funext fun i => i.elim0⟩⟩
  | succ n ih =>
    intro hl
    obtain ⟨⟨Q, hQ⟩⟩ := ih (fun i => l i.castSucc)
      fun _ _ hij => hl (Fin.castSucc_le_castSucc_iff.mpr hij)
    have h : Interlaces l Q.topRow :=
      interlaces_iff.mpr fun i => by rw [hQ]; exact ⟨le_rfl, hl i.castSucc_le_succ⟩
    exact ⟨⟨extend Q l h, topRow_extend _ _ _⟩⟩

/-- **A top row is counted at least once exactly when it is weakly decreasing.**  The `Nat.card`
form of `TauCeti.GTPattern.nonempty_topRow_eq_iff`, available because only finitely many patterns
share a top row. -/
theorem card_topRow_pos_iff (l : Fin n → ℤ) :
    0 < Nat.card {P : GTPattern n // P.topRow = l} ↔ Antitone l := by
  rw [Nat.card_pos_iff, and_iff_left (finite_topRow_eq l), nonempty_topRow_eq_iff]

/-- **Counting patterns by top weight is counting them by top row.**  A
`TauCeti.DominantWeight` is a sequence together with a proof, so fixing the top weight and fixing
the top row cut out the same patterns.  This is what lets the recursion above feed the
top-weight-indexed counts of `TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Shift`. -/
theorem card_topWeight_eq_card_topRow (l : DominantWeight n) :
    Nat.card {P : GTPattern n // P.topWeight = l}
      = Nat.card {P : GTPattern n // P.topRow = (l : Fin n → ℤ)} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => by rw [Subtype.ext_iff, topWeight_coe])

/-! ### The count for `GL 3` -/

/-- **The count for `GL 3`.**  Unwinding the branching recursion once and then the `GL 2` count
`TauCeti.GTPattern.card_topRow_two_eq_toNat_sub_add_one`, the patterns with top row
`(λ₀, λ₁, λ₂)` are counted by a double sum over the two entries `a ≥ b` of the middle row, each
contributing the `(a - b + 1)` choices of bottom entry.

As everywhere in this development the top row is an arbitrary integer sequence: for a top row that
is not weakly decreasing one of the two intervals is empty and the count is `0`. -/
theorem card_topRow_three (l : Fin 3 → ℤ) :
    Nat.card {P : GTPattern 3 // P.topRow = l}
      = ∑ a ∈ Finset.Icc (l 1) (l 0), ∑ b ∈ Finset.Icc (l 2) (l 1), (a - b + 1).toNat := by
  rw [card_topRow_succ, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun m => (m 0, m 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [mem_interlacingFinset] at hm
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hm.succ_le 0, hm.le_castSucc 0⟩,
        Finset.mem_Icc.mpr ⟨hm.succ_le 1, hm.le_castSucc 1⟩⟩
  · intro p hp
    obtain ⟨hp₀, hp₁⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp₀ hp₁
    refine mem_interlacingFinset.mpr (interlaces_iff.mpr fun i => ?_)
    fin_cases i
    · exact ⟨hp₀.2, hp₀.1⟩
    · exact ⟨hp₁.2, hp₁.1⟩
  · intro m _
    ext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro m _
    exact card_topRow_two_eq_toNat_sub_add_one m

/-- **The `GL 3` acceptance example.**  The top row `(2, 1, 0)` carries exactly `8` Gelfand-Tsetlin
patterns, one for each choice of an interlacing middle row `(a, b)` with `2 ≥ a ≥ 1`, `1 ≥ b ≥ 0`
and a bottom entry between them: the four middle rows `(1, 0)`, `(1, 1)`, `(2, 0)`, `(2, 1)` admit
`2`, `1`, `3`, `2` bottom entries.  This is the dimension of the `8`-dimensional irreducible
representation of `GL 3` of highest weight `(2, 1, 0)`, the adjoint representation of `SL 3`. -/
theorem card_topRow_three_two_one_zero :
    Nat.card {P : GTPattern 3 // P.topRow = ![2, 1, 0]} = 8 := by
  rw [card_topRow_three]
  decide

/-- **The rational `GL 3` acceptance example.**  The top row `(1, 0, -1)` is the determinant twist
of `(2, 1, 0)` by `-1`, and it carries the same `8` patterns — now with negative entries in some
rows, which the sign-free interlacing of `TauCeti.GTPattern` admits.  A nonnegativity constraint
on the row-final entries would wrongly exclude them. -/
theorem card_topRow_three_one_zero_neg_one :
    Nat.card {P : GTPattern 3 // P.topRow = ![1, 0, -1]} = 8 := by
  rw [card_topRow_three]
  decide

end GTPattern

end TauCeti
