/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
public import Mathlib.Data.Int.Interval
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Gelfand-Tsetlin patterns

A **Gelfand-Tsetlin pattern** for `GL n` is a triangular array of integers

```text
                    λ₀,ₙ  λ₁,ₙ  …  λₙ₋₁,ₙ
                       λ₀,ₙ₋₁  …  λₙ₋₂,ₙ₋₁
                              ⋱
                            λ₀,₁
```

whose row `j` has `j` entries `λ₀,ⱼ ≥ ⋯ ≥ λⱼ₋₁,ⱼ`, and in which consecutive rows **interlace**:
`λᵢ,ⱼ₊₁ ≥ λᵢ,ⱼ ≥ λᵢ₊₁,ⱼ₊₁`.  Iterating the multiplicity-free branching `GL n ↓ GL (n-1)` down the
chain `GL 1 ⊂ ⋯ ⊂ GL n` refines an irreducible representation into lines indexed by exactly these
patterns, so they are the combinatorial index of the Gelfand-Tsetlin basis, and their count is the
dimension of the representation.  Nothing of the kind is in Mathlib (whose `Gelfand*` files are
about C\*-algebras), so this file builds the combinatorial object and its recursion.

Entries are **integers** and no positivity is imposed, so the determinant-twisted (rational)
patterns are included alongside the polynomial ones.  The polynomial patterns are those all of
whose entries are nonnegative; since every entry is at least the last entry of the top row, that
is decided by the last entry of the top row alone, and not by the signs of the other entries,
which a dominant top row is free to mix.  The interlacing inequalities are imposed only on the
interior cells `i < j < n`, where all three entries involved are informative; weak decrease along
each row is then a consequence (`TauCeti.GTPattern.entry_anti`), not an extra hypothesis.

The engine of the file is `TauCeti.GTPattern.truncateEquiv`: deleting the top row identifies the
patterns with `n + 1` rows and top row `l` with the patterns with `n` rows whose own top row
interlaces `l`.  This is the combinatorial shadow of the `GL (n+1) ↓ GL n` branching rule, and it
is what makes the patterns with a prescribed top row finite and countable.  Read off at `n = 1` it
gives a unique pattern for each top row, and at `n = 2` the count `(λ₀ - λ₁ + 1).toNat`, which for
a dominant top row `λ₁ ≤ λ₀` is `λ₀ - λ₁ + 1`, the dimension of the irreducible representation of
`GL 2` of highest weight `(λ₀, λ₁)`.

## Main definitions

* `TauCeti.GTPattern n`: Gelfand-Tsetlin patterns with `n` rows.
* `TauCeti.GTPattern.topRow` and `TauCeti.GTPattern.topWeight`: the longest row, the highest weight
  the pattern refines, the second packaged as a `TauCeti.DominantWeight`.
* `TauCeti.Interlaces`: the betweenness relation `lᵢ ≥ mᵢ ≥ lᵢ₊₁` between two integer sequences.
* `TauCeti.GTPattern.truncate` and `TauCeti.GTPattern.extend`: deleting and prepending a top row.

## Main results

* `TauCeti.GTPattern.entry_anti` and `TauCeti.GTPattern.topRow_antitone`: rows are weakly
  decreasing, so the top row is a dominant weight.
* `TauCeti.GTPattern.entry_nonneg`: a pattern with a nonnegative top row has nonnegative entries,
  so the polynomial patterns are cut out by the top row alone.
* `TauCeti.Interlaces.antitone`: an interlacing sequence is weakly decreasing, so a sequence
  interlacing a dominant weight is dominant.
* `TauCeti.GTPattern.truncateEquiv`: patterns with `n + 1` rows and top row `l` correspond to
  patterns with `n` rows whose top row interlaces `l`.
* `TauCeti.GTPattern.finite_topRow_eq`: only finitely many patterns share a top row.
* `TauCeti.GTPattern.card_topRow_one_eq_one` and
  `TauCeti.GTPattern.card_topRow_two_eq_toNat_sub_add_one`: the counts for `n = 1` and `n = 2`,
  the latter being `(λ₀ - λ₁ + 1).toNat`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "Gelfand-Tsetlin patterns", which pins the name `GTPattern` and the convention that the
  interlacing constraint ranges only over interior cells.
* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Dokl. Akad. Nauk SSSR **71** (1950), 825-828.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

namespace TauCeti

/-- A **Gelfand-Tsetlin pattern** for `GL n`: a triangular array of integers whose row `j` has the
`j` entries `λ₀,ⱼ ≥ ⋯ ≥ λⱼ₋₁,ⱼ`, subject to the interlacing inequalities
`λᵢ,ⱼ₊₁ ≥ λᵢ,ⱼ ≥ λᵢ₊₁,ⱼ₊₁`.

As with Mathlib's `SemistandardYoungTableau`, the array is carried by an unrestricted function
`ℕ → ℕ → ℤ` required to vanish off the triangle `i < j ≤ n`, so that two patterns agreeing on the
informative cells are equal.  Entries may be negative: the determinant-twisted patterns are
included. -/
structure GTPattern (n : ℕ) where
  /-- `entry i j` is the `i`-th entry of row `j`; the informative cells are `i < j ≤ n`. -/
  entry : ℕ → ℕ → ℤ
  /-- Cells outside the triangle `i < j ≤ n` carry no data. -/
  zeros' : ∀ {i j : ℕ}, n < j ∨ j ≤ i → entry i j = 0
  /-- The interlacing inequalities `λᵢ,ⱼ₊₁ ≥ λᵢ,ⱼ ≥ λᵢ₊₁,ⱼ₊₁`, imposed on the interior cells
  `i < j < n` where all three entries are informative. -/
  interlacing' : ∀ {i j : ℕ}, i < j → j < n →
    entry i j ≤ entry i (j + 1) ∧ entry (i + 1) (j + 1) ≤ entry i j

namespace GTPattern

variable {n : ℕ}

instance instFunLike : FunLike (GTPattern n) ℕ (ℕ → ℤ) where
  coe := GTPattern.entry
  coe_injective P P' h := by cases P; cases P'; congr

@[simp]
theorem entry_eq_coe {P : GTPattern n} : P.entry = (P : ℕ → ℕ → ℤ) := rfl

@[ext]
theorem ext {P P' : GTPattern n} (h : ∀ i j, P i j = P' i j) : P = P' :=
  DFunLike.ext P P' fun _ => funext (h _)

theorem entry_eq_zero (P : GTPattern n) {i j : ℕ} (h : n < j ∨ j ≤ i) : P i j = 0 := P.zeros' h

/-- The `i`-th entry of row `j` vanishes once `j` outruns the number of rows. -/
@[simp]
theorem entry_eq_zero_of_lt (P : GTPattern n) {i j : ℕ} (h : n < j) : P i j = 0 :=
  P.entry_eq_zero (Or.inl h)

/-- The `i`-th entry of row `j` vanishes once `i` outruns the length of the row. -/
@[simp]
theorem entry_eq_zero_of_le (P : GTPattern n) {i j : ℕ} (h : j ≤ i) : P i j = 0 :=
  P.entry_eq_zero (Or.inr h)

/-- The first interlacing inequality `λᵢ,ⱼ ≤ λᵢ,ⱼ₊₁`. -/
theorem entry_le_entry_succ_row (P : GTPattern n) {i j : ℕ} (hij : i < j) (hj : j < n) :
    P i j ≤ P i (j + 1) := (P.interlacing' hij hj).1

/-- The second interlacing inequality `λᵢ₊₁,ⱼ₊₁ ≤ λᵢ,ⱼ`.  The interlacing constraint is imposed
only on the informative cells `i < j`, but the inequality needs no such restriction: off them both
sides vanish. -/
theorem entry_succ_succ_le_entry (P : GTPattern n) {i j : ℕ} (hj : j < n) :
    P (i + 1) (j + 1) ≤ P i j := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exact (P.interlacing' hij hj).2
  · rw [P.entry_eq_zero_of_le hij, P.entry_eq_zero_of_le (Nat.succ_le_succ hij)]

/-- Rows decrease weakly, in adjacent form. -/
theorem entry_succ_le_entry (P : GTPattern n) {i j : ℕ} (hij : i + 1 < j) (hj : j ≤ n) :
    P (i + 1) j ≤ P i j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact (P.entry_succ_succ_le_entry (by omega)).trans
    (P.entry_le_entry_succ_row (by omega) (by omega))

/-- Rows decrease weakly: `λᵢ,ⱼ ≥ λᵢ',ⱼ` for `i ≤ i' < j ≤ n`.  This is a consequence of the
interlacing inequalities, not a separate hypothesis on a pattern. -/
theorem entry_anti (P : GTPattern n) {i j : ℕ} (hj : j ≤ n) :
    ∀ {i' : ℕ}, i ≤ i' → i' < j → P i' j ≤ P i j := by
  intro i' h
  induction i', h using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ k _ ih => exact fun hkj => (P.entry_succ_le_entry hkj hj).trans (ih (by omega))

/-- Entries increase weakly with the row index: `λᵢ,ⱼ ≤ λᵢ,ⱼ'` for `i < j ≤ j' ≤ n`. -/
theorem entry_le_entry_of_le (P : GTPattern n) {i j : ℕ} (hij : i < j) :
    ∀ {j' : ℕ}, j ≤ j' → j' ≤ n → P i j ≤ P i j' := by
  intro j' hjj'
  induction j' with
  | zero => exact absurd hij (by omega)
  | succ k ih =>
    intro hk
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (P.entry_le_entry_succ_row (by omega) (by omega))
    · obtain rfl : j = k + 1 := by omega
      exact le_rfl

/-- Entries increase weakly with the row index across the uninformative cells `j ≤ i` as well,
provided the larger entry is nonnegative: `λᵢ,ⱼ ≤ λᵢ,ⱼ'` for `j ≤ j' ≤ n` and `0 ≤ λᵢ,ⱼ'`. -/
theorem entry_le_entry_of_nonneg_of_le (P : GTPattern n) {i j j' : ℕ} (hnn : 0 ≤ P i j')
    (hj : j ≤ j') (hj' : j' ≤ n) : P i j ≤ P i j' := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exact P.entry_le_entry_of_le hij hj hj'
  · rw [P.entry_eq_zero_of_le hij]
    exact hnn

/-- Increasing both indices of a cell by the same amount decreases it. -/
theorem entry_add_le (P : GTPattern n) {i j : ℕ} :
    ∀ {d : ℕ}, j + d ≤ n → P (i + d) (j + d) ≤ P i j := by
  intro d
  induction d with
  | zero => exact fun _ => le_rfl
  | succ e ih =>
    intro hj
    have h : P (i + e + 1) (j + e + 1) ≤ P (i + e) (j + e) :=
      P.entry_succ_succ_le_entry (by omega)
    exact h.trans (ih (by omega))

/-! ### The top row -/

/-- The **top row** `(λ₀,ₙ, …, λₙ₋₁,ₙ)` of a Gelfand-Tsetlin pattern: the highest weight it
refines. -/
def topRow (P : GTPattern n) : Fin n → ℤ := fun i => P i n

@[simp]
theorem topRow_apply (P : GTPattern n) (i : Fin n) : P.topRow i = P i n := (rfl)

/-- **The top row is weakly decreasing.**  Rows of a pattern decrease weakly (`entry_anti`), and
the top row is one of them, so it is a dominant weight of `GL n`; `TauCeti.GTPattern.topWeight`
packages it as one. -/
theorem topRow_antitone (P : GTPattern n) : Antitone P.topRow :=
  fun _ i' h => P.entry_anti le_rfl h i'.2

/-- The top row of a Gelfand-Tsetlin pattern, as a dominant weight of `GL n`. -/
def topWeight (P : GTPattern n) : DominantWeight n := ⟨P.topRow, P.topRow_antitone⟩

@[simp]
theorem topWeight_coe (P : GTPattern n) : (P.topWeight : Fin n → ℤ) = P.topRow := (rfl)

/-- Every entry is at most the top-row entry directly above it. -/
theorem entry_le_topRow (P : GTPattern n) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    P i j ≤ P.topRow ⟨i, hij.trans_le hj⟩ :=
  P.entry_le_entry_of_le hij hj le_rfl

/-- Every entry dominates the top-row entry reached from it by increasing both indices equally. -/
theorem topRow_le_entry (P : GTPattern n) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    P.topRow ⟨i + (n - j), by omega⟩ ≤ P i j := by
  have hjn : j + (n - j) = n := by omega
  have h := P.entry_add_le (i := i) (j := j) (d := n - j) (by omega)
  rw [hjn] at h
  simpa using h

/-- **A pattern with a nonnegative top row has nonnegative entries**: every informative entry
dominates a top-row entry, and the remaining ones vanish.  This is what confines a pattern whose
top row is a shape to the polynomial regime, where it names a semistandard Young tableau. -/
theorem entry_nonneg (P : GTPattern n) (h : ∀ i : Fin n, 0 ≤ P.topRow i) (i j : ℕ) :
    0 ≤ P i j := by
  rcases Nat.lt_or_ge n j with hj | hj
  · exact (P.entry_eq_zero_of_lt hj).ge
  · rcases Nat.lt_or_ge i j with hij | hij
    · exact (h _).trans (P.topRow_le_entry hij hj)
    · exact (P.entry_eq_zero_of_le hij).ge

/-- Every entry of a pattern lies between the last and the first entry of its top row. -/
theorem entry_mem_Icc (P : GTPattern n) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    P i j ∈ Set.Icc (P.topRow ⟨n - 1, by omega⟩) (P.topRow ⟨0, by omega⟩) := by
  have hlast : (⟨i + (n - j), by omega⟩ : Fin n) ≤ ⟨n - 1, by omega⟩ := by
    simp only [Fin.le_def]; omega
  have hfirst : (⟨0, by omega⟩ : Fin n) ≤ ⟨i, hij.trans_le hj⟩ := by
    simp only [Fin.le_def]; omega
  exact ⟨(P.topRow_antitone hlast).trans (P.topRow_le_entry hij hj),
    (P.entry_le_topRow hij hj).trans (P.topRow_antitone hfirst)⟩

/-- There is exactly one empty pattern. -/
instance : Unique (GTPattern 0) where
  default := ⟨fun _ _ => 0, fun _ => rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  uniq P := by ext i j; exact P.entry_eq_zero (by omega)

end GTPattern

/-! ### Interlacing -/

/-- `TauCeti.Interlaces l m` says that the integer sequence `m : Fin n → ℤ` **interlaces** the
longer sequence `l : Fin (n + 1) → ℤ`: `lᵢ ≥ mᵢ ≥ lᵢ₊₁` for every `i`.  This is the betweenness
condition relating consecutive rows of a Gelfand-Tsetlin pattern.

No dominance is assumed: `l` and `m` are arbitrary integer sequences and the relation is purely
combinatorial.  When `l` *is* dominant it acquires its representation-theoretic reading: every `m`
interlacing `l` is then dominant too (the two inequalities give `mᵢ₊₁ ≤ lᵢ₊₁ ≤ mᵢ`), and such `m`
are exactly the highest weights of the constituents of `V_l` restricted along
`GL n ↪ GL (n + 1)`. -/
def Interlaces {n : ℕ} (l : Fin (n + 1) → ℤ) (m : Fin n → ℤ) : Prop :=
  ∀ i : Fin n, m i ≤ l i.castSucc ∧ l i.succ ≤ m i

/-- Interlacing unfolded: the pair of inequalities at each index.  This is the introduction and
elimination rule for `TauCeti.Interlaces`, whose body is not exposed. -/
@[simp]
theorem interlaces_iff {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ} :
    Interlaces l m ↔ ∀ i : Fin n, m i ≤ l i.castSucc ∧ l i.succ ≤ m i :=
  Iff.rfl

/-- Half of the interlacing condition: `mᵢ ≤ lᵢ`. -/
theorem Interlaces.le_castSucc {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ}
    (h : Interlaces l m) (i : Fin n) : m i ≤ l i.castSucc := (h i).1

/-- The other half of the interlacing condition: `lᵢ₊₁ ≤ mᵢ`. -/
theorem Interlaces.succ_le {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ}
    (h : Interlaces l m) (i : Fin n) : l i.succ ≤ m i := (h i).2

/-- **An interlacing sequence is weakly decreasing.**  The two interlacing inequalities at
adjacent indices meet at the same entry of `l`, giving `mᵢ₊₁ ≤ lᵢ₊₁ ≤ mᵢ`; no assumption on `l` is
needed.  In particular a sequence interlacing a dominant weight is itself dominant, which is what
packages the output of `TauCeti.GTPattern.truncateEquiv` as a `TauCeti.DominantWeight`. -/
theorem Interlaces.antitone {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ} (h : Interlaces l m) :
    Antitone m := by
  cases n with
  | zero => exact fun i => i.elim0
  | succ _ =>
    exact Fin.antitone_iff_succ_le.mpr fun i =>
      (h.le_castSucc i.succ).trans (by simpa using h.succ_le i.castSucc)

namespace GTPattern

variable {n : ℕ}

/-! ### Deleting and prepending a top row -/

/-- Delete the top row of a pattern with `n + 1` rows. -/
def truncate (P : GTPattern (n + 1)) : GTPattern n where
  entry i j := if j ≤ n then P i j else 0
  zeros' := by
    intro i j h
    by_cases hj : j ≤ n
    · rw [ite_eq_left hj]; exact P.entry_eq_zero (by omega)
    · rw [ite_eq_right hj]
  interlacing' := by
    intro i j hij hj
    have h1 : j ≤ n := by omega
    have h2 : j + 1 ≤ n := by omega
    simp only [h1, h2, ite_true]
    exact P.interlacing' hij (by omega)

@[simp]
theorem truncate_apply (P : GTPattern (n + 1)) (i j : ℕ) :
    truncate P i j = if j ≤ n then P i j else 0 := (rfl)

/-- The top row of a truncated pattern is the row below the top of the original. -/
theorem topRow_truncate (P : GTPattern (n + 1)) (i : Fin n) : (truncate P).topRow i = P i n := by
  simp

/-- The row below the top of a pattern interlaces its top row: the pattern's own witness that
`TauCeti.GTPattern.truncate` lands where `TauCeti.GTPattern.extend` expects it. -/
theorem interlaces_topRow_truncate (P : GTPattern (n + 1)) :
    Interlaces P.topRow (truncate P).topRow :=
  interlaces_iff.mpr fun i =>
    ⟨by simpa using P.entry_le_entry_succ_row i.2 (by omega),
      by simpa using P.entry_succ_succ_le_entry (i := (i : ℕ)) (j := n) (by omega)⟩

/-- Prepend the row `l` on top of a pattern with `n` rows whose own top row it interlaces. -/
def extend (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow) :
    GTPattern (n + 1) where
  entry i j := if j = n + 1 then (if hi : i < n + 1 then l ⟨i, hi⟩ else 0) else Q i j
  zeros' := by
    intro i j hz
    by_cases hj : j = n + 1
    · have hi : ¬ i < n + 1 := by omega
      rw [ite_eq_left hj, dite_eq_right hi]
    · rw [ite_eq_right hj]
      exact Q.entry_eq_zero (by omega)
  interlacing' := by
    intro i j hij hj
    by_cases hjn : j = n
    · have hi : i < n := hjn ▸ hij
      have hne : ¬ (n = n + 1) := by omega
      have hi' : i < n + 1 := by omega
      have hi'' : i + 1 < n + 1 := by omega
      rw [hjn]
      exact ⟨by simp only [ite_eq_right hne, dite_eq_left hi']; exact h.le_castSucc ⟨i, hi⟩,
        by simp only [ite_eq_right hne, dite_eq_left hi'']; exact h.succ_le ⟨i, hi⟩⟩
    · have hne : ¬ (j = n + 1) := by omega
      have hne' : ¬ (j + 1 = n + 1) := by omega
      simp only [ite_eq_right hne, ite_eq_right hne']
      exact Q.interlacing' hij (by omega)

theorem extend_apply (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    (i j : ℕ) :
    extend Q l h i j = if j = n + 1 then (if hi : i < n + 1 then l ⟨i, hi⟩ else 0) else Q i j :=
  (rfl)

@[simp]
theorem extend_apply_of_ne (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    {i j : ℕ} (hj : j ≠ n + 1) : extend Q l h i j = Q i j := by
  rw [extend_apply, ite_eq_right hj]

@[simp]
theorem extend_apply_top (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    {i : ℕ} (hi : i < n + 1) : extend Q l h i (n + 1) = l ⟨i, hi⟩ := by
  rw [extend_apply, ite_eq_left rfl, dite_eq_left hi]

/-- Prepending a row leaves the cells past the end of the new row empty.  This is not `@[simp]`:
`entry_eq_zero_of_le` already rewrites it, being the general normal form for an out-of-row cell. -/
theorem extend_apply_top_of_le (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow)
    {i : ℕ} (hi : n + 1 ≤ i) : extend Q l h i (n + 1) = 0 := by
  rw [extend_apply, ite_eq_left rfl, dite_eq_right (by omega)]

@[simp]
theorem topRow_extend (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow) :
    (extend Q l h).topRow = l := by
  funext i
  rw [topRow_apply, extend_apply_top Q l h i.2]

@[simp]
theorem truncate_extend (Q : GTPattern n) (l : Fin (n + 1) → ℤ) (h : Interlaces l Q.topRow) :
    truncate (extend Q l h) = Q := by
  ext i j
  rw [truncate_apply]
  by_cases hj : j ≤ n
  · have hj' : j ≠ n + 1 := by omega
    rw [ite_eq_left hj, extend_apply_of_ne Q l h hj']
  · rw [ite_eq_right hj]
    exact (Q.entry_eq_zero_of_lt (by omega)).symm

@[simp]
theorem extend_truncate (P : GTPattern (n + 1)) :
    extend (truncate P) P.topRow (interlaces_topRow_truncate P) = P := by
  ext i j
  by_cases hj : j = n + 1
  · subst hj
    by_cases hi : i < n + 1
    · rw [extend_apply_top _ _ _ hi, topRow_apply]
    · rw [extend_apply_top_of_le _ _ _ (by omega)]
      exact (P.entry_eq_zero_of_le (by omega)).symm
  · rw [extend_apply_of_ne _ _ _ hj, truncate_apply]
    by_cases hjn : j ≤ n
    · rw [ite_eq_left hjn]
    · rw [ite_eq_right hjn]
      exact (P.entry_eq_zero_of_lt (by omega)).symm

/-- **Deleting the top row is a bijection.**  The Gelfand-Tsetlin patterns with `n + 1` rows and
top row `l` are exactly the patterns with `n` rows whose own top row interlaces `l`.

The statement holds for an arbitrary integer sequence `l`, where it is a bijection between two
combinatorial sets and nothing more (for a non-dominant `l` both sides are empty as soon as
`n ≥ 1`).  For a *dominant* `l` it is the combinatorial form of the multiplicity-free branching
`GL (n+1) ↓ GL n`: the constituents of the restriction of `V_l` are indexed by the interlacing
weights, which are again dominant, and a basis vector of `V_l` is a choice of interlacing weight
together with a basis vector of the corresponding constituent. -/
def truncateEquiv (l : Fin (n + 1) → ℤ) :
    {P : GTPattern (n + 1) // P.topRow = l} ≃ {Q : GTPattern n // Interlaces l Q.topRow} where
  toFun := fun ⟨P, hP⟩ => ⟨truncate P, hP ▸ interlaces_topRow_truncate P⟩
  invFun Q := ⟨extend Q.1 l Q.2, topRow_extend _ _ _⟩
  left_inv := by rintro ⟨P, rfl⟩; exact Subtype.ext (extend_truncate P)
  right_inv Q := Subtype.ext (truncate_extend _ _ _)

@[simp]
theorem truncateEquiv_apply_coe (l : Fin (n + 1) → ℤ)
    (P : {P : GTPattern (n + 1) // P.topRow = l}) :
    (truncateEquiv l P).1 = truncate P.1 :=
  (rfl)

@[simp]
theorem truncateEquiv_symm_apply_coe (l : Fin (n + 1) → ℤ)
    (Q : {Q : GTPattern n // Interlaces l Q.topRow}) :
    ((truncateEquiv l).symm Q).1 = extend Q.1 l Q.2 :=
  (rfl)

/-! ### Finitely many patterns share a top row -/

/-- **Only finitely many patterns share a top row.**  Every entry of a pattern is squeezed between
the last and the first entry of its top row (`TauCeti.GTPattern.entry_mem_Icc`), so the patterns
with a prescribed top row form a finite type. -/
instance finite_topRow_eq (l : Fin n → ℤ) : Finite {P : GTPattern n // P.topRow = l} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · infer_instance
  · set a : ℤ := min (l ⟨n - 1, by omega⟩) 0 with ha
    set b : ℤ := max (l ⟨0, hn⟩) 0 with hb
    have hmem : ∀ (P : {P : GTPattern n // P.topRow = l}) (i j : ℕ),
        P.1 i j ∈ Set.Icc a b := by
      rintro ⟨P, rfl⟩ i j
      by_cases hij : i < j ∧ j ≤ n
      · exact ⟨(min_le_left _ _).trans (P.entry_mem_Icc hij.1 hij.2).1,
          (P.entry_mem_Icc hij.1 hij.2).2.trans (le_max_left _ _)⟩
      · rw [P.entry_eq_zero (by omega)]
        exact ⟨min_le_right _ _, le_max_right _ _⟩
    refine Finite.of_injective
      (fun P => fun (i j : Fin (n + 1)) => (⟨P.1 i j, hmem P i j⟩ : Set.Icc a b)) ?_
    rintro ⟨P, _⟩ ⟨P', _⟩ hPP'
    refine Subtype.ext (GTPattern.ext fun i j => ?_)
    by_cases hi : i < n + 1
    · by_cases hj : j < n + 1
      · exact congrArg Subtype.val (congrFun (congrFun hPP' ⟨i, hi⟩) ⟨j, hj⟩)
      · rw [P.entry_eq_zero (by omega), P'.entry_eq_zero (by omega)]
    · rw [P.entry_eq_zero (by omega), P'.entry_eq_zero (by omega)]

/-! ### The counts in low rank -/

/-- A one-row pattern is nothing but its top row: for each `l` there is exactly one pattern with
top row `l`. -/
instance uniqueTopRowOne (l : Fin 1 → ℤ) : Unique {P : GTPattern 1 // P.topRow = l} := by
  haveI : Unique {Q : GTPattern 0 // Interlaces l Q.topRow} :=
    ⟨⟨⟨default, interlaces_iff.mpr fun i => i.elim0⟩⟩,
      fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  exact (truncateEquiv l).unique

/-- A Gelfand-Tsetlin pattern with a single row is its top row: there is exactly one pattern with
each prescribed top row.  This is the statement that the irreducible representations of `GL 1` are
one-dimensional. -/
theorem card_topRow_one_eq_one (l : Fin 1 → ℤ) : Nat.card {P : GTPattern 1 // P.topRow = l} = 1 :=
  Nat.card_unique

/-- Reading the top row is a bijection from the patterns with one row onto the integer sequences of
length one. -/
def equivOne : GTPattern 1 ≃ (Fin 1 → ℤ) where
  toFun := topRow
  invFun l := (default : {P : GTPattern 1 // P.topRow = l}).1
  left_inv P := congrArg Subtype.val
    (Subsingleton.elim (default : {X : GTPattern 1 // X.topRow = P.topRow}) ⟨P, rfl⟩)
  right_inv l := (default : {P : GTPattern 1 // P.topRow = l}).2

@[simp]
theorem equivOne_apply (P : GTPattern 1) : equivOne P = P.topRow := (rfl)

/-- **The count for `GL 2`.**  A Gelfand-Tsetlin pattern with two rows is its top row together with
a single integer `λ₀,₁` between `λ₁` and `λ₀`, so the patterns with top row `(λ₀, λ₁)` are counted
by `(λ₀ - λ₁ + 1).toNat`.  The truncation is not decoration: `l` is an arbitrary integer sequence,
and for `λ₀ < λ₁` there is no such pattern at all.  On a dominant top row, `λ₁ ≤ λ₀`, the count is
`λ₀ - λ₁ + 1`, the dimension of the irreducible representation of `GL 2` of highest weight
`(λ₀, λ₁)`. -/
theorem card_topRow_two_eq_toNat_sub_add_one (l : Fin 2 → ℤ) :
    Nat.card {P : GTPattern 2 // P.topRow = l} = (l 0 - l 1 + 1).toNat := by
  have e₂ : {Q : GTPattern 1 // Interlaces l Q.topRow} ≃ {m : Fin 1 → ℤ // Interlaces l m} :=
    Equiv.subtypeEquiv equivOne fun _ => Iff.rfl
  have e₃ : {m : Fin 1 → ℤ // Interlaces l m} ≃ Set.Icc (l 1) (l 0) :=
    { toFun := fun m => ⟨m.1 0, ⟨m.2.succ_le 0, m.2.le_castSucc 0⟩⟩
      invFun := fun x => ⟨fun _ => x.1, interlaces_iff.mpr fun i => by
        obtain rfl : i = 0 := Subsingleton.elim _ _
        exact ⟨x.2.2, x.2.1⟩⟩
      left_inv := fun m => by
        refine Subtype.ext (funext fun i => ?_)
        obtain rfl : i = 0 := Subsingleton.elim _ _
        rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr ((truncateEquiv l).trans (e₂.trans e₃)), Nat.card_eq_fintype_card,
    Fintype.card_Icc, Int.card_Icc]
  omega

end GTPattern

end TauCeti
