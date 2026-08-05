/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
public import Mathlib.Combinatorics.Young.SemistandardTableau

/-!
# Gelfand-Tsetlin patterns are semistandard Young tableaux

A Gelfand-Tsetlin pattern whose top row is a shape `μ` records a chain of shapes

```text
∅ = ν⁰ ⊆ ν¹ ⊆ ⋯ ⊆ νⁿ = μ,
```

row `j` being the row-length sequence of `νʲ`; consecutive shapes differ by a horizontal strip
because consecutive rows interlace.  Such a chain is the same thing as a semistandard Young
tableau of shape `μ` with entries in `{0, …, n - 1}`: the cells carrying the entry `j` are
exactly those of `νʲ⁺¹` and not of `νʲ`.  This file builds that bijection.

Both directions are counting maps, and both rest on the same principle: a downward closed
predicate on `ℕ` cuts an initial segment out of `Finset.range N`, so membership in the segment is
decided by comparison with its cardinality.  Concretely, the tableau attached to a pattern `P`
has

```text
T i c = #{j < n | λᵢ,ⱼ₊₁ ≤ c},
```

the index of the first row of `P` whose `i`-th entry runs past `c`, and the pattern attached to a
tableau `T` has `λᵢ,ⱼ` the number of cells `(i, c)` of `μ` with `T i c < j`, that is, the length
of row `i` of the shape filled by the entries below `j`.  The interlacing inequalities and the
semistandardness conditions are exchanged by these two formulas, and the two maps are mutually
inverse.

Nonnegativity of the entries is not assumed on `TauCeti.GTPattern`, which admits the
determinant-twisted patterns; it is a *consequence* of the top row being a shape, since every
entry dominates a top-row entry (`TauCeti.GTPattern.entry_nonneg`).  Only in this polynomial
regime is there a tableau to speak of.

## Main definitions

* `TauCeti.GTPattern.tableauEntry` and `TauCeti.GTPattern.toTableau`: the tableau entry `T i c`
  read off a pattern, and the semistandard Young tableau it assembles.
* `TauCeti.SemistandardYoungTableau.patternEntry` and
  `TauCeti.SemistandardYoungTableau.toGTPattern`: the pattern read off a tableau.
* `TauCeti.gtPatternEquivSSYT`: **the bijection**, between the patterns with `n` rows and top row
  the shape `μ` and the semistandard Young tableaux of shape `μ` with entries below `n`.

## Main results

* `TauCeti.GTPattern.entry_nonneg`: a pattern with a nonnegative top row has nonnegative entries.
* `TauCeti.GTPattern.lt_tableauEntry_iff` and
  `TauCeti.SemistandardYoungTableau.lt_card_filter_rowLen_iff`: the two counting maps are decided
  by the pattern entries, respectively by the tableau entries.  Everything else is read off these
  two comparisons.
* `TauCeti.SemistandardYoungTableau.row_le_entry`: an entry of a semistandard tableau is at least
  its row index, which is why the pattern read off a tableau vanishes off the triangle `i < j`.
* `TauCeti.finite_ssyt_lt` and `TauCeti.card_gtPattern_topRow_eq_card_ssyt`: there are finitely
  many semistandard tableaux of a fixed shape with bounded entries, and they are as many as the
  patterns with the corresponding top row.

## Implementation notes

The roadmap states the bijection with the bound `∀ i j, T i j < n` on the tableau side.  That
form fails in exactly one case: for `n = 0` and `μ = ⊥` there is one (empty) pattern but no
tableau at all, because the bound also constrains the entries off `μ`, which vanish.  The bound
is therefore imposed on the cells of `μ`, where it is the intended condition; whenever `μ` is
nonempty the two readings agree, since a nonempty shape forces `n ≠ 0`.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 6, "the Gelfand-Tsetlin pattern ↔ semistandard tableau bijection", which pins the name
  `gtPatternEquivSSYT`.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

namespace TauCeti

open Finset

variable {n : ℕ} {μ : YoungDiagram}

/-! ### Initial segments cut out by a downward closed predicate -/

/-- A predicate that is downward closed below `N` keeps an initial segment of `Finset.range N`.
This is the plumbing behind both counting maps of this file, each of which filters a range by a
downward closed condition. -/
private theorem filter_range_eq_range_card :
    ∀ {N : ℕ} {p : ℕ → Prop} [DecidablePred p],
      (∀ ⦃x y : ℕ⦄, y ≤ x → x < N → p x → p y) →
      {y ∈ range N | p y} = range #{y ∈ range N | p y} := by
  intro N
  induction N with
  | zero => intro p _ _; simp
  | succ N ih =>
    intro p _ hp
    by_cases hN : p N
    · have h : {y ∈ range (N + 1) | p y} = range (N + 1) :=
        filter_true_of_mem fun y hy =>
          hp (Nat.lt_succ_iff.mp (mem_range.mp hy)) (Nat.lt_succ_self N) hN
      rw [h, card_range]
    · have h : {y ∈ range (N + 1) | p y} = {y ∈ range N | p y} := by
        rw [range_add_one, filter_insert, if_neg hN]
      rw [h]
      exact ih fun x y hxy hx => hp hxy (hx.trans (Nat.lt_succ_self N))

/-- Membership below the count, for a predicate that is downward closed below `N`. -/
private theorem lt_card_filter_range_iff {N : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y : ℕ⦄, y ≤ x → x < N → p x → p y) {x : ℕ} :
    x < #{y ∈ range N | p y} ↔ x < N ∧ p x := by
  rw [← mem_range, ← filter_range_eq_range_card hp, mem_filter, mem_range]

/-! ### Entries of a semistandard Young tableau -/

namespace SemistandardYoungTableau

/-- **Entries dominate their row index**: in a semistandard Young tableau the entry in row `i` is
at least `i`, because the `i` cells above it in its column carry strictly smaller entries. -/
theorem row_le_entry (T : SemistandardYoungTableau μ) :
    ∀ {i c : ℕ}, (i, c) ∈ μ → i ≤ T i c := by
  intro i
  induction i with
  | zero => intro c _; exact Nat.zero_le _
  | succ k ih =>
    intro c hc
    exact Nat.succ_le_of_lt
      ((ih (μ.up_left_mem (Nat.le_succ k) le_rfl hc)).trans_lt
        (T.col_strict (Nat.lt_succ_self k) hc))

end SemistandardYoungTableau

/-! ### Nonnegativity and monotonicity of pattern entries -/

namespace GTPattern

/-- **A pattern with a nonnegative top row has nonnegative entries**: every informative entry
dominates a top-row entry, and the remaining ones vanish.  This is what confines a pattern whose
top row is a shape to the polynomial regime, where it names a tableau. -/
theorem entry_nonneg (P : GTPattern n) (h : ∀ i : Fin n, 0 ≤ P.topRow i) (i j : ℕ) :
    0 ≤ P i j := by
  rcases Nat.lt_or_ge n j with hj | hj
  · exact (P.entry_eq_zero_of_lt hj).ge
  · rcases Nat.lt_or_ge i j with hij | hij
    · exact (h _).trans (P.topRow_le_entry hij hj)
    · exact (P.entry_eq_zero_of_le hij).ge

/-- Entries of a nonnegative pattern increase weakly with the row index, across the uninformative
cells `j ≤ i` as well as the informative ones. -/
theorem entry_le_entry_of_le' (P : GTPattern n) (hnn : ∀ i j, 0 ≤ P i j) {i j j' : ℕ}
    (hj : j ≤ j') (hj' : j' ≤ n) : P i j ≤ P i j' := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exact P.entry_le_entry_of_le hij hj hj'
  · rw [P.entry_eq_zero_of_le hij]
    exact hnn i j'

/-- The second interlacing inequality `λᵢ₊₁,ⱼ₊₁ ≤ λᵢ,ⱼ`, extended to the uninformative cells,
where both sides vanish. -/
theorem entry_succ_succ_le_entry' (P : GTPattern n) {i j : ℕ} (hj : j < n) :
    P (i + 1) (j + 1) ≤ P i j := by
  rcases Nat.lt_or_ge i j with hij | hij
  · exact P.entry_succ_succ_le_entry hij hj
  · rw [P.entry_eq_zero_of_le hij, P.entry_eq_zero_of_le (Nat.succ_le_succ hij)]

end GTPattern

/-! ### Patterns whose top row is a shape -/

/-- A cell of a shape with at most `n` rows has row index below `n`. -/
theorem row_lt_of_mem_of_colLen_le (hμ : μ.colLen 0 ≤ n) {i c : ℕ} (h : (i, c) ∈ μ) : i < n :=
  (YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le c) h)).trans_le hμ

namespace GTPattern

/-- A pattern whose top row is the shape `μ` has nonnegative entries. -/
theorem entry_nonneg_of_topRow (P : GTPattern n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i j : ℕ) : 0 ≤ P i j :=
  P.entry_nonneg (fun k => by rw [hP k]; exact Int.natCast_nonneg _) i j

/-- The top row of a pattern whose top row is the shape `μ` is the row-length sequence of `μ` at
*every* index: past `n` both sides vanish, because `μ` has at most `n` rows. -/
theorem entry_top_eq (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i : ℕ) : P i n = (μ.rowLen i : ℤ) := by
  rcases Nat.lt_or_ge i n with hi | hi
  · simpa using hP ⟨i, hi⟩
  · have hnot : (i, 0) ∉ μ := fun h => absurd (row_lt_of_mem_of_colLen_le hμ h) (by omega)
    have hz : μ.rowLen i = 0 := by
      by_contra h
      exact hnot (YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))
    rw [P.entry_eq_zero_of_le hi, hz, Nat.cast_zero]

/-! ### From a pattern to a tableau -/

/-- The `(i, c)` entry of the tableau attached to a Gelfand-Tsetlin pattern: the number of rows
`j` of the pattern whose `i`-th entry is at most `c`.  Equivalently, the least `v` with
`c < λᵢ,ᵥ₊₁`, that is, the index of the first shape in the chain recorded by the pattern that
contains the cell `(i, c)`. -/
@[expose] def tableauEntry (P : GTPattern n) (i c : ℕ) : ℕ :=
  #{j ∈ range n | P i (j + 1) ≤ (c : ℤ)}

/-- **The tableau entry, read off the pattern**: `j < T i c` exactly when the `i`-th entry of row
`j + 1` is at most `c`.  The rows of a nonnegative pattern increase weakly with the row index, so
the condition is downward closed in `j` and the count is an initial segment. -/
theorem lt_tableauEntry_iff (P : GTPattern n) (hnn : ∀ i j, 0 ≤ P i j) {i c j : ℕ} :
    j < P.tableauEntry i c ↔ j < n ∧ P i (j + 1) ≤ (c : ℤ) :=
  lt_card_filter_range_iff fun _ _ hxy hx hpx =>
    (P.entry_le_entry_of_le' hnn (by omega) (by omega)).trans hpx

/-- Tableau entries are bounded by the number of rows of the pattern: a cell strictly inside the
top row is reached before the last shape of the chain. -/
theorem tableauEntry_lt (P : GTPattern n) (hnn : ∀ i j, 0 ≤ P i j) {i c : ℕ}
    (hn : 0 < n) (hc : (c : ℤ) < P i n) : P.tableauEntry i c < n := by
  by_contra h
  obtain ⟨-, hle⟩ := (P.lt_tableauEntry_iff hnn (i := i) (c := c) (j := n - 1)).mp (by omega)
  rw [Nat.sub_add_cancel hn] at hle
  omega

/-- Tableau entries increase weakly along a row. -/
theorem tableauEntry_mono (P : GTPattern n) (i : ℕ) {c c' : ℕ} (h : c ≤ c') :
    P.tableauEntry i c ≤ P.tableauEntry i c' := by
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_range] at hj ⊢
  exact ⟨hj.1, hj.2.trans (by exact_mod_cast h)⟩

/-- Tableau entries increase strictly down a column, one step: the count `m` for row `i` is beaten
by the count for row `i + 1`, because the second interlacing inequality carries each of the `m`
rows witnessing the bound for row `i` one step up, while row `1` supplies a further witness. -/
theorem tableauEntry_lt_tableauEntry_succ (P : GTPattern n) (hnn : ∀ i j, 0 ≤ P i j) {i c : ℕ}
    (hlt : P.tableauEntry i c < n) :
    P.tableauEntry i c < P.tableauEntry (i + 1) c := by
  refine (P.lt_tableauEntry_iff hnn).mpr ⟨hlt, ?_⟩
  rcases Nat.eq_zero_or_pos (P.tableauEntry i c) with h0 | hpos
  · rw [h0, P.entry_eq_zero_of_le (show 0 + 1 ≤ i + 1 by omega)]
    exact Int.natCast_nonneg c
  · obtain ⟨k, hk⟩ : ∃ k, P.tableauEntry i c = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨-, hle⟩ := (P.lt_tableauEntry_iff hnn (i := i) (c := c) (j := k)).mp (by omega)
    rw [hk]
    exact (P.entry_succ_succ_le_entry' (show k + 1 < n by omega)).trans hle

/-- Tableau entries increase strictly down a column. -/
theorem tableauEntry_lt_tableauEntry (P : GTPattern n) (hnn : ∀ i j, 0 ≤ P i j) {c : ℕ} :
    ∀ {i₁ i₂ : ℕ}, i₁ < i₂ → (∀ i ≤ i₂, P.tableauEntry i c < n) →
      P.tableauEntry i₁ c < P.tableauEntry i₂ c := by
  intro i₁ i₂ h
  induction i₂, h using Nat.le_induction with
  | base => exact fun hlt => P.tableauEntry_lt_tableauEntry_succ hnn (hlt i₁ (by omega))
  | succ k _ ih =>
    exact fun hlt => (ih fun i hi => hlt i (by omega)).trans
      (P.tableauEntry_lt_tableauEntry_succ hnn (hlt k (by omega)))

/-- **The semistandard Young tableau of a Gelfand-Tsetlin pattern** whose top row is the shape
`μ`: the cell `(i, c)` carries the index of the first shape in the chain that contains it. -/
@[expose] def toTableau (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) : SemistandardYoungTableau μ where
  entry i c := if (i, c) ∈ μ then P.tableauEntry i c else 0
  row_weak' {i c₁ c₂} hc hcell := by
    rw [if_pos (μ.up_left_mem le_rfl hc.le hcell), if_pos hcell]
    exact P.tableauEntry_mono i hc.le
  col_strict' {i₁ i₂ c} hi hcell := by
    rw [if_pos (μ.up_left_mem hi.le le_rfl hcell), if_pos hcell]
    refine P.tableauEntry_lt_tableauEntry (P.entry_nonneg_of_topRow hP) hi fun i hi' => ?_
    have hcell' : (i, c) ∈ μ := μ.up_left_mem hi' le_rfl hcell
    refine P.tableauEntry_lt (P.entry_nonneg_of_topRow hP)
      (by have := row_lt_of_mem_of_colLen_le hμ hcell'; omega) ?_
    rw [P.entry_top_eq hμ hP]
    exact_mod_cast YoungDiagram.mem_iff_lt_rowLen.mp hcell'
  zeros' h := if_neg h

/-- The tableau of a pattern, unfolded: off `μ` the entry vanishes, and on `μ` it is the count
`TauCeti.GTPattern.tableauEntry`. -/
theorem toTableau_apply (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i c : ℕ) :
    P.toTableau hμ hP i c = if (i, c) ∈ μ then P.tableauEntry i c else 0 :=
  rfl

/-- On a cell of `μ` the tableau of a pattern is the count `TauCeti.GTPattern.tableauEntry`. -/
theorem toTableau_apply_of_mem (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {i c : ℕ} (h : (i, c) ∈ μ) :
    P.toTableau hμ hP i c = P.tableauEntry i c := by
  rw [toTableau_apply, if_pos h]

/-- The tableau of a pattern with `n` rows has entries below `n` on the cells of its shape. -/
theorem toTableau_lt (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {i c : ℕ} (h : (i, c) ∈ μ) :
    P.toTableau hμ hP i c < n := by
  rw [P.toTableau_apply_of_mem hμ hP h]
  refine P.tableauEntry_lt (P.entry_nonneg_of_topRow hP)
    (by have := row_lt_of_mem_of_colLen_le hμ h; omega) ?_
  rw [P.entry_top_eq hμ hP]
  exact_mod_cast YoungDiagram.mem_iff_lt_rowLen.mp h

/-- The defining comparison for the tableau of a pattern: the entry at a cell of `μ` is below `j`
exactly when the `i`-th entry of row `j` of the pattern runs past `c`. -/
theorem toTableau_lt_iff (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {i c j : ℕ} (hj : j ≤ n)
    (hc : (i, c) ∈ μ) : P.toTableau hμ hP i c < j ↔ (c : ℤ) < P i j := by
  rw [P.toTableau_apply_of_mem hμ hP hc]
  cases j with
  | zero => simp [P.entry_eq_zero_of_le (Nat.zero_le i)]
  | succ k =>
    rw [Nat.lt_succ_iff, ← Nat.not_lt, P.lt_tableauEntry_iff (P.entry_nonneg_of_topRow hP)]
    simp only [show k < n by omega, true_and, not_le]

end GTPattern

/-! ### From a tableau to a pattern -/

namespace SemistandardYoungTableau

/-- The `(i, j)` entry of the pattern attached to a semistandard Young tableau: the number of
cells of row `i` of `μ` whose entry is below `j`, that is, the length of row `i` of the shape
filled by the entries `< j`. -/
@[expose] def patternEntry (T : SemistandardYoungTableau μ) (n i j : ℕ) : ℤ :=
  if n < j then 0 else (#{c ∈ range (μ.rowLen i) | T i c < j} : ℤ)

/-- **The pattern entry, read off the tableau**: `c` is counted in row `j` of the `i`-th row
exactly when `(i, c)` is a cell of `μ` carrying an entry below `j`.  The rows of a tableau
increase weakly, so the condition is downward closed in `c`. -/
theorem lt_card_filter_rowLen_iff (T : SemistandardYoungTableau μ) {i j c : ℕ} :
    c < #{c' ∈ range (μ.rowLen i) | T i c' < j} ↔ c < μ.rowLen i ∧ T i c < j :=
  lt_card_filter_range_iff fun _ _ hxy hx hpx =>
    (T.row_weak_of_le hxy (YoungDiagram.mem_iff_lt_rowLen.mpr hx)).trans_lt hpx

/-- **The Gelfand-Tsetlin pattern of a semistandard Young tableau**, with `n` rows: row `j` is
the row-length sequence of the shape filled by the entries `< j`.  No bound on the entries is
needed to build the pattern; a bound is what makes its top row the whole of `μ`
(`TauCeti.SemistandardYoungTableau.topRow_toGTPattern`). -/
@[expose] def toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) : GTPattern n where
  entry := patternEntry T n
  zeros' {i j} h := by
    simp only [patternEntry]
    rcases h with h | h
    · rw [if_pos h]
    · by_cases hj : n < j
      · rw [if_pos hj]
      · rw [if_neg hj]
        have hempty : {c ∈ range (μ.rowLen i) | T i c < j} = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro c hc
          rw [mem_filter, mem_range] at hc
          have := row_le_entry T (YoungDiagram.mem_iff_lt_rowLen.mpr hc.1)
          omega
        rw [hempty, card_empty, Nat.cast_zero]
  interlacing' {i j} _ hj := by
    simp only [patternEntry]
    refine ⟨?_, ?_⟩
    · rw [if_neg (show ¬ n < j by omega), if_neg (show ¬ n < j + 1 by omega), Nat.cast_le]
      refine card_le_card fun c hc => ?_
      simp only [mem_filter, mem_range] at hc ⊢
      omega
    · rw [if_neg (show ¬ n < j by omega), if_neg (show ¬ n < j + 1 by omega), Nat.cast_le]
      refine card_le_card fun c hc => ?_
      simp only [mem_filter, mem_range] at hc ⊢
      have hcell : (i + 1, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hc.1
      have hup : (i, c) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
      have := T.col_strict (show i < i + 1 by omega) hcell
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp hup, by omega⟩

/-- The pattern of a tableau, unfolded. -/
theorem toGTPattern_apply (T : SemistandardYoungTableau μ) (n i j : ℕ) :
    toGTPattern T n i j = patternEntry T n i j :=
  rfl

/-- The top row of the pattern of a tableau of shape `μ` is the row-length sequence of `μ`: every
entry lies below `n`, so the last shape of the chain is `μ` itself. -/
theorem topRow_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ)
    (hT : ∀ i c : ℕ, (i, c) ∈ μ → T i c < n) (i : Fin n) :
    (toGTPattern T n).topRow i = (μ.rowLen i : ℤ) := by
  have hfil : {c ∈ range (μ.rowLen (i : ℕ)) | T (i : ℕ) c < n} = range (μ.rowLen (i : ℕ)) :=
    filter_true_of_mem fun c hc =>
      hT _ _ (YoungDiagram.mem_iff_lt_rowLen.mpr (mem_range.mp hc))
  rw [GTPattern.topRow_apply, toGTPattern_apply]
  simp only [patternEntry]
  rw [if_neg (lt_irrefl n), hfil, card_range]

/-- The defining comparison for the pattern of a tableau: the `i`-th entry of row `j + 1` is at
most `c` exactly when the cell `(i, c)` carries an entry above `j`. -/
theorem toGTPattern_succ_le_iff (T : SemistandardYoungTableau μ) (n : ℕ) {i c j : ℕ}
    (hj : j < n) (hc : (i, c) ∈ μ) :
    toGTPattern T n i (j + 1) ≤ (c : ℤ) ↔ j < T i c := by
  have hcr : c < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hc
  rw [toGTPattern_apply]
  simp only [patternEntry]
  rw [if_neg (show ¬ n < j + 1 by omega), Nat.cast_le, ← Nat.not_lt,
    lt_card_filter_rowLen_iff T]
  omega

end SemistandardYoungTableau

/-! ### The bijection -/

/-- **Gelfand-Tsetlin patterns are semistandard Young tableaux.**  For a shape `μ` with at most
`n` rows, the patterns with `n` rows and top row `μ` correspond to the semistandard Young tableaux
of shape `μ` whose entries lie in `{0, …, n - 1}`: row `j` of the pattern is the row-length
sequence of the shape filled by the entries below `j`, and the cell `(i, c)` of the tableau
carries the index of the first row of the pattern that runs past `c`.

Together with the count of the patterns with a given top row, this is the tableau reading of the
Gelfand-Tsetlin basis of an irreducible polynomial representation of `GL n`. -/
def gtPatternEquivSSYT (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)} ≃
      {T : SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n} where
  toFun P := ⟨P.1.toTableau hμ P.2, fun _ _ h => P.1.toTableau_lt hμ P.2 h⟩
  invFun T := ⟨SemistandardYoungTableau.toGTPattern T.1 n,
    SemistandardYoungTableau.topRow_toGTPattern T.1 n T.2⟩
  left_inv := by
    rintro ⟨P, hP⟩
    have hnn := P.entry_nonneg_of_topRow hP
    refine Subtype.ext (GTPattern.ext fun i j => ?_)
    rw [SemistandardYoungTableau.toGTPattern_apply]
    simp only [SemistandardYoungTableau.patternEntry]
    by_cases hjn : n < j
    · rw [if_pos hjn, P.entry_eq_zero_of_lt hjn]
    · rw [if_neg hjn]
      have hj : j ≤ n := by omega
      have hle : P i j ≤ (μ.rowLen i : ℤ) := by
        rw [← P.entry_top_eq hμ hP]
        exact P.entry_le_entry_of_le' hnn hj le_rfl
      have hset : {c ∈ range (μ.rowLen i) | P.toTableau hμ hP i c < j}
          = range (P i j).toNat := by
        ext c
        simp only [mem_filter, mem_range]
        constructor
        · rintro ⟨hc, hlt⟩
          have := (P.toTableau_lt_iff hμ hP hj (YoungDiagram.mem_iff_lt_rowLen.mpr hc)).mp hlt
          omega
        · intro hc
          have hcr : c < μ.rowLen i := by omega
          exact ⟨hcr, (P.toTableau_lt_iff hμ hP hj
            (YoungDiagram.mem_iff_lt_rowLen.mpr hcr)).mpr (by omega)⟩
      rw [hset, card_range, Int.toNat_of_nonneg (hnn i j)]
  right_inv := by
    rintro ⟨T, hT⟩
    refine Subtype.ext (SemistandardYoungTableau.ext fun i c => ?_)
    by_cases hc : (i, c) ∈ μ
    · rw [GTPattern.toTableau_apply, if_pos hc]
      simp only [GTPattern.tableauEntry]
      have hset : {j ∈ range n | SemistandardYoungTableau.toGTPattern T n i (j + 1) ≤ (c : ℤ)}
          = range (T i c) := by
        ext j
        simp only [mem_filter, mem_range]
        constructor
        · rintro ⟨hjn, hle⟩
          exact (SemistandardYoungTableau.toGTPattern_succ_le_iff T n hjn hc).mp hle
        · intro hj
          have hjn : j < n := hj.trans (hT i c hc)
          exact ⟨hjn, (SemistandardYoungTableau.toGTPattern_succ_le_iff T n hjn hc).mpr hj⟩
      rw [hset, card_range]
    · rw [GTPattern.toTableau_apply, if_neg hc, T.zeros hc]

/-- **Bounded semistandard tableaux of a fixed shape are finitely many**, transported along the
bijection from the finiteness of the patterns with a given top row
(`TauCeti.GTPattern.finite_topRow_eq`).  Mathlib's `SemistandardYoungTableau μ` allows unbounded
entries and is infinite for a nonempty `μ`, so the bound is what makes the count finite. -/
theorem finite_ssyt_lt (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    Finite {T : SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n} := by
  have : Finite {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)} :=
    Finite.of_equiv {P : GTPattern n // P.topRow = fun i : Fin n => (μ.rowLen (i : ℕ) : ℤ)}
      (Equiv.subtypeEquivRight fun _ => funext_iff)
  exact Finite.of_equiv _ (gtPatternEquivSSYT n μ hμ)

/-- **The pattern count is the tableau count**: the patterns with top row the shape `μ` are as
many as the semistandard Young tableaux of shape `μ` with entries below `n`.  This is the form in
which the bijection feeds the Gelfand-Tsetlin dimension count. -/
theorem card_gtPattern_topRow_eq_card_ssyt (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    Nat.card {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)}
      = Nat.card {T : SemistandardYoungTableau μ // ∀ i c : ℕ, (i, c) ∈ μ → T i c < n} :=
  Nat.card_congr (gtPatternEquivSSYT n μ hμ)

end TauCeti
