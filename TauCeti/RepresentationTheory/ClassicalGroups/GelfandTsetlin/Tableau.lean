/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Kostka
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
public import Mathlib.Data.Fintype.Fin

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

the number of rows of `P` that do *not* yet reach past `c`: for a cell `(i, c)` of `μ` this is one
less than the number of the first shape of the chain that contains it, so that the cells carrying
the entry `j` are exactly those of `νʲ⁺¹` and not of `νʲ`.  The pattern attached to a tableau `T`
has `λᵢ,ⱼ` the number of cells `(i, c)` of `μ` with `T i c < j`, that is, the length of row `i` of
the shape filled by the entries below `j`.  The interlacing inequalities and the semistandardness
conditions are exchanged by these two formulas, and the two maps are mutually inverse.

Nonnegativity of the entries is not assumed on `TauCeti.GTPattern`, which admits the
determinant-twisted patterns; it is a *consequence* of the top row being a shape, since every
entry dominates a top-row entry (`TauCeti.GTPattern.entry_nonneg`).  Only in this polynomial
regime is there a tableau to speak of.

## Main definitions

* `TauCeti.GTPattern.tableauEntry` and `TauCeti.GTPattern.toTableau`: the tableau entry `T i c`
  read off a pattern, and the semistandard Young tableau it assembles.
* `SemistandardYoungTableau.patternEntry` and
  `SemistandardYoungTableau.toGTPattern`: the pattern read off a tableau.
* `TauCeti.gtPatternEquivSSYT`: **the bijection**, between the patterns with `n` rows and top row
  the shape `μ` and the semistandard Young tableaux of shape `μ` with entries below `n`, that is,
  `TauCeti.BoundedSSYT n μ`.

## Main results

* `TauCeti.GTPattern.lt_tableauEntry_iff` and
  `SemistandardYoungTableau.lt_card_filter_rowLen_iff`: the two counting maps are decided
  by the pattern entries, respectively by the tableau entries.  Everything else is read off these
  two comparisons.
* `TauCeti.card_gtPattern_topRow_eq_card_ssyt`: the patterns with a given top row are as many as
  the semistandard tableaux of the corresponding shape with bounded entries, both counts being
  finite by `TauCeti.GTPattern.finite_topRow_eq` and `TauCeti.finite_boundedSSYT`.

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

open Finset

namespace TauCeti

variable {n : ℕ} {μ : YoungDiagram}

/-! ### Initial segments cut out by a downward closed predicate -/

/-- Membership below the count, for a predicate that is downward closed below `N`: such a
predicate keeps an initial segment of `Finset.range N`, so a number is counted exactly when it
lies below `N` and satisfies the predicate.  This is the plumbing behind both counting maps of
this file, each of which filters a range by a downward closed condition; it is
`Fin.lt_card_filter_univ_iff_apply_of_imp` transported along `Finset.image_fin_univ`. -/
private theorem lt_card_filter_range_iff {N : ℕ} {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ ⦃x y : ℕ⦄, y ≤ x → x < N → p x → p y) {x : ℕ} :
    x < #{y ∈ range N | p y} ↔ x < N ∧ p x := by
  have hcard : #{y ∈ range N | p y} = #{i : Fin N | p i} := by
    rw [← Finset.image_fin_univ, filter_image, card_image_of_injective _ Fin.val_injective]
  rcases Nat.lt_or_ge x N with hx | hx
  · have h : x < #{i : Fin N | p i} ↔ p x :=
      Fin.lt_card_filter_univ_iff_apply_of_imp (j := (⟨x, hx⟩ : Fin N)) (fun i => p i)
        fun i _ hji hi => hp hji i.2 hi
    rw [hcard, h, and_iff_right hx]
  · have hle : #{y ∈ range N | p y} ≤ N := (card_filter_le _ _).trans_eq (card_range N)
    exact iff_of_false (by omega) fun h => absurd h.1 (by omega)

/-! ### Patterns whose top row is a shape -/

namespace GTPattern

/-- The top row of a pattern whose top row is the shape `μ` is the row-length sequence of `μ` at
*every* index: past `n` both sides vanish, because `μ` has at most `n` rows. -/
theorem entry_top_eq (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i : ℕ) : P i n = (μ.rowLen i : ℤ) := by
  rcases Nat.lt_or_ge i n with hi | hi
  · simpa using hP ⟨i, hi⟩
  · rw [P.entry_eq_zero_of_le hi, YoungDiagram.rowLen_eq_zero_of_colLen_le (hμ.trans hi),
      Nat.cast_zero]

/-! ### From a pattern to a tableau -/

/-- The `(i, c)` entry of the tableau attached to a Gelfand-Tsetlin pattern: the number of rows
`j < n` of the pattern whose `i`-th entry is at most `c`.  The counted rows form an initial
segment, so *when some row `v < n` has `c < λᵢ,ᵥ₊₁`* the count is the least such `v`: the cell
`(i, c)` first appears in the shape `νᵛ⁺¹` of the chain recorded by the pattern, one step further
along the chain than the value `v` carried by the cell.  When no row does, every row is counted
and the entry is `n`. -/
def tableauEntry (P : GTPattern n) (i c : ℕ) : ℕ :=
  #{j ∈ range n | P i (j + 1) ≤ (c : ℤ)}

/-- The tableau entry of a pattern, unfolded: the count of the rows `j < n` whose `i`-th entry is
at most `c`.  The body of `TauCeti.GTPattern.tableauEntry` is not exposed, so this is how the
count is reached. -/
@[simp]
theorem tableauEntry_def (P : GTPattern n) (i c : ℕ) :
    P.tableauEntry i c = #{j ∈ range n | P i (j + 1) ≤ (c : ℤ)} :=
  (rfl)

/-- **The tableau entry, read off the pattern**: `j < T i c` exactly when `j < n` and the `i`-th
entry of row `j + 1` is at most `c`.  The `i`-th entries of a pattern increase weakly with the row
index on the informative cells and vanish on the rest, where the bound holds anyway since `c` is a
natural number, so the condition is downward closed in `j` and the count is an initial segment. -/
theorem lt_tableauEntry_iff (P : GTPattern n) {i c j : ℕ} :
    j < P.tableauEntry i c ↔ j < n ∧ P i (j + 1) ≤ (c : ℤ) :=
  lt_card_filter_range_iff fun x y hxy hx hpx => by
    rcases Nat.lt_or_ge i (y + 1) with hi | hi
    · exact (P.entry_le_entry_of_le hi (by omega) (by omega)).trans hpx
    · rw [P.entry_eq_zero_of_le hi]
      exact Int.natCast_nonneg c

/-- Tableau entries are bounded by the number of rows of the pattern: a cell strictly inside the
top row is reached before the last shape of the chain. -/
theorem tableauEntry_lt (P : GTPattern n) {i c : ℕ} (hc : (c : ℤ) < P i n) :
    P.tableauEntry i c < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [P.entry_eq_zero_of_le (Nat.zero_le i)] at hc
    omega
  · by_contra h
    obtain ⟨-, hle⟩ := (P.lt_tableauEntry_iff (i := i) (c := c) (j := n - 1)).mp (by omega)
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
theorem tableauEntry_lt_tableauEntry_succ (P : GTPattern n) {i c : ℕ}
    (hlt : P.tableauEntry i c < n) :
    P.tableauEntry i c < P.tableauEntry (i + 1) c := by
  refine P.lt_tableauEntry_iff.mpr ⟨hlt, ?_⟩
  rcases Nat.eq_zero_or_pos (P.tableauEntry i c) with h0 | hpos
  · rw [h0, zero_add, P.entry_eq_zero_of_le (Nat.le_add_left 1 i)]
    exact Int.natCast_nonneg c
  · obtain ⟨k, hk⟩ : ∃ k, P.tableauEntry i c = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    obtain ⟨-, hle⟩ := (P.lt_tableauEntry_iff (i := i) (c := c) (j := k)).mp (by omega)
    have hkn : k + 1 < n := by omega
    rw [hk]
    exact (P.entry_succ_succ_le_entry hkn).trans hle

/-- Tableau entries increase strictly down a column.  Only the rows `i₁ ≤ i < i₂` that the chain of
one-step comparisons passes through need to be bounded. -/
theorem tableauEntry_lt_tableauEntry (P : GTPattern n) {c : ℕ} :
    ∀ {i₁ i₂ : ℕ}, i₁ < i₂ → (∀ i, i₁ ≤ i → i < i₂ → P.tableauEntry i c < n) →
      P.tableauEntry i₁ c < P.tableauEntry i₂ c := by
  intro i₁ i₂ h
  induction i₂, h using Nat.le_induction with
  | base => exact fun hlt => P.tableauEntry_lt_tableauEntry_succ (hlt i₁ le_rfl (by omega))
  | succ k _ ih =>
    exact fun hlt => (ih fun i hi hi' => hlt i hi (by omega)).trans
      (P.tableauEntry_lt_tableauEntry_succ (hlt k (by omega) (by omega)))

/-- **The semistandard Young tableau of a Gelfand-Tsetlin pattern** whose top row is the shape
`μ`: the cell `(i, c)` carries the entry `j` for which `νʲ⁺¹` is the first shape in the chain that
contains it, one less than the number of that shape. -/
def toTableau (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) : SemistandardYoungTableau μ where
  entry i c := if (i, c) ∈ μ then P.tableauEntry i c else 0
  row_weak' {i c₁ c₂} hc hcell := by
    rw [ite_eq_left (μ.up_left_mem le_rfl hc.le hcell), ite_eq_left hcell]
    exact P.tableauEntry_mono i hc.le
  col_strict' {i₁ i₂ c} hi hcell := by
    rw [ite_eq_left (μ.up_left_mem hi.le le_rfl hcell), ite_eq_left hcell]
    refine P.tableauEntry_lt_tableauEntry hi fun i _ hi' => ?_
    have hcell' : (i, c) ∈ μ := μ.up_left_mem hi'.le le_rfl hcell
    refine P.tableauEntry_lt ?_
    rw [P.entry_top_eq hμ hP]
    exact_mod_cast YoungDiagram.mem_iff_lt_rowLen.mp hcell'
  zeros' h := ite_eq_right h

/-- The tableau of a pattern, unfolded: off `μ` the entry vanishes, and on `μ` it is the count
`TauCeti.GTPattern.tableauEntry`. -/
@[simp]
theorem toTableau_apply (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i c : ℕ) :
    P.toTableau hμ hP i c = if (i, c) ∈ μ then P.tableauEntry i c else 0 :=
  (rfl)

/-- On a cell of `μ` the tableau of a pattern is the count `TauCeti.GTPattern.tableauEntry`. -/
theorem toTableau_apply_of_mem (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {i c : ℕ} (h : (i, c) ∈ μ) :
    P.toTableau hμ hP i c = P.tableauEntry i c := by
  rw [toTableau_apply, ite_eq_left h]

/-- The tableau of a pattern with `n` rows has entries below `n` on the cells of its shape. -/
theorem toTableau_lt (P : GTPattern n) (hμ : μ.colLen 0 ≤ n)
    (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) {i c : ℕ} (h : (i, c) ∈ μ) :
    P.toTableau hμ hP i c < n := by
  rw [P.toTableau_apply_of_mem hμ hP h]
  refine P.tableauEntry_lt ?_
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
    have hkn : k < n := by omega
    rw [Nat.lt_succ_iff, ← Nat.not_lt, P.lt_tableauEntry_iff]
    simp only [hkn, true_and, not_le]

end GTPattern

/-! ### From a tableau to a pattern -/

end TauCeti

namespace SemistandardYoungTableau

variable {n : ℕ} {μ : YoungDiagram}

/-- The `(i, j)` entry of the pattern attached to a semistandard Young tableau, as a pattern with
`n` rows: for `j ≤ n` it is the number of cells of row `i` of `μ` whose entry is below `j`, that
is, the length of row `i` of the shape filled by the entries `< j`.  Past the top row, `n < j`,
the entry is forced to `0`, as a pattern with `n` rows carries no data there. -/
def patternEntry (T : SemistandardYoungTableau μ) (n i j : ℕ) : ℤ :=
  if n < j then 0 else (#{c ∈ range (μ.rowLen i) | T i c < j} : ℤ)

/-- The pattern entry of a tableau, unfolded: `0` past the top row, and otherwise the count of the
cells of row `i` of `μ` carrying an entry below `j`.  The body of
`SemistandardYoungTableau.patternEntry` is not exposed, so this is how the count is
reached. -/
@[simp]
theorem patternEntry_def (T : SemistandardYoungTableau μ) (n i j : ℕ) :
    patternEntry T n i j = if n < j then 0 else (#{c ∈ range (μ.rowLen i) | T i c < j} : ℤ) :=
  (rfl)

/-- **The pattern entry, read off the tableau**: `c` is counted in row `j` of the `i`-th row
exactly when `(i, c)` is a cell of `μ` carrying an entry below `j`.  The rows of a tableau
increase weakly, so the condition is downward closed in `c`. -/
@[simp]
theorem lt_card_filter_rowLen_iff (T : SemistandardYoungTableau μ) {i j c : ℕ} :
    c < #{c' ∈ range (μ.rowLen i) | T i c' < j} ↔ c < μ.rowLen i ∧ T i c < j :=
  TauCeti.lt_card_filter_range_iff fun _ _ hxy hx hpx =>
    (T.row_weak_of_le hxy (YoungDiagram.mem_iff_lt_rowLen.mpr hx)).trans_lt hpx

/-- **The Gelfand-Tsetlin pattern of a semistandard Young tableau**, with `n` rows: row `j` is
the row-length sequence of the shape filled by the entries `< j`.  No bound on the entries is
needed to build the pattern; a bound is what makes its top row the whole of `μ`
(`SemistandardYoungTableau.topRow_toGTPattern`). -/
def toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ) : TauCeti.GTPattern n where
  entry := patternEntry T n
  zeros' {i j} h := by
    simp only [patternEntry_def]
    rcases h with h | h
    · rw [ite_eq_left h]
    · by_cases hj : n < j
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj]
        have hempty : {c ∈ range (μ.rowLen i) | T i c < j} = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro c hc
          rw [mem_filter, mem_range] at hc
          have := le_entry T (YoungDiagram.mem_iff_lt_rowLen.mpr hc.1)
          omega
        rw [hempty, card_empty, Nat.cast_zero]
  interlacing' {i j} _ hj := by
    have hnj : ¬ n < j := by omega
    have hnj' : ¬ n < j + 1 := by omega
    simp only [patternEntry_def]
    refine ⟨?_, ?_⟩
    · rw [ite_eq_right hnj, ite_eq_right hnj', Nat.cast_le]
      refine card_le_card fun c hc => ?_
      simp only [mem_filter, mem_range] at hc ⊢
      omega
    · rw [ite_eq_right hnj, ite_eq_right hnj', Nat.cast_le]
      refine card_le_card fun c hc => ?_
      simp only [mem_filter, mem_range] at hc ⊢
      have hcell : (i + 1, c) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hc.1
      have hup : (i, c) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
      have hii : i < i + 1 := Nat.lt_succ_self i
      have := T.col_strict hii hcell
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp hup, by omega⟩

/-- The pattern of a tableau, unfolded. -/
@[simp]
theorem toGTPattern_apply (T : SemistandardYoungTableau μ) (n i j : ℕ) :
    toGTPattern T n i j = patternEntry T n i j :=
  (rfl)

/-- The top row of the pattern of a tableau of shape `μ` is the row-length sequence of `μ`: every
entry lies below `n`, so the last shape of the chain is `μ` itself. -/
theorem topRow_toGTPattern (T : SemistandardYoungTableau μ) (n : ℕ)
    (hT : ∀ i c : ℕ, (i, c) ∈ μ → T i c < n) (i : Fin n) :
    (toGTPattern T n).topRow i = (μ.rowLen i : ℤ) := by
  have hfil : {c ∈ range (μ.rowLen (i : ℕ)) | T (i : ℕ) c < n} = range (μ.rowLen (i : ℕ)) :=
    filter_true_of_mem fun c hc =>
      hT _ _ (YoungDiagram.mem_iff_lt_rowLen.mpr (mem_range.mp hc))
  rw [TauCeti.GTPattern.topRow_apply, toGTPattern_apply]
  simp only [patternEntry_def]
  rw [ite_eq_right (lt_irrefl n), hfil, card_range]

/-- The defining comparison for the pattern of a tableau: the `i`-th entry of row `j + 1` is at
most `c` exactly when the cell `(i, c)` carries an entry above `j`. -/
theorem toGTPattern_succ_le_iff (T : SemistandardYoungTableau μ) (n : ℕ) {i c j : ℕ}
    (hj : j < n) (hc : (i, c) ∈ μ) :
    toGTPattern T n i (j + 1) ≤ (c : ℤ) ↔ j < T i c := by
  have hcr : c < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hnj : ¬ n < j + 1 := by omega
  rw [toGTPattern_apply]
  simp only [patternEntry_def]
  rw [ite_eq_right hnj, Nat.cast_le, ← Nat.not_lt, lt_card_filter_rowLen_iff T]
  omega

end SemistandardYoungTableau

namespace TauCeti

/-! ### The bijection -/

/-- **Reading a pattern off the tableau it names returns the pattern.** -/
private theorem toGTPattern_toTableau_apply (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (P : GTPattern n) (hP : ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)) (i j : ℕ) :
    SemistandardYoungTableau.toGTPattern (P.toTableau hμ hP) n i j = P i j := by
  have hnn := P.entry_nonneg fun k => by rw [hP k]; exact Int.natCast_nonneg _
  rw [SemistandardYoungTableau.toGTPattern_apply]
  simp only [SemistandardYoungTableau.patternEntry_def]
  by_cases hjn : n < j
  · rw [ite_eq_left hjn, P.entry_eq_zero_of_lt hjn]
  · rw [ite_eq_right hjn]
    have hj : j ≤ n := by omega
    have hle : P i j ≤ (μ.rowLen i : ℤ) := by
      rw [← P.entry_top_eq hμ hP]
      exact P.entry_le_entry_of_nonneg_of_le (hnn i n) hj le_rfl
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

/-- **Naming the pattern read off a bounded tableau returns the tableau.** -/
private theorem toTableau_toGTPattern_apply (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : SemistandardYoungTableau μ) (hT : ∀ i c : ℕ, (i, c) ∈ μ → T i c < n) (i c : ℕ) :
    (SemistandardYoungTableau.toGTPattern T n).toTableau hμ
        (SemistandardYoungTableau.topRow_toGTPattern T n hT) i c = T i c := by
  by_cases hc : (i, c) ∈ μ
  · rw [GTPattern.toTableau_apply, ite_eq_left hc]
    simp only [GTPattern.tableauEntry_def]
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
  · rw [GTPattern.toTableau_apply, ite_eq_right hc, T.zeros hc]

/-- **Gelfand-Tsetlin patterns are semistandard Young tableaux.**  For a shape `μ` with at most
`n` rows, the patterns with `n` rows and top row `μ` correspond to the semistandard Young tableaux
of shape `μ` whose entries lie in `{0, …, n - 1}`: row `j` of the pattern is the row-length
sequence of the shape filled by the entries below `j`, and the cell `(i, c)` of the tableau
carries the number of rows of the pattern whose `i`-th entry does not yet run past `c`, one less
than the index of the first row that does.

Together with the count of the patterns with a given top row, this is the tableau reading of the
Gelfand-Tsetlin basis of an irreducible polynomial representation of `GL n`. -/
def gtPatternEquivSSYT (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)} ≃ BoundedSSYT n μ where
  toFun P := ⟨P.1.toTableau hμ P.2, fun _ _ h => P.1.toTableau_lt hμ P.2 h⟩
  invFun T := ⟨SemistandardYoungTableau.toGTPattern T.1 n,
    SemistandardYoungTableau.topRow_toGTPattern T.1 n T.2⟩
  left_inv P :=
    Subtype.ext (GTPattern.ext fun i j => toGTPattern_toTableau_apply n μ hμ P.1 P.2 i j)
  right_inv T :=
    Subtype.ext (SemistandardYoungTableau.ext fun i c =>
      toTableau_toGTPattern_apply n μ hμ T.1 T.2 i c)

/-- The bijection sends a pattern to the tableau `TauCeti.GTPattern.toTableau` it names. -/
@[simp]
theorem gtPatternEquivSSYT_apply_coe (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (P : {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)}) :
    (gtPatternEquivSSYT n μ hμ P).1 = P.1.toTableau hμ P.2 :=
  (rfl)

/-- The inverse bijection sends a tableau to the pattern
`SemistandardYoungTableau.toGTPattern` it names. -/
@[simp]
theorem gtPatternEquivSSYT_symm_apply_coe (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : BoundedSSYT n μ) :
    ((gtPatternEquivSSYT n μ hμ).symm T).1 = SemistandardYoungTableau.toGTPattern T.1 n :=
  (rfl)

/-- **The pattern count is the tableau count**: the patterns with top row the shape `μ` are as
many as the semistandard Young tableaux of shape `μ` with entries below `n`.  This is the form in
which the bijection feeds the Gelfand-Tsetlin dimension count. -/
theorem card_gtPattern_topRow_eq_card_ssyt (n : ℕ) (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    Nat.card {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.rowLen i : ℤ)}
      = Nat.card (BoundedSSYT n μ) :=
  Nat.card_congr (gtPatternEquivSSYT n μ hμ)

end TauCeti
