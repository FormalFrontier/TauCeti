/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.Diagram
public import TauCeti.Combinatorics.Young.Kostka

/-!
# The Bender-Knuth involutions

Fix a semistandard Young tableau `T` and a letter `v`.  The **Bender-Knuth involution** at `v`
rewrites the `v`s and `(v + 1)`s of `T` so as to exchange how often the two letters occur, leaving
every other letter untouched.  It is the combinatorial mechanism behind the symmetry of the Schur
polynomials, and this file builds it.

The construction here is *not* the usual row-by-row description ("the `v`s and `(v + 1)`s that are
not vertically paired form, in each row, a block of `a` copies of `v` followed by `b` copies of
`v + 1`; replace it by `b` copies of `v` and `a` copies of `v + 1`").  It is organized instead
around a single counting function, `SemistandardYoungTableau.rowCountLt T i x`, the number of
entries smaller than `x` in row `i`.  Rows increase weakly, so the entries of row `i` smaller than
`x` occupy exactly the columns below `rowCountLt T i x`, and this one function records the whole
row.  Writing `a i = rowCountLt T i v`, `n i = rowCountLt T i (v + 1)` and
`b i = rowCountLt T i (v + 2)`, the letters `v` and `v + 1` of row `i` occupy the columns of
`Finset.Ico (a i) (b i)`, split at `n i`.

A filling with the same entries outside those blocks is then the same thing as a choice of a new
splitting point `cut i` in each row, and `SemistandardYoungTableau.recut` builds it.  Two
inequalities per row beyond `a i ≤ cut i ≤ b i` are enough to make the result semistandard again —
this is `SemistandardYoungTableau.IsCut`, a sufficient condition — and together they place `cut i`
in the interval `[max (a i) (b (i + 1)), min (b i) (a (i - 1))]`, which contains `n i`.  The
Bender-Knuth involution recuts each row at the reflection of `n i` in that interval, and being a
reflection is what makes it an involution: the interval is unchanged by a recut, because its
endpoints depend only on `a` and `b`, which a recut does not move.

## Main definitions

* `SemistandardYoungTableau.rowCountLt`: the number of entries smaller than a given letter in a
  given row.
* `SemistandardYoungTableau.IsCut`: the condition on a family of splitting points that makes the
  recut filling semistandard.
* `SemistandardYoungTableau.recut`: the tableau obtained by splitting the `v`/`(v + 1)` block of
  each row at a prescribed column.
* `SemistandardYoungTableau.benderKnuth`: the Bender-Knuth involution at a letter `v`.

## Main results

* `SemistandardYoungTableau.benderKnuth_benderKnuth`: the Bender-Knuth involution is an involution.
* `SemistandardYoungTableau.content_benderKnuth`: it exchanges the multiplicities of `v` and
  `v + 1` and fixes every other one.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 7.
-/

public section

namespace SemistandardYoungTableau

variable {μ : YoungDiagram} {T : SemistandardYoungTableau μ} {v x : ℕ} {cut : ℕ → ℕ}

/-! ### Counting the entries of a row -/

/-- The number of entries smaller than `x` in row `i` of a tableau.  As rows increase weakly, these
entries occupy exactly the columns below this number — the content of
`SemistandardYoungTableau.lt_rowCountLt_iff` — so a single such counting function records the whole
row. -/
def rowCountLt (T : SemistandardYoungTableau μ) (i x : ℕ) : ℕ :=
  ((Finset.range (μ.rowLen i)).filter fun j => T i j < x).card

/-- The entries of a row smaller than `x` occupy an initial segment of columns, of length
`SemistandardYoungTableau.rowCountLt`. -/
theorem filter_lt_eq_range (T : SemistandardYoungTableau μ) (i x : ℕ) :
    ((Finset.range (μ.rowLen i)).filter fun j => T i j < x) = Finset.range (rowCountLt T i x) := by
  have hdown : ∀ j' j : ℕ, j' ≤ j →
      j ∈ (Finset.range (μ.rowLen i)).filter (fun j => T i j < x) →
      j' ∈ (Finset.range (μ.rowLen i)).filter (fun j => T i j < x) := by
    intro j' j hj' hj
    rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨lt_of_le_of_lt hj' hj.1,
      lt_of_le_of_lt (T.row_weak_of_le hj' (YoungDiagram.mem_iff_lt_rowLen.mpr hj.1)) hj.2⟩
  have hsub : ((Finset.range (μ.rowLen i)).filter fun j => T i j < x)
      ⊆ Finset.range (rowCountLt T i x) := by
    intro j hj
    refine Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self j) ?_)
    refine le_trans (le_of_eq (Finset.card_range (j + 1)).symm)
      (Finset.card_le_card fun k hk => ?_)
    exact hdown k j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hj
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_range _))

/-- The columns of a row carrying an entry smaller than `x` are exactly those below
`SemistandardYoungTableau.rowCountLt`. -/
theorem lt_rowCountLt_iff (T : SemistandardYoungTableau μ) {i j x : ℕ} (hj : j < μ.rowLen i) :
    j < rowCountLt T i x ↔ T i j < x := by
  have h := Finset.ext_iff.mp (filter_lt_eq_range T i x) j
  simpa only [Finset.mem_filter, Finset.mem_range, hj, true_and] using h.symm

/-- A row has at most as many entries smaller than `x` as it has cells. -/
theorem rowCountLt_le_rowLen (T : SemistandardYoungTableau μ) (i x : ℕ) :
    rowCountLt T i x ≤ μ.rowLen i := by
  simpa only [rowCountLt, Finset.card_range] using
    Finset.card_le_card (Finset.filter_subset (fun j => T i j < x) (Finset.range (μ.rowLen i)))

/-- Counting entries below a larger letter counts more of them. -/
theorem rowCountLt_mono (T : SemistandardYoungTableau μ) (i : ℕ) {x y : ℕ} (hxy : x ≤ y) :
    rowCountLt T i x ≤ rowCountLt T i y := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 hxy⟩

/-- **The column inequality**, in the form everything below rests on: entries increase strictly
down a column, so row `i + 1` has no more entries smaller than `x + 1` than row `i` has entries
smaller than `x`. -/
theorem rowCountLt_succ_le (T : SemistandardYoungTableau μ) (i x : ℕ) :
    rowCountLt T (i + 1) (x + 1) ≤ rowCountLt T i x := by
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
  have hcell : ((i + 1, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj.1
  exact ⟨lt_of_lt_of_le hj.1 (μ.rowLen_anti i (i + 1) (Nat.le_succ i)),
    lt_of_lt_of_le (T.col_strict (Nat.lt_succ_self i) hcell) (Nat.lt_succ_iff.mp hj.2)⟩

/-- A row past the height of the shape has no entries at all. -/
theorem rowCountLt_eq_zero_of_colLen_le (T : SemistandardYoungTableau μ) {i : ℕ}
    (hi : μ.colLen 0 ≤ i) (x : ℕ) : rowCountLt T i x = 0 :=
  Nat.le_zero.mp (YoungDiagram.rowLen_eq_zero_of_colLen_le hi ▸ T.rowCountLt_le_rowLen i x)

/-! ### The block of a letter and its successor -/

/-- The cells of `T` carrying the letter `v` or the letter `v + 1`: the ones a Bender-Knuth
involution at `v` may move. -/
def InBlock (T : SemistandardYoungTableau μ) (v i j : ℕ) : Prop :=
  (i, j) ∈ μ ∧ v ≤ T i j ∧ T i j ≤ v + 1

instance (T : SemistandardYoungTableau μ) (v i j : ℕ) : Decidable (T.InBlock v i j) :=
  inferInstanceAs (Decidable ((i, j) ∈ μ ∧ v ≤ T i j ∧ T i j ≤ v + 1))

/-- The block of a row is the interval of columns from `rowCountLt T i v` to
`rowCountLt T i (v + 2)`. -/
theorem inBlock_iff (T : SemistandardYoungTableau μ) {i j : ℕ} (v : ℕ)
    (hj : ((i, j) : ℕ × ℕ) ∈ μ) :
    T.InBlock v i j ↔ (rowCountLt T i v ≤ j ∧ j < rowCountLt T i (v + 2)) := by
  have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hj
  have h1 := T.lt_rowCountLt_iff (x := v) hlt
  have h2 := T.lt_rowCountLt_iff (x := v + 2) hlt
  rw [InBlock, and_iff_right hj]
  omega

/-- A cell outside the shape is outside the block. -/
theorem not_inBlock_of_notMem {T : SemistandardYoungTableau μ} {v i j : ℕ}
    (hj : ((i, j) : ℕ × ℕ) ∉ μ) : ¬ T.InBlock v i j := fun h => hj h.1

/-! ### Recutting a block -/

/-- **The recut condition**: a family of splitting points, one per row, produces a semistandard
filling — `SemistandardYoungTableau.recut` — as soon as each `cut i` lies inside the block of row
`i` and no vertically adjacent pair of a `v` above a `v + 1` is broken.  The last two clauses say
the latter: such a pair sits in the columns of
`Finset.Ico (rowCountLt T i v) (rowCountLt T (i + 1) (v + 2))`, so its `v` keeps its letter when
`cut i` is at least the right endpoint, and its `v + 1` keeps its letter when `cut (i + 1)` is at
most the left one.

This is a sufficient condition, not a necessary one: a row whose block is empty carries no letter
that a recut can move, so the recut filling ignores `cut i` there while the condition still pins it
down.  Every family of splitting points used here — the tableau's own, and the reflected ones of
`SemistandardYoungTableau.benderKnuth` — satisfies it. -/
structure IsCut (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ) : Prop where
  /-- The splitting point of a row is at least the start of its block. -/
  le_cut (i : ℕ) : rowCountLt T i v ≤ cut i
  /-- The splitting point of a row is at most the end of its block. -/
  cut_le (i : ℕ) : cut i ≤ rowCountLt T i (v + 2)
  /-- The `v` of a vertically adjacent pair keeps its letter. -/
  succ_le_cut (i : ℕ) : rowCountLt T (i + 1) (v + 2) ≤ cut i
  /-- The `v + 1` of a vertically adjacent pair keeps its letter. -/
  cut_succ_le (i : ℕ) : cut (i + 1) ≤ rowCountLt T i v

/-- The filling obtained from `T` by splitting the `v`/`(v + 1)` block of each row at a prescribed
column. -/
private def recutEntry (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ) (i j : ℕ) : ℕ :=
  if T.InBlock v i j then (if j < cut i then v else v + 1) else T i j

/-- Outside the block, a recut entry is the old entry. -/
private theorem recutEntry_of_not_inBlock (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ)
    {i j : ℕ} (h : ¬ T.InBlock v i j) : recutEntry T v cut i j = T i j :=
  ite_eq_right h

/-- Inside the block, a recut entry is `v` before the splitting point and `v + 1` after it. -/
private theorem recutEntry_of_inBlock (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ)
    {i j : ℕ} (h : T.InBlock v i j) :
    recutEntry T v cut i j = if j < cut i then v else v + 1 :=
  ite_eq_left h

/-- A recut entry is either the old entry or one of the two letters being exchanged. -/
private theorem recutEntry_eq_or (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ) (i j : ℕ) :
    recutEntry T v cut i j = T i j ∨ recutEntry T v cut i j = v
      ∨ recutEntry T v cut i j = v + 1 := by
  by_cases h : T.InBlock v i j
  · rw [recutEntry_of_inBlock T v cut h]
    by_cases hj : j < cut i
    · exact Or.inr (Or.inl (ite_eq_left hj))
    · exact Or.inr (Or.inr (ite_eq_right hj))
  · exact Or.inl (recutEntry_of_not_inBlock T v cut h)

/-- A recut entry lies in the block exactly when the old one did: a recut moves letters within
`{v, v + 1}` and moves nothing else. -/
private theorem inBlock_recutEntry_iff (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ)
    (i j : ℕ) :
    ((i, j) ∈ μ ∧ v ≤ recutEntry T v cut i j ∧ recutEntry T v cut i j ≤ v + 1)
      ↔ ((i, j) ∈ μ ∧ v ≤ T i j ∧ T i j ≤ v + 1) := by
  by_cases h : T.InBlock v i j
  · rw [recutEntry_of_inBlock T v cut h]
    refine iff_of_true ⟨h.1, ?_⟩ h
    split <;> omega
  · rw [recutEntry_of_not_inBlock T v cut h]

/-- Recutting does not break a column between adjacent rows. -/
private theorem recutEntry_lt_succ (hcut : IsCut T v cut) {i j : ℕ}
    (hcell : ((i + 1, j) : ℕ × ℕ) ∈ μ) :
    recutEntry T v cut i j < recutEntry T v cut (i + 1) j := by
  have hcell' : ((i, j) : ℕ × ℕ) ∈ μ := μ.up_left_mem (Nat.le_succ i) le_rfl hcell
  have hlt : T i j < T (i + 1) j := T.col_strict (Nat.lt_succ_self i) hcell
  by_cases h₁ : T.InBlock v i j <;> by_cases h₂ : T.InBlock v (i + 1) j
  · -- both cells lie in the block, so they carry `v` above `v + 1`
    have hb₁ := (T.inBlock_iff v hcell').mp h₁
    have hb₂ := (T.inBlock_iff v hcell).mp h₂
    rw [recutEntry_of_inBlock T v cut h₁, recutEntry_of_inBlock T v cut h₂,
      ite_eq_left (lt_of_lt_of_le hb₂.2 (hcut.succ_le_cut i)),
      ite_eq_right (Nat.not_lt.mpr (le_trans (hcut.cut_succ_le i) hb₁.1))]
    omega
  · rw [recutEntry_of_inBlock T v cut h₁, recutEntry_of_not_inBlock T v cut h₂]
    have hnot : ¬(v ≤ T (i + 1) j ∧ T (i + 1) j ≤ v + 1) := fun hb => h₂ ⟨hcell, hb⟩
    have := h₁.2
    split <;> omega
  · rw [recutEntry_of_not_inBlock T v cut h₁, recutEntry_of_inBlock T v cut h₂]
    have hnot : ¬(v ≤ T i j ∧ T i j ≤ v + 1) := fun hb => h₁ ⟨hcell', hb⟩
    have := h₂.2
    split <;> omega
  · rw [recutEntry_of_not_inBlock T v cut h₁, recutEntry_of_not_inBlock T v cut h₂]
    exact hlt

private theorem recutEntry_col_strict_aux (hcut : IsCut T v cut) (i j : ℕ) : ∀ d : ℕ,
    ((i + d + 1, j) : ℕ × ℕ) ∈ μ →
      recutEntry T v cut i j < recutEntry T v cut (i + d + 1) j := by
  intro d
  induction d with
  | zero => exact fun h => recutEntry_lt_succ hcut h
  | succ e ih =>
    intro h
    have h' : ((i + e + 1, j) : ℕ × ℕ) ∈ μ := μ.up_left_mem (by omega) le_rfl h
    exact lt_trans (ih h') (recutEntry_lt_succ hcut h)

/-- Recutting does not break a column. -/
private theorem recutEntry_col_strict (hcut : IsCut T v cut) {i₁ i₂ j : ℕ} (hi : i₁ < i₂)
    (hcell : ((i₂, j) : ℕ × ℕ) ∈ μ) :
    recutEntry T v cut i₁ j < recutEntry T v cut i₂ j := by
  obtain ⟨d, rfl⟩ : ∃ d, i₂ = i₁ + d + 1 := ⟨i₂ - i₁ - 1, by omega⟩
  exact recutEntry_col_strict_aux hcut i₁ j d hcell

/-- Recutting keeps rows weakly increasing.  No recut condition is needed: within a row the
letters `v` come before the letters `v + 1` wherever the block is split. -/
private theorem recutEntry_row_weak (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ)
    {i j₁ j₂ : ℕ} (hj : j₁ < j₂)
    (hcell : ((i, j₂) : ℕ × ℕ) ∈ μ) :
    recutEntry T v cut i j₁ ≤ recutEntry T v cut i j₂ := by
  have hcell₁ : ((i, j₁) : ℕ × ℕ) ∈ μ := μ.up_left_mem le_rfl hj.le hcell
  have hle : T i j₁ ≤ T i j₂ := T.row_weak hj hcell
  by_cases h₁ : T.InBlock v i j₁ <;> by_cases h₂ : T.InBlock v i j₂
  · rw [recutEntry_of_inBlock T v cut h₁, recutEntry_of_inBlock T v cut h₂]
    split <;> split <;> omega
  · rw [recutEntry_of_inBlock T v cut h₁, recutEntry_of_not_inBlock T v cut h₂]
    have hnot : ¬(v ≤ T i j₂ ∧ T i j₂ ≤ v + 1) := fun hb => h₂ ⟨hcell, hb⟩
    have := h₁.2
    split <;> omega
  · rw [recutEntry_of_not_inBlock T v cut h₁, recutEntry_of_inBlock T v cut h₂]
    have hnot : ¬(v ≤ T i j₁ ∧ T i j₁ ≤ v + 1) := fun hb => h₁ ⟨hcell₁, hb⟩
    have := h₂.2
    split <;> omega
  · rw [recutEntry_of_not_inBlock T v cut h₁, recutEntry_of_not_inBlock T v cut h₂]
    exact hle

/-- **The recut tableau**: the semistandard tableau agreeing with `T` outside the `v`/`(v + 1)`
blocks, whose blocks are split at the prescribed columns. -/
def recut (T : SemistandardYoungTableau μ) (v : ℕ) (cut : ℕ → ℕ) (hcut : IsCut T v cut) :
    SemistandardYoungTableau μ where
  entry := recutEntry T v cut
  row_weak' := recutEntry_row_weak T v cut
  col_strict' := recutEntry_col_strict hcut
  zeros' := fun hij => by
    rw [recutEntry_of_not_inBlock T v cut (not_inBlock_of_notMem hij), T.zeros hij]

/-- The entries of a recut tableau: inside the block of a row, `v` before the splitting point and
`v + 1` after it; everywhere else, the old entry. -/
@[simp]
theorem recut_apply (hcut : IsCut T v cut) (i j : ℕ) :
    recut T v cut hcut i j =
      if T.InBlock v i j then (if j < cut i then v else v + 1) else T i j := (rfl)

/-- Inside the block, the entry of a recut tableau is `v` before the splitting point and `v + 1`
after it. -/
theorem recut_apply_of_inBlock (hcut : IsCut T v cut) {i j : ℕ} (h : T.InBlock v i j) :
    recut T v cut hcut i j = if j < cut i then v else v + 1 :=
  (recut_apply hcut i j).trans (ite_eq_left h)

/-- Outside the block, the entry of a recut tableau is the old entry. -/
theorem recut_apply_of_not_inBlock (hcut : IsCut T v cut) {i j : ℕ} (h : ¬ T.InBlock v i j) :
    recut T v cut hcut i j = T i j :=
  (recut_apply hcut i j).trans (ite_eq_right h)

/-- A recut moves no letter into or out of the block, so the two tableaux have the same blocks. -/
theorem inBlock_recut_iff (hcut : IsCut T v cut) (i j : ℕ) :
    (recut T v cut hcut).InBlock v i j ↔ T.InBlock v i j :=
  inBlock_recutEntry_iff T v cut i j

/-! ### The row counts of a recut tableau -/

/-- Below the block, a recut changes no row count. -/
theorem rowCountLt_recut_of_le (hcut : IsCut T v cut) (i : ℕ) (hx : x ≤ v) :
    rowCountLt (recut T v cut hcut) i x = rowCountLt T i x := by
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  have hcell : ((i, j) : ℕ × ℕ) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj)
  by_cases h : T.InBlock v i j
  · rw [recut_apply_of_inBlock hcut h]
    have := h.2
    refine iff_of_false ?_ (by omega)
    split <;> omega
  · rw [recut_apply_of_not_inBlock hcut h]

/-- Above the block, a recut changes no row count. -/
theorem rowCountLt_recut_of_ge (hcut : IsCut T v cut) (i : ℕ) (hx : v + 2 ≤ x) :
    rowCountLt (recut T v cut hcut) i x = rowCountLt T i x := by
  refine congrArg Finset.card (Finset.filter_congr fun j hj => ?_)
  have hcell : ((i, j) : ℕ × ℕ) ∈ μ :=
    YoungDiagram.mem_iff_lt_rowLen.mpr (Finset.mem_range.mp hj)
  by_cases h : T.InBlock v i j
  · rw [recut_apply_of_inBlock hcut h]
    have := h.2
    refine iff_of_true ?_ (by omega)
    split <;> omega
  · rw [recut_apply_of_not_inBlock hcut h]

/-- **A recut is exactly a change of splitting point**: in the recut tableau, the block of row `i`
is split at `cut i`. -/
theorem rowCountLt_recut_succ (hcut : IsCut T v cut) (i : ℕ) :
    rowCountLt (recut T v cut hcut) i (v + 1) = cut i := by
  have hcl : cut i ≤ μ.rowLen i := le_trans (hcut.cut_le i) (T.rowCountLt_le_rowLen i (v + 2))
  have hfilter : ((Finset.range (μ.rowLen i)).filter
      fun j => recut T v cut hcut i j < v + 1) = Finset.range (cut i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hlt⟩
      have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
      by_cases h : T.InBlock v i j
      · rw [recut_apply_of_inBlock hcut h] at hlt
        by_contra hc
        rw [ite_eq_right (Nat.not_lt.mpr (Nat.not_lt.mp hc))] at hlt
        omega
      · rw [recut_apply_of_not_inBlock hcut h] at hlt
        have hnot : ¬(v ≤ T i j ∧ T i j ≤ v + 1) := fun hb => h ⟨hcell, hb⟩
        have hlow : j < rowCountLt T i v := (T.lt_rowCountLt_iff hj).mpr (by omega)
        exact lt_of_lt_of_le hlow (hcut.le_cut i)
    · intro hj
      have hjr : j < μ.rowLen i := lt_of_lt_of_le hj hcl
      have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hjr
      refine ⟨hjr, ?_⟩
      by_cases h : T.InBlock v i j
      · rw [recut_apply_of_inBlock hcut h, ite_eq_left hj]
        omega
      · rw [recut_apply_of_not_inBlock hcut h]
        have hnot : ¬(v ≤ T i j ∧ T i j ≤ v + 1) := fun hb => h ⟨hcell, hb⟩
        have hhigh : j < rowCountLt T i (v + 2) :=
          lt_of_lt_of_le hj (le_trans (hcut.cut_le i) le_rfl)
        rw [T.lt_rowCountLt_iff hjr] at hhigh
        omega
  rw [rowCountLt, hfilter, Finset.card_range]

/-- Recutting at the splitting points of `T` itself changes nothing. -/
theorem isCut_rowCountLt (T : SemistandardYoungTableau μ) (v : ℕ) :
    IsCut T v fun i => rowCountLt T i (v + 1) where
  le_cut i := T.rowCountLt_mono i (Nat.le_succ v)
  cut_le i := T.rowCountLt_mono i (Nat.le_succ (v + 1))
  succ_le_cut i := T.rowCountLt_succ_le i (v + 1)
  cut_succ_le i := T.rowCountLt_succ_le i v

@[simp]
theorem recut_rowCountLt (T : SemistandardYoungTableau μ) (v : ℕ) :
    recut T v (fun i => rowCountLt T i (v + 1)) (isCut_rowCountLt T v) = T := by
  ext i j
  by_cases h : T.InBlock v i j
  · rw [recut_apply_of_inBlock (isCut_rowCountLt T v) h]
    have hcell := h.1
    have hjr := YoungDiagram.mem_iff_lt_rowLen.mp hcell
    have hiff := T.lt_rowCountLt_iff (x := v + 1) hjr
    have := h.2
    split
    · omega
    · omega
  · exact recut_apply_of_not_inBlock (isCut_rowCountLt T v) h

/-- A recut condition for `T` is a recut condition for any recut of `T`: the constraints depend
only on the row counts below and above the block, which a recut leaves alone. -/
theorem IsCut.recut {cut' : ℕ → ℕ} (hcut : IsCut T v cut) (hcut' : IsCut T v cut') :
    IsCut (recut T v cut hcut) v cut' where
  le_cut i := by rw [rowCountLt_recut_of_le hcut i le_rfl]; exact hcut'.le_cut i
  cut_le i := by rw [rowCountLt_recut_of_ge hcut i le_rfl]; exact hcut'.cut_le i
  succ_le_cut i := by rw [rowCountLt_recut_of_ge hcut _ le_rfl]; exact hcut'.succ_le_cut i
  cut_succ_le i := by rw [rowCountLt_recut_of_le hcut i le_rfl]; exact hcut'.cut_succ_le i

/-- Recutting twice is recutting once. -/
theorem recut_recut {cut' : ℕ → ℕ} (hcut : IsCut T v cut) (hcut' : IsCut T v cut') :
    recut (recut T v cut hcut) v cut' (hcut.recut hcut') = recut T v cut' hcut' := by
  ext i j
  by_cases h : T.InBlock v i j
  · rw [recut_apply_of_inBlock (hcut.recut hcut') ((inBlock_recut_iff hcut i j).mpr h),
      recut_apply_of_inBlock hcut' h]
  · rw [recut_apply_of_not_inBlock (hcut.recut hcut')
      (fun hc => h ((inBlock_recut_iff hcut i j).mp hc)),
      recut_apply_of_not_inBlock hcut' h, recut_apply_of_not_inBlock hcut h]

/-! ### The content of a recut tableau -/

/-- Inside a row, the cells of a recut tableau carrying the letter `v` are those from the start of
the block to the splitting point. -/
theorem filter_recut_eq (hcut : IsCut T v cut) (i : ℕ) :
    ((Finset.range (μ.rowLen i)).filter fun j => recut T v cut hcut i j = v)
      = Finset.Ico (rowCountLt T i v) (cut i) := by
  have hcl : cut i ≤ μ.rowLen i := le_trans (hcut.cut_le i) (T.rowCountLt_le_rowLen i (v + 2))
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hj, hv⟩
    have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    by_cases h : T.InBlock v i j
    · rw [recut_apply_of_inBlock hcut h] at hv
      refine ⟨((T.inBlock_iff v hcell).mp h).1, ?_⟩
      by_contra hc
      rw [ite_eq_right hc] at hv
      omega
    · rw [recut_apply_of_not_inBlock hcut h] at hv
      exact absurd ⟨hcell, hv.ge, hv.le.trans (Nat.le_succ v)⟩ h
  · rintro ⟨hlow, hhigh⟩
    have hj : j < μ.rowLen i := lt_of_lt_of_le hhigh hcl
    have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have h : T.InBlock v i j :=
      (T.inBlock_iff v hcell).mpr ⟨hlow, lt_of_lt_of_le hhigh (hcut.cut_le i)⟩
    exact ⟨hj, by rw [recut_apply_of_inBlock hcut h, ite_eq_left hhigh]⟩

/-- Inside a row, the cells of a recut tableau carrying the letter `v + 1` are those from the
splitting point to the end of the block. -/
theorem filter_recut_eq_succ (hcut : IsCut T v cut) (i : ℕ) :
    ((Finset.range (μ.rowLen i)).filter fun j => recut T v cut hcut i j = v + 1)
      = Finset.Ico (cut i) (rowCountLt T i (v + 2)) := by
  have hbl : rowCountLt T i (v + 2) ≤ μ.rowLen i := T.rowCountLt_le_rowLen i (v + 2)
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨hj, hv⟩
    have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    by_cases h : T.InBlock v i j
    · rw [recut_apply_of_inBlock hcut h] at hv
      refine ⟨?_, ((T.inBlock_iff v hcell).mp h).2⟩
      by_contra hc
      rw [ite_eq_left (Nat.lt_of_not_le (fun hd => hc (Nat.le_of_not_lt fun he => hd.not_gt he)))]
        at hv
      omega
    · rw [recut_apply_of_not_inBlock hcut h] at hv
      exact absurd ⟨hcell, by omega, by omega⟩ h
  · rintro ⟨hlow, hhigh⟩
    have hj : j < μ.rowLen i := lt_of_lt_of_le hhigh hbl
    have hcell : ((i, j) : ℕ × ℕ) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr hj
    have h : T.InBlock v i j :=
      (T.inBlock_iff v hcell).mpr ⟨le_trans (hcut.le_cut i) hlow, hhigh⟩
    exact ⟨hj, by rw [recut_apply_of_inBlock hcut h, ite_eq_right (Nat.not_lt.mpr hlow)]⟩

/-- A recut moves no letter other than `v` and `v + 1`. -/
theorem content_recut_of_ne (hcut : IsCut T v cut) (hx : x ≠ v) (hx' : x ≠ v + 1) :
    content (recut T v cut hcut) x = content T x := by
  rw [content_apply, content_apply]
  refine congrArg Finset.card (Finset.filter_congr fun c hc => ?_)
  obtain ⟨i, j⟩ := c
  by_cases h : T.InBlock v i j
  · rw [recut_apply_of_inBlock hcut h]
    have hb := h.2
    have hne : T i j ≠ x := by omega
    have hne' : (if j < cut i then v else v + 1) ≠ x := by split <;> omega
    exact iff_of_false hne' hne
  · rw [recut_apply_of_not_inBlock hcut h]

/-- How often the letter `v` occurs in a recut tableau, counted row by row. -/
theorem content_recut (hcut : IsCut T v cut) :
    content (recut T v cut hcut) v
      = ∑ i ∈ Finset.range (μ.colLen 0), (cut i - rowCountLt T i v) := by
  rw [content_apply, YoungDiagram.card_filter_cells μ _ le_rfl]
  exact Finset.sum_congr rfl fun i _ => by rw [filter_recut_eq hcut i, Nat.card_Ico]

/-- How often the letter `v + 1` occurs in a recut tableau, counted row by row. -/
theorem content_recut_succ (hcut : IsCut T v cut) :
    content (recut T v cut hcut) (v + 1)
      = ∑ i ∈ Finset.range (μ.colLen 0), (rowCountLt T i (v + 2) - cut i) := by
  rw [content_apply, YoungDiagram.card_filter_cells μ _ le_rfl]
  exact Finset.sum_congr rfl fun i _ => by rw [filter_recut_eq_succ hcut i, Nat.card_Ico]

/-- How often the letter `v` occurs in a tableau, counted row by row: it is the recut count at the
tableau's own splitting points. -/
theorem content_eq_sum (T : SemistandardYoungTableau μ) (v : ℕ) :
    content T v
      = ∑ i ∈ Finset.range (μ.colLen 0), (rowCountLt T i (v + 1) - rowCountLt T i v) := by
  have h := content_recut (isCut_rowCountLt T v)
  rwa [recut_rowCountLt] at h

/-- How often the letter `v + 1` occurs in a tableau, counted row by row. -/
theorem content_succ_eq_sum (T : SemistandardYoungTableau μ) (v : ℕ) :
    content T (v + 1)
      = ∑ i ∈ Finset.range (μ.colLen 0), (rowCountLt T i (v + 2) - rowCountLt T i (v + 1)) := by
  have h := content_recut_succ (isCut_rowCountLt T v)
  rwa [recut_rowCountLt] at h

/-- A recut preserves how many cells carry one of the two letters `v` and `v + 1`; it only moves
the boundary between them. -/
theorem content_recut_add (hcut : IsCut T v cut) :
    content (recut T v cut hcut) v + content (recut T v cut hcut) (v + 1)
      = content T v + content T (v + 1) := by
  rw [content_recut hcut, content_recut_succ hcut, content_eq_sum, content_succ_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h₁ := hcut.le_cut i
  have h₂ := hcut.cut_le i
  have h₃ : rowCountLt T i v ≤ rowCountLt T i (v + 1) := T.rowCountLt_mono i (by omega)
  have h₄ : rowCountLt T i (v + 1) ≤ rowCountLt T i (v + 2) := T.rowCountLt_mono i (by omega)
  omega

/-! ### The Bender-Knuth involution -/

/-- The start of the block of the row above, the first row being treated as if the row above it
had an empty block: it is the constraint `SemistandardYoungTableau.IsCut.cut_succ_le` places on a
splitting point from above. -/
private def prevBlockStart (T : SemistandardYoungTableau μ) (v : ℕ) : ℕ → ℕ
  | 0 => rowCountLt T 0 (v + 2)
  | i + 1 => rowCountLt T i v

/-- The lower end of the interval of splitting points admissible in row `i`. -/
private def cutLower (T : SemistandardYoungTableau μ) (v i : ℕ) : ℕ :=
  max (rowCountLt T i v) (rowCountLt T (i + 1) (v + 2))

/-- The upper end of the interval of splitting points admissible in row `i`. -/
private def cutUpper (T : SemistandardYoungTableau μ) (v i : ℕ) : ℕ :=
  min (rowCountLt T i (v + 2)) (prevBlockStart T v i)

/-- The splitting point of `T` itself is at least the lower end of the admissible interval: `T` is
its own recut. -/
private theorem cutLower_le (T : SemistandardYoungTableau μ) (v i : ℕ) :
    cutLower T v i ≤ rowCountLt T i (v + 1) :=
  max_le (T.rowCountLt_mono i (Nat.le_succ v)) (T.rowCountLt_succ_le i (v + 1))

/-- The splitting point of `T` itself is at most the upper end of the admissible interval: `T` is
its own recut. -/
private theorem le_cutUpper (T : SemistandardYoungTableau μ) (v i : ℕ) :
    rowCountLt T i (v + 1) ≤ cutUpper T v i := by
  refine le_min (T.rowCountLt_mono i (Nat.le_succ (v + 1))) ?_
  cases i with
  | zero => exact T.rowCountLt_mono 0 (Nat.le_succ (v + 1))
  | succ k => exact T.rowCountLt_succ_le k v

/-- **The Bender-Knuth splitting point**: the reflection, in the interval of admissible splitting
points of row `i`, of the splitting point of `T` itself. -/
private def bkCut (T : SemistandardYoungTableau μ) (v i : ℕ) : ℕ :=
  cutLower T v i + cutUpper T v i - rowCountLt T i (v + 1)

/-- The Bender-Knuth splitting points are admissible. -/
private theorem isCut_bkCut (T : SemistandardYoungTableau μ) (v : ℕ) :
    IsCut T v (bkCut T v) where
  le_cut i := by
    have hlow := cutLower_le T v i
    have hhigh := le_cutUpper T v i
    have hstart : rowCountLt T i v ≤ cutLower T v i := le_max_left _ _
    unfold bkCut; omega
  cut_le i := by
    have hlow := cutLower_le T v i
    have hhigh := le_cutUpper T v i
    have hend : cutUpper T v i ≤ rowCountLt T i (v + 2) := min_le_left _ _
    unfold bkCut; omega
  succ_le_cut i := by
    have hlow := cutLower_le T v i
    have hhigh := le_cutUpper T v i
    have hpair : rowCountLt T (i + 1) (v + 2) ≤ cutLower T v i := le_max_right _ _
    unfold bkCut; omega
  cut_succ_le i := by
    have hlow := cutLower_le T v (i + 1)
    have hhigh := le_cutUpper T v (i + 1)
    have hpair : cutUpper T v (i + 1) ≤ rowCountLt T i v := min_le_right _ _
    unfold bkCut; omega

/-- **The Bender-Knuth involution at the letter `v`**: the recut of `T` at the reflected splitting
points. -/
def benderKnuth (T : SemistandardYoungTableau μ) (v : ℕ) : SemistandardYoungTableau μ :=
  recut T v (bkCut T v) (isCut_bkCut T v)

/-- Inside the block, the involution writes `v` before its splitting point and `v + 1` after it. -/
private theorem benderKnuth_apply_of_inBlock (T : SemistandardYoungTableau μ) (v : ℕ) {i j : ℕ}
    (h : T.InBlock v i j) : benderKnuth T v i j = if j < bkCut T v i then v else v + 1 :=
  recut_apply_of_inBlock (isCut_bkCut T v) h

/-- Outside the block, the involution leaves the entry alone. -/
theorem benderKnuth_apply_of_not_inBlock (T : SemistandardYoungTableau μ) (v : ℕ)
    {i j : ℕ} (h : ¬ T.InBlock v i j) : benderKnuth T v i j = T i j :=
  recut_apply_of_not_inBlock (isCut_bkCut T v) h

/-- The involution writes no letter other than the ones already there and the two it exchanges. -/
theorem benderKnuth_apply_eq_or (T : SemistandardYoungTableau μ) (v i j : ℕ) :
    benderKnuth T v i j = T i j ∨ benderKnuth T v i j = v ∨ benderKnuth T v i j = v + 1 :=
  recutEntry_eq_or T v (bkCut T v) i j

/-- The involution moves no letter into or out of the block, so it leaves the block alone. -/
theorem inBlock_benderKnuth_iff (T : SemistandardYoungTableau μ) (v i j : ℕ) :
    (benderKnuth T v).InBlock v i j ↔ T.InBlock v i j :=
  inBlock_recut_iff (isCut_bkCut T v) i j

theorem rowCountLt_benderKnuth_of_le (T : SemistandardYoungTableau μ) (v i : ℕ) (hx : x ≤ v) :
    rowCountLt (benderKnuth T v) i x = rowCountLt T i x :=
  rowCountLt_recut_of_le (isCut_bkCut T v) i hx

theorem rowCountLt_benderKnuth_of_ge (T : SemistandardYoungTableau μ) (v i : ℕ)
    (hx : v + 2 ≤ x) : rowCountLt (benderKnuth T v) i x = rowCountLt T i x :=
  rowCountLt_recut_of_ge (isCut_bkCut T v) i hx

private theorem rowCountLt_benderKnuth_succ (T : SemistandardYoungTableau μ) (v i : ℕ) :
    rowCountLt (benderKnuth T v) i (v + 1) = bkCut T v i :=
  rowCountLt_recut_succ (isCut_bkCut T v) i

/-- The interval of admissible splitting points is unchanged by the involution: its endpoints are
read off the row counts below and above the block, which the involution does not move. -/
private theorem bkCut_benderKnuth (T : SemistandardYoungTableau μ) (v i : ℕ) :
    bkCut (benderKnuth T v) v i = rowCountLt T i (v + 1) := by
  have hlow : cutLower (benderKnuth T v) v i = cutLower T v i := by
    unfold cutLower
    rw [rowCountLt_benderKnuth_of_le T v i le_rfl, rowCountLt_benderKnuth_of_ge T v (i + 1) le_rfl]
  have hprev : prevBlockStart (benderKnuth T v) v i = prevBlockStart T v i := by
    cases i with
    | zero => exact rowCountLt_benderKnuth_of_ge T v 0 le_rfl
    | succ k => exact rowCountLt_benderKnuth_of_le T v k le_rfl
  have hhigh : cutUpper (benderKnuth T v) v i = cutUpper T v i := by
    unfold cutUpper
    rw [rowCountLt_benderKnuth_of_ge T v i le_rfl, hprev]
  have h₁ := cutLower_le T v i
  have h₂ := le_cutUpper T v i
  unfold bkCut
  rw [hlow, hhigh, rowCountLt_benderKnuth_succ]
  unfold bkCut
  omega

/-- **The Bender-Knuth involution is an involution.** -/
@[simp]
theorem benderKnuth_benderKnuth (T : SemistandardYoungTableau μ) (v : ℕ) :
    benderKnuth (benderKnuth T v) v = T := by
  ext i j
  by_cases h : T.InBlock v i j
  · rw [benderKnuth_apply_of_inBlock _ v ((inBlock_benderKnuth_iff T v i j).mpr h),
      bkCut_benderKnuth]
    have hjr := YoungDiagram.mem_iff_lt_rowLen.mp h.1
    have hiff := T.lt_rowCountLt_iff (x := v + 1) hjr
    have := h.2
    split <;> omega
  · rw [benderKnuth_apply_of_not_inBlock _ v
      (fun hc => h ((inBlock_benderKnuth_iff T v i j).mp hc)),
      benderKnuth_apply_of_not_inBlock T v h]

theorem benderKnuth_involutive (μ : YoungDiagram) (v : ℕ) :
    Function.Involutive fun T : SemistandardYoungTableau μ => benderKnuth T v :=
  fun T => benderKnuth_benderKnuth T v

/-! ### The effect on the content -/

private theorem bkCut_key (T : SemistandardYoungTableau μ) (v i : ℕ) :
    bkCut T v i - rowCountLt T i v + (rowCountLt T i (v + 2) - prevBlockStart T v i)
      = rowCountLt T (i + 1) (v + 2) - rowCountLt T i v
        + (rowCountLt T i (v + 2) - rowCountLt T i (v + 1)) := by
  have h₁ := cutLower_le T v i
  have h₂ := le_cutUpper T v i
  unfold bkCut cutLower cutUpper at *
  omega

private theorem sum_prevBlockStart (T : SemistandardYoungTableau μ) (v : ℕ) :
    ∑ i ∈ Finset.range (μ.colLen 0), (rowCountLt T i (v + 2) - prevBlockStart T v i)
      = ∑ i ∈ Finset.range (μ.colLen 0),
          (rowCountLt T (i + 1) (v + 2) - rowCountLt T i v) := by
  cases hM : μ.colLen 0 with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ' (fun i => rowCountLt T i (v + 2) - prevBlockStart T v i) m,
      Finset.sum_range_succ (fun i => rowCountLt T (i + 1) (v + 2) - rowCountLt T i v) m]
    have hzero : rowCountLt T (m + 1) (v + 2) = 0 :=
      T.rowCountLt_eq_zero_of_colLen_le (le_of_eq hM) (v + 2)
    simp [prevBlockStart, hzero]

/-- **The Bender-Knuth involution exchanges the two letters it is named for**: after it, the letter
`v` occurs as often as `v + 1` did. -/
theorem content_benderKnuth_self (T : SemistandardYoungTableau μ) (v : ℕ) :
    content (benderKnuth T v) v = content T (v + 1) := by
  rw [benderKnuth, content_recut, content_succ_eq_sum]
  have hkey : ∑ i ∈ Finset.range (μ.colLen 0),
      (bkCut T v i - rowCountLt T i v + (rowCountLt T i (v + 2) - prevBlockStart T v i))
      = ∑ i ∈ Finset.range (μ.colLen 0),
        (rowCountLt T (i + 1) (v + 2) - rowCountLt T i v
          + (rowCountLt T i (v + 2) - rowCountLt T i (v + 1))) :=
    Finset.sum_congr rfl fun i _ => bkCut_key T v i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_prevBlockStart] at hkey
  omega

/-- **The Bender-Knuth involution exchanges the two letters it is named for**: after it, the letter
`v + 1` occurs as often as `v` did. -/
theorem content_benderKnuth_succ (T : SemistandardYoungTableau μ) (v : ℕ) :
    content (benderKnuth T v) (v + 1) = content T v := by
  have hadd := content_recut_add (isCut_bkCut T v)
  rw [← benderKnuth, content_benderKnuth_self] at hadd
  omega

/-- The Bender-Knuth involution leaves every other letter alone. -/
theorem content_benderKnuth_of_ne (T : SemistandardYoungTableau μ) (v : ℕ) (hx : x ≠ v)
    (hx' : x ≠ v + 1) : content (benderKnuth T v) x = content T x :=
  content_recut_of_ne (isCut_bkCut T v) hx hx'

/-- **The Bender-Knuth involution exchanges the multiplicities of `v` and `v + 1`** and fixes every
other one. -/
@[simp]
theorem content_benderKnuth (T : SemistandardYoungTableau μ) (v x : ℕ) :
    content (benderKnuth T v) x = content T (Equiv.swap v (v + 1) x) := by
  rcases eq_or_ne x v with rfl | hx
  · rw [Equiv.swap_apply_left, content_benderKnuth_self]
  rcases eq_or_ne x (v + 1) with rfl | hx'
  · rw [Equiv.swap_apply_right, content_benderKnuth_succ]
  · rw [Equiv.swap_apply_of_ne_of_ne hx hx', content_benderKnuth_of_ne T v hx hx']

end SemistandardYoungTableau
