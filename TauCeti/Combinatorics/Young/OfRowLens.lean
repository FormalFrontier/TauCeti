/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Sort
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Young diagrams from a bounded family of row lengths

Mathlib builds a Young diagram from a weakly decreasing `List ℕ` of row lengths
(`YoungDiagram.ofRowLens`) and reads that list back off a diagram (`YoungDiagram.rowLens`); the
two are inverse only after the *positive* entries are singled out, since `rowLens` never records
a row of length `0`.

Indexing the row lengths by `Fin n` rather than by a list removes that mismatch: a weakly
decreasing `f : Fin n → ℕ` is allowed to end in zeros, and `TauCeti.YoungDiagram.ofRowLensFin`
turns any such family into the diagram whose `i`-th row has length `f i` for `i < n` and which has
no row beyond. Reading the first `n` row lengths back off is then an honest inverse on the
diagrams with at most `n` rows — the form consumed when partitions with a bounded number of rows
are matched against weight data for `GL n`.

## Main definitions

* `TauCeti.YoungDiagram.ofRowLensFin`: the Young diagram with prescribed weakly decreasing row
  lengths `f : Fin n → ℕ` and no further rows.

## Main results

* `TauCeti.YoungDiagram.rowLen_ofRowLensFin` and
  `TauCeti.YoungDiagram.rowLen_ofRowLensFin_of_le`: the row lengths of `ofRowLensFin f hf` are
  `f` on `Fin n` and `0` beyond it.
* `TauCeti.YoungDiagram.colLen_zero_ofRowLensFin_le` and
  `TauCeti.YoungDiagram.ofRowLensFin_rowLen`: `ofRowLensFin` lands in the diagrams with at most
  `n` rows, and is there inverse to reading off the first `n` row lengths.
* `TauCeti.YoungDiagram.card_ofRowLensFin`: its number of cells is `∑ i, f i`.
-/

public section

namespace TauCeti

namespace YoungDiagram

open Finset

variable {n : ℕ}

/-- Two Young diagrams with the same row lengths are equal. -/
theorem eq_of_rowLen_eq {μ ν : _root_.YoungDiagram} (h : ∀ i, μ.rowLen i = ν.rowLen i) :
    μ = ν := by
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, h]

/-- The cells of a Young diagram, counted over any range of rows that contains all of them.  This
is `TauCeti.YoungDiagram.sum_rowLens` with the range of summation chosen by hand instead of being
the exact number of rows. -/
theorem card_eq_sum_range_rowLen (μ : _root_.YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ range N, μ.rowLen i := by
  rw [sum_range_rowLen_eq_card_filter_fst]
  refine (congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)).symm
  exact lt_of_lt_of_le ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
    (μ.colLen_anti 0 c.snd c.snd.zero_le)) hN

/-- A weakly decreasing family `f : Fin n → ℕ` is a weakly decreasing list of row lengths. -/
private theorem sortedGE_ofFn {f : Fin n → ℕ} (hf : Antitone f) : (List.ofFn f).SortedGE :=
  List.sortedGE_iff_pairwise.mpr (List.pairwise_ofFn.mpr fun _ _ hij => hf hij.le)

/-- The Young diagram whose first `n` rows have the prescribed weakly decreasing lengths
`f : Fin n → ℕ`, and which has no row beyond.  Unlike `YoungDiagram.ofRowLens`, the family `f`
may take the value `0`; such an entry simply contributes an empty row. -/
def ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) : _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens (List.ofFn f) (sortedGE_ofFn hf)

@[simp]
theorem rowLen_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (ofRowLensFin f hf).rowLen i = f i := by
  have h : (i : ℕ) < (List.ofFn f).length := by simp
  simpa [ofRowLensFin] using
    _root_.YoungDiagram.rowLen_ofRowLens (w := List.ofFn f) (hw := sortedGE_ofFn hf) ⟨i, h⟩

theorem rowLen_ofRowLensFin_of_le (f : Fin n → ℕ) (hf : Antitone f) {i : ℕ} (hi : n ≤ i) :
    (ofRowLensFin f hf).rowLen i = 0 := by
  by_contra h
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  obtain ⟨hlt, -⟩ := _root_.YoungDiagram.mem_ofRowLens.mp hmem
  simp only [List.length_ofFn] at hlt
  exact absurd hlt (Nat.not_lt.mpr hi)

theorem colLen_zero_ofRowLensFin_le (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  exact absurd (rowLen_ofRowLensFin_of_le f hf (le_refl n))
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mp hmem).ne'

/-- The first `n` row lengths of a Young diagram are weakly decreasing. -/
theorem antitone_rowLen (μ : _root_.YoungDiagram) (n : ℕ) :
    Antitone fun i : Fin n => μ.rowLen i := fun _ _ h => μ.rowLen_anti _ _ h

/-- Reading the first `n` row lengths off a Young diagram with at most `n` rows recovers it. -/
theorem ofRowLensFin_rowLen (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    ofRowLensFin (fun i : Fin n => μ.rowLen i) (antitone_rowLen μ n) = μ := by
  refine eq_of_rowLen_eq fun i => ?_
  by_cases hi : i < n
  · simpa using rowLen_ofRowLensFin (fun i : Fin n => μ.rowLen i) (antitone_rowLen μ n) ⟨i, hi⟩
  · rw [rowLen_ofRowLensFin_of_le _ (antitone_rowLen μ n) (Nat.le_of_not_lt hi),
      rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.le_of_not_lt hi))]

@[simp]
theorem card_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).card = ∑ i, f i := by
  rw [card_eq_sum_range_rowLen _ (colLen_zero_ofRowLensFin_le f hf),
    ← Fin.sum_univ_eq_sum_range (fun i => (ofRowLensFin f hf).rowLen i) n]
  exact Finset.sum_congr rfl fun i _ => rowLen_ofRowLensFin f hf i

end YoungDiagram

end TauCeti
