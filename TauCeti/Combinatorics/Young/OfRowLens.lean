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
decreasing `f : Fin n → ℕ` is allowed to end in zeros, and `YoungDiagram.ofRowLensFin`
turns any such family into the diagram whose `i`-th row has length `f i` for `i < n` and which has
no row beyond. Reading the first `n` row lengths back off is then an honest inverse on the
diagrams with at most `n` rows — the form consumed when partitions with a bounded number of rows
are matched against weight data for `GL n`.

## Main definitions

* `YoungDiagram.ofRowLensFin`: the Young diagram with prescribed weakly decreasing row
  lengths `f : Fin n → ℕ` and no further rows.

## Main results

* `YoungDiagram.rowLen_ofRowLensFin` and
  `YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le`: the row lengths of `ofRowLensFin f hf`
  are `f` on `Fin n` and `0` beyond it.
* `YoungDiagram.colLen_zero_ofRowLensFin_le` and
  `YoungDiagram.ofRowLensFin_rowLen`: `ofRowLensFin` lands in the diagrams with at most
  `n` rows, and is there inverse to reading off the first `n` row lengths.
* `YoungDiagram.card_ofRowLensFin`: its number of cells is `∑ i, f i`.
-/

public section

namespace YoungDiagram

variable {n : ℕ}

/-- The Young diagram whose first `n` rows have the prescribed weakly decreasing lengths
`f : Fin n → ℕ`, and which has no row beyond.  Unlike `YoungDiagram.ofRowLens`, the family `f`
may take the value `0`; such an entry simply contributes an empty row. -/
def ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) : _root_.YoungDiagram :=
  _root_.YoungDiagram.ofRowLens (List.ofFn f) hf.sortedGE_ofFn

/-- The rows of `ofRowLensFin f hf` indexed by `Fin n` have the prescribed lengths. -/
@[simp]
theorem rowLen_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) (i : Fin n) :
    (ofRowLensFin f hf).rowLen i = f i := by
  have h : (i : ℕ) < (List.ofFn f).length := by simp
  simpa [ofRowLensFin] using
    _root_.YoungDiagram.rowLen_ofRowLens (w := List.ofFn f) (hw := hf.sortedGE_ofFn) ⟨i, h⟩

/-- The rows of `ofRowLensFin f hf` past the `n` prescribed ones are empty. -/
@[simp]
theorem rowLen_ofRowLensFin_eq_zero_of_le (f : Fin n → ℕ) (hf : Antitone f) {i : ℕ} (hi : n ≤ i) :
    (ofRowLensFin f hf).rowLen i = 0 := by
  by_contra h
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h)
  obtain ⟨hlt, -⟩ := _root_.YoungDiagram.mem_ofRowLens.mp hmem
  simp only [List.length_ofFn] at hlt
  exact absurd hlt (Nat.not_lt.mpr hi)

/-- `ofRowLensFin f hf` has at most `n` rows. -/
theorem colLen_zero_ofRowLensFin_le (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).colLen 0 ≤ n := by
  by_contra h
  have hmem : ((n, 0) : ℕ × ℕ) ∈ ofRowLensFin f hf :=
    _root_.YoungDiagram.mem_iff_lt_colLen.mpr (Nat.lt_of_not_le h)
  exact absurd (rowLen_ofRowLensFin_eq_zero_of_le f hf (le_refl n))
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mp hmem).ne'

/-- Reading the first `n` row lengths off a Young diagram with at most `n` rows recovers it. -/
theorem ofRowLensFin_rowLen (μ : _root_.YoungDiagram) (hμ : μ.colLen 0 ≤ n) :
    ofRowLensFin (fun i : Fin n => μ.rowLen i) (fun _ _ h => μ.rowLen_anti _ _ h) = μ := by
  refine rowLen_injective (funext fun i => ?_)
  by_cases hi : i < n
  · simpa using rowLen_ofRowLensFin (fun i : Fin n => μ.rowLen i)
      (fun _ _ h => μ.rowLen_anti _ _ h) ⟨i, hi⟩
  · rw [rowLen_ofRowLensFin_eq_zero_of_le _ (fun _ _ h => μ.rowLen_anti _ _ h)
        (Nat.le_of_not_lt hi),
      rowLen_eq_zero_of_colLen_le (hμ.trans (Nat.le_of_not_lt hi))]

/-- `ofRowLensFin f hf` has `∑ i, f i` cells. -/
@[simp]
theorem card_ofRowLensFin (f : Fin n → ℕ) (hf : Antitone f) :
    (ofRowLensFin f hf).card = ∑ i, f i := by
  rw [card_eq_sum_range_rowLen _ (colLen_zero_ofRowLensFin_le f hf),
    ← Fin.sum_univ_eq_sum_range (fun i => (ofRowLensFin f hf).rowLen i) n]
  exact Finset.sum_congr rfl fun i _ => rowLen_ofRowLensFin f hf i

end YoungDiagram

