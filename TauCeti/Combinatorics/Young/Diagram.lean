/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Multiset.Sort

/-!
# Counting the cells of a Young diagram by rows

Mathlib's `YoungDiagram.rowLens` records the lengths of the rows of a Young diagram.  This file
counts the cells of a diagram row by row: the row lengths sum to the number of cells, and the
first `k` row lengths sum to the number of cells lying in the first `k` rows, whether those
lengths are summed as `∑ i ∈ Finset.range k, μ.rowLen i` or as `(μ.rowLens.take k).sum`.  Since
the rows exhaust the cells, the row lengths also determine the diagram
(`YoungDiagram.rowLen_injective`).  Cutting the same count column by column,
`YoungDiagram.card_filter_fst_lt_filter_snd_eq` counts the cells of the first `k` rows
lying in a fixed column.  The same row-by-row reading applies to any property of the cells, not
only to counting them all: `YoungDiagram.card_filter_cells` counts the cells satisfying a
predicate one row at a time.

The partial sums are the shape of every dominance statement about partitions, since dominance
compares partial sums of decreasingly sorted parts, and the sorted parts of a partition are the
row lengths of its Young diagram.

Reading the rows also describes containment: one diagram is contained in another exactly when
each of its rows is shorter (`YoungDiagram.le_iff_forall_rowLen_le`), from which a diagram
has only finitely many sub-diagrams (`YoungDiagram.finite_Iic`).

The file closes with the two degenerate shapes, at the bottom and at the top of the dominance
order.  A diagram with at most one column has its cells described one row at a time by
`YoungDiagram.mem_iff_of_rowLen_le_one` and counted by
`YoungDiagram.card_eq_colLen_of_rowLen_le_one`; a diagram with at most one row is described
by `YoungDiagram.mem_iff_of_colLen_le_one` and counted by
`YoungDiagram.card_eq_rowLen_of_colLen_le_one`.
-/

public section

namespace YoungDiagram

/-- Transposing a Young diagram preserves its number of cells. -/
@[simp]
theorem card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  apply Finset.card_equiv (Equiv.prodComm ℕ ℕ)
  intro c
  simp

private theorem sum_list_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A row past the last one of a Young diagram is empty. -/
theorem rowLen_eq_zero_of_colLen_le {μ : YoungDiagram} {i : ℕ} (hi : μ.colLen 0 ≤ i) :
    μ.rowLen i = 0 := by
  by_contra h
  exact absurd (_root_.YoungDiagram.mem_iff_lt_colLen.mp
    (_root_.YoungDiagram.mem_iff_lt_rowLen.mpr (Nat.pos_of_ne_zero h))) (Nat.not_lt.mpr hi)

/-- A Young diagram is determined by its row lengths. -/
theorem rowLen_injective : Function.Injective _root_.YoungDiagram.rowLen := by
  intro μ ν h
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, _root_.YoungDiagram.mem_cells,
    _root_.YoungDiagram.mem_iff_lt_rowLen, _root_.YoungDiagram.mem_iff_lt_rowLen, congrFun h i]

/-- Reading the length of a row off `YoungDiagram.rowLens`, with `0` for the rows past the last
one. -/
theorem getD_rowLens (μ : YoungDiagram) (i : ℕ) : μ.rowLens.getD i 0 = μ.rowLen i := by
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, _root_.YoungDiagram.get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
      rowLen_eq_zero_of_colLen_le
        (le_of_eq_of_le _root_.YoungDiagram.length_rowLens.symm (Nat.le_of_not_lt hi))]

/-- Merge-sorting the row lengths of a Young diagram recovers them: they are already
decreasing. This is stated for `List.mergeSort` in the shape `simp` produces from
`Multiset.sort` on a coerced list (via `Multiset.coe_sort` and `ge_iff_le`), making it the
`simp` normal form for sorted row-length expressions; the public statement is
`TauCeti.YoungDiagram.sort_coe_rowLens`. -/
@[simp]
private theorem mergeSort_rowLens (μ : YoungDiagram) :
    μ.rowLens.mergeSort (fun a b => decide (b ≤ a)) = μ.rowLens :=
  List.mergeSort_eq_self _ μ.rowLens_sorted.pairwise

/-- Sorting the row lengths of a Young diagram, as a multiset, recovers the row lengths: they
are already decreasing. -/
theorem sort_coe_rowLens (μ : YoungDiagram) :
    (↑μ.rowLens : Multiset ℕ).sort (· ≥ ·) = μ.rowLens := by
  rw [Multiset.coe_sort]
  exact mergeSort_rowLens μ

/-- The first `k` row lengths of a Young diagram count its cells in the first `k` rows. -/
theorem sum_range_rowLen_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, μ.rowLen i = (μ.cells.filter fun c => c.1 < k).card := by
  symm
  calc
    (μ.cells.filter fun c => c.1 < k).card =
        ∑ i ∈ Finset.range k,
          ((μ.cells.filter fun c => c.1 < k).filter fun c => c.1 = i).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro c hc
      simp only [Finset.mem_coe, Finset.mem_filter] at hc
      exact Finset.mem_range.mpr hc.2
    _ = ∑ i ∈ Finset.range k, μ.rowLen i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [μ.rowLen_eq_card]
      congr 1
      ext c
      have hik : i < k := Finset.mem_range.mp hi
      simp only [Finset.mem_filter, _root_.YoungDiagram.mem_cells,
        _root_.YoungDiagram.mem_row_iff]
      aesop

/-- The cells of a Young diagram, counted over any range of rows that contains all of them.  This
is `YoungDiagram.sum_rowLens` with the range of summation chosen by hand instead of being
the exact number of rows `μ.colLen 0`. -/
theorem card_eq_sum_range_rowLen (μ : _root_.YoungDiagram) {N : ℕ} (hN : μ.colLen 0 ≤ N) :
    μ.card = ∑ i ∈ Finset.range N, μ.rowLen i := by
  rw [sum_range_rowLen_eq_card_filter_fst]
  refine (congrArg Finset.card (Finset.filter_true_of_mem fun c hc => ?_)).symm
  exact lt_of_lt_of_le ((_root_.YoungDiagram.mem_iff_lt_colLen.mp hc).trans_le
    (μ.colLen_anti 0 c.snd c.snd.zero_le)) hN

/-- **The cells of a Young diagram carrying a given property, counted row by row.**  The range of
summation is any range of rows containing all of them, as in
`YoungDiagram.card_eq_sum_range_rowLen`; a row past the last one contributes nothing, being
empty. -/
theorem card_filter_cells (μ : _root_.YoungDiagram) (p : ℕ × ℕ → Prop) [DecidablePred p] {N : ℕ}
    (hN : μ.colLen 0 ≤ N) :
    (μ.cells.filter p).card
      = ∑ i ∈ Finset.range N, ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).card := by
  have hcells : μ.cells.filter p
      = (Finset.range N).biUnion fun i =>
          ((Finset.range (μ.rowLen i)).filter fun j => p (i, j)).image fun j => (i, j) := by
    ext c
    obtain ⟨i, j⟩ := c
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image,
      _root_.YoungDiagram.mem_cells, Prod.mk.injEq]
    constructor
    · rintro ⟨hij, hp⟩
      refine ⟨i, lt_of_lt_of_le (lt_of_lt_of_le (_root_.YoungDiagram.mem_iff_lt_colLen.mp hij)
        (μ.colLen_anti 0 j j.zero_le)) hN, j, ⟨?_, hp⟩, rfl, rfl⟩
      exact _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij
    · rintro ⟨i', -, j', ⟨hj', hp⟩, rfl, rfl⟩
      exact ⟨_root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj', hp⟩
  rw [hcells, Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun i _ =>
      Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h
  · intro y _ z _ hyz
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    rintro c ⟨j, -, rfl⟩ ⟨j', -, hj'⟩
    exact hyz (congrArg Prod.fst hj').symm

/-- The first `k` entries of `YoungDiagram.rowLens` count the cells in the first `k` rows.  This
is `YoungDiagram.sum_range_rowLen_eq_card_filter_fst` with the truncation taken on the
list of row lengths, the form in which partial sums enter the dominance order on partitions. -/
theorem sum_take_rowLens_eq_card_filter_fst (μ : YoungDiagram) (k : ℕ) :
    (μ.rowLens.take k).sum = (μ.cells.filter fun c => c.1 < k).card := by
  rw [_root_.YoungDiagram.rowLens, ← List.map_take, List.take_range, sum_list_range,
    ← sum_range_rowLen_eq_card_filter_fst]
  have hsub : Finset.range (min k (μ.colLen 0)) ⊆ Finset.range k := fun i hi =>
    Finset.mem_range.mpr (lt_min_iff.mp (Finset.mem_range.mp hi)).1
  refine Finset.sum_subset hsub fun i hi hi' => ?_
  exact rowLen_eq_zero_of_colLen_le
    (by simpa [lt_min_iff, Finset.mem_range.mp hi] using Finset.mem_range.not.mp hi')

/-- The sum of the row lengths of a Young diagram is its number of cells. -/
@[simp]
theorem sum_rowLens (μ : YoungDiagram) : μ.rowLens.sum = μ.card := by
  rw [_root_.YoungDiagram.rowLens, sum_list_range, ← card_eq_sum_range_rowLen μ le_rfl]

/-- The cells of a Young diagram lying in a fixed column and in one of the first `k` rows are the
top `min k (colLen j)` cells of that column. -/
theorem card_filter_fst_lt_filter_snd_eq (lam : YoungDiagram) (k j : ℕ) :
    (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j).card
      = min k (lam.colLen j) := by
  have himg : (((lam.cells.filter fun c => c.1 < k)).filter fun c => c.2 = j)
      = (Finset.range (min k (lam.colLen j))).image fun i => (i, j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, lt_min_iff,
      _root_.YoungDiagram.mem_cells]
    constructor
    · rintro ⟨⟨hc, hk⟩, hj⟩
      refine ⟨c.1, ⟨hk, ?_⟩, ?_⟩
      · exact _root_.YoungDiagram.mem_iff_lt_colLen.mp (hj ▸ hc)
      · rw [← hj]
    · rintro ⟨i, ⟨hik, hicol⟩, rfl⟩
      exact ⟨⟨_root_.YoungDiagram.mem_iff_lt_colLen.mpr hicol, hik⟩, rfl⟩
  rw [himg, Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.fst h, Finset.card_range]

/-- A row of a sub-diagram is no longer than the corresponding row. -/
theorem rowLen_le_of_le {μ ν : YoungDiagram} (h : ν ≤ μ) (i : ℕ) : ν.rowLen i ≤ μ.rowLen i := by
  rcases Nat.eq_zero_or_pos (ν.rowLen i) with h0 | h0
  · omega
  · have hmem : ((i, ν.rowLen i - 1) : ℕ × ℕ) ∈ ν :=
      _root_.YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h hmem)
    omega

/-- A Young diagram is contained in another as soon as each of its rows is shorter. -/
theorem le_of_forall_rowLen_le {μ ν : YoungDiagram} (h : ∀ i, ν.rowLen i ≤ μ.rowLen i) : ν ≤ μ := by
  rintro ⟨i, j⟩ hc
  exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr
    ((_root_.YoungDiagram.mem_iff_lt_rowLen.mp hc).trans_le (h i))

/-- Containment of Young diagrams is containment of rows. -/
theorem le_iff_forall_rowLen_le {μ ν : YoungDiagram} : ν ≤ μ ↔ ∀ i, ν.rowLen i ≤ μ.rowLen i :=
  ⟨fun h => rowLen_le_of_le h, le_of_forall_rowLen_le⟩

/-- A row of a Young diagram is at least as long as any initial segment of cells it contains. -/
theorem le_rowLen_of_forall_mem {ν : YoungDiagram} {i k : ℕ}
    (h : ∀ j < k, ((i, j) : ℕ × ℕ) ∈ ν) : k ≤ ν.rowLen i := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  · have := _root_.YoungDiagram.mem_iff_lt_rowLen.mp (h (k - 1) (by omega))
    omega

/-- A Young diagram has finitely many sub-diagrams, each being determined by its set of cells. -/
theorem finite_Iic (μ : YoungDiagram) : (Set.Iic μ).Finite := by
  have hinj : Set.InjOn _root_.YoungDiagram.cells (Set.Iic μ) :=
    fun _ _ _ _ h => _root_.YoungDiagram.ext h
  refine Set.Finite.of_finite_image ?_ hinj
  refine Set.Finite.subset (μ.cells.powerset : Finset (Finset (ℕ × ℕ))).finite_toSet ?_
  rintro s ⟨ξ, hξ, rfl⟩
  exact Finset.mem_coe.mpr (Finset.mem_powerset.mpr fun c hc => Set.mem_Iic.mp hξ hc)

/-- **The cells of a Young diagram with at most one column.**  Every row is then either empty or
the single cell in column `0`, so a cell is a cell of the first column, and the diagram reaches
exactly as far down as that column does. -/
theorem mem_iff_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) {i j : ℕ} :
    (i, j) ∈ μ ↔ i < μ.colLen 0 ∧ j = 0 := by
  constructor
  · intro hij
    have hlt := _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij
    have hanti := μ.rowLen_anti 0 i (Nat.zero_le _)
    have hj : j = 0 := by omega
    subst hj
    exact ⟨_root_.YoungDiagram.mem_iff_lt_colLen.mp hij, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact _root_.YoungDiagram.mem_iff_lt_colLen.mpr hi

/-- The cells of a Young diagram with at most one column are exactly the cells `(i, 0)` with
`i < μ.colLen 0`: the whole of its first column, and nothing else. -/
theorem cells_eq_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    μ.cells = Finset.range (μ.colLen 0) ×ˢ {0} := by
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, mem_iff_of_rowLen_le_one h, Finset.mem_product,
    Finset.mem_range, Finset.mem_singleton]

/-- A Young diagram with at most one column has one cell in each of its `μ.colLen 0` rows. -/
theorem card_eq_colLen_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    μ.card = μ.colLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_rowLen_le_one h]

/-- **The cells of a Young diagram with at most one row.**  Every column is then either empty or
the single cell in row `0`, so a cell is a cell of the first row, and the diagram reaches exactly
as far right as that row does. -/
theorem mem_iff_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) {i j : ℕ} :
    (i, j) ∈ μ ↔ i = 0 ∧ j < μ.rowLen 0 := by
  constructor
  · intro hij
    have hlt := _root_.YoungDiagram.mem_iff_lt_colLen.mp hij
    have hanti := μ.colLen_anti 0 j (Nat.zero_le _)
    have hi : i = 0 := by omega
    subst hi
    exact ⟨rfl, _root_.YoungDiagram.mem_iff_lt_rowLen.mp hij⟩
  · rintro ⟨rfl, hj⟩
    exact _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj

/-- The cells of a Young diagram with at most one row are exactly the cells `(0, j)` with
`j < μ.rowLen 0`: the whole of its first row, and nothing else. -/
theorem cells_eq_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.cells = {0} ×ˢ Finset.range (μ.rowLen 0) := by
  ext c
  obtain ⟨i, j⟩ := c
  rw [_root_.YoungDiagram.mem_cells, mem_iff_of_colLen_le_one h, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_range]

/-- A Young diagram with at most one row has one cell in each of its `μ.rowLen 0` columns. -/
theorem card_eq_rowLen_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.card = μ.rowLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_colLen_le_one h]

end YoungDiagram

