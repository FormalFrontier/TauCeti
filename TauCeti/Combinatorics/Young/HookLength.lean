/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import TauCeti.Combinatorics.Young.Diagram

/-!
# Hooks and hook lengths of a Young diagram

The *hook* of a cell `c` of a Young diagram `μ` consists of `c` itself, the cells of `μ` strictly to
the right of `c` in its row (its *arm*), and the cells of `μ` strictly below `c` in its column (its
*leg*).  Its cardinality is the *hook length* `hookLength μ c`, the quantity appearing in the
hook-length formula `f^μ · ∏_{c ∈ μ} hookLength μ c = μ.card !`.

This file defines `YoungDiagram.arm`, `YoungDiagram.leg` and `YoungDiagram.hook` as finite sets of
cells, together with the numerical `armLength`, `legLength` and `hookLength`, and proves that the
cardinalities agree.  The basic theory is then developed: transposition exchanges arms and legs,
hook lengths strictly decrease along a row and down a column, a cell has hook length `1` exactly
when it is a corner of the diagram, and the product of the hook lengths of a diagram with a single
row (or a single column) is `μ.card !`.

The arm, the leg and the hook of a cell `c` are cut out of `μ`, so all three are empty apart from
`c` itself when `c ∉ μ`; in that case `hookLength μ c = 1`.  The lemmas below that would be false
for such a junk value carry the hypothesis `c ∈ μ` explicitly.

## Main definitions

* `TauCeti.YoungDiagram.hook`: the hook of a cell, as a `Finset (ℕ × ℕ)`.
* `TauCeti.YoungDiagram.hookLength`: the hook length of a cell, `armLength + legLength + 1`.

## Main results

* `TauCeti.YoungDiagram.card_hook`: the hook of a cell has `hookLength` many elements.
* `TauCeti.YoungDiagram.hookLength_transpose`: transposition preserves hook lengths.
* `TauCeti.YoungDiagram.hookLength_eq_one_iff`: a cell has hook length `1` exactly when neither the
  cell to its right nor the cell below it lies in the diagram; for a cell of the diagram this says
  that it is a corner.
* `TauCeti.YoungDiagram.prod_hookLength_eq_factorial_of_colLen_le_one`: the hook lengths of a
  one-row diagram multiply to `μ.card !`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  1, Example 1, where the arm, leg and hook lengths of a cell are introduced.
* [B. E. Sagan, *The Symmetric Group*][sagan2001], Section 3.10, for the hook-length formula.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 5, where `hookLength` is a pinned, individually claimable target.  Its milestone
  `standardCount μ * ∏ c ∈ μ.cells, hookLength μ c = μ.card !` is stated in terms of Layer 0's
  `standardCount`, so nothing here depends on the Specht modules of Layer 3; the Specht-module
  dimension form is a derived corollary of Layer 5's separate standard-basis target.
-/

public section

namespace TauCeti

namespace YoungDiagram

variable (μ : YoungDiagram) (c : ℕ × ℕ)

/-! ### Arms, legs and hooks -/

/-- The arm of the cell `c` in the Young diagram `μ`: the cells of `μ` lying strictly to the right
of `c` in the same row. -/
def arm : Finset (ℕ × ℕ) :=
  (Finset.Ico (c.2 + 1) (μ.rowLen c.1)).map ⟨fun j => (c.1, j), fun _ _ h => by simpa using h⟩

/-- The leg of the cell `c` in the Young diagram `μ`: the cells of `μ` lying strictly below `c` in
the same column. -/
def leg : Finset (ℕ × ℕ) :=
  (Finset.Ico (c.1 + 1) (μ.colLen c.2)).map ⟨fun i => (i, c.2), fun _ _ h => by simpa using h⟩

/-- The hook of the cell `c` in the Young diagram `μ`: the cell itself together with its arm and its
leg. -/
def hook : Finset (ℕ × ℕ) :=
  insert c (arm μ c ∪ leg μ c)

variable {μ c}

@[simp]
theorem mem_arm {d : ℕ × ℕ} : d ∈ arm μ c ↔ d ∈ μ ∧ d.1 = c.1 ∧ c.2 < d.2 := by
  obtain ⟨a, b⟩ := d
  simp only [arm, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk, Prod.mk.injEq,
    _root_.YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · rintro ⟨j, ⟨hj₁, hj₂⟩, rfl, rfl⟩
    exact ⟨hj₂, rfl, hj₁⟩
  · rintro ⟨hb, rfl, hc⟩
    exact ⟨b, ⟨hc, hb⟩, rfl, rfl⟩

@[simp]
theorem mem_leg {d : ℕ × ℕ} : d ∈ leg μ c ↔ d ∈ μ ∧ d.2 = c.2 ∧ c.1 < d.1 := by
  obtain ⟨a, b⟩ := d
  simp only [leg, Finset.mem_map, Finset.mem_Ico, Function.Embedding.coeFn_mk, Prod.mk.injEq,
    _root_.YoungDiagram.mem_iff_lt_colLen]
  constructor
  · rintro ⟨i, ⟨hi₁, hi₂⟩, rfl, rfl⟩
    exact ⟨hi₂, rfl, hi₁⟩
  · rintro ⟨ha, rfl, hc⟩
    exact ⟨a, ⟨hc, ha⟩, rfl, rfl⟩

@[simp]
theorem mem_hook {d : ℕ × ℕ} :
    d ∈ hook μ c ↔ d = c ∨ (d ∈ μ ∧ d.1 = c.1 ∧ c.2 < d.2) ∨ (d ∈ μ ∧ d.2 = c.2 ∧ c.1 < d.1) := by
  simp [hook]

theorem mem_hook_self : c ∈ hook μ c := by simp [mem_hook]

theorem arm_subset_cells : arm μ c ⊆ μ.cells := fun _ hd => (mem_arm.mp hd).1

theorem leg_subset_cells : leg μ c ⊆ μ.cells := fun _ hd => (mem_leg.mp hd).1

theorem hook_subset_cells (h : c ∈ μ) : hook μ c ⊆ μ.cells := by
  rw [hook, Finset.insert_subset_iff, Finset.union_subset_iff]
  exact ⟨h, arm_subset_cells, leg_subset_cells⟩

theorem notMem_arm_self : c ∉ arm μ c := by simp

theorem notMem_leg_self : c ∉ leg μ c := by simp

theorem disjoint_arm_leg : Disjoint (arm μ c) (leg μ c) := by
  refine Finset.disjoint_left.mpr fun d hd hd' => ?_
  have h₁ := (mem_arm.mp hd).2.1
  have h₂ := (mem_leg.mp hd').2.2
  omega

/-! ### Arm, leg and hook lengths -/

variable (μ c)

/-- The arm length of the cell `c` in the Young diagram `μ`: the number of cells of `μ` strictly to
the right of `c` in the same row. -/
def armLength : ℕ := μ.rowLen c.1 - c.2 - 1

/-- The leg length of the cell `c` in the Young diagram `μ`: the number of cells of `μ` strictly
below `c` in the same column. -/
def legLength : ℕ := μ.colLen c.2 - c.1 - 1

/-- The hook length of the cell `c` in the Young diagram `μ`: the number of cells in its hook. -/
def hookLength : ℕ := armLength μ c + legLength μ c + 1

/-- The arm length of a cell counts the columns of its row beyond it. -/
theorem armLength_def : armLength μ c = μ.rowLen c.1 - c.2 - 1 := (rfl)

/-- The leg length of a cell counts the rows of its column beyond it. -/
theorem legLength_def : legLength μ c = μ.colLen c.2 - c.1 - 1 := (rfl)

/-- The hook length of a cell is its arm length plus its leg length plus one, the cell itself. -/
theorem hookLength_def : hookLength μ c = armLength μ c + legLength μ c + 1 := (rfl)

/-- The arm of a cell has `armLength` many elements. -/
@[simp]
theorem card_arm : (arm μ c).card = armLength μ c := by
  simp only [arm, Finset.card_map, Nat.card_Ico, armLength]
  omega

/-- The leg of a cell has `legLength` many elements. -/
@[simp]
theorem card_leg : (leg μ c).card = legLength μ c := by
  simp only [leg, Finset.card_map, Nat.card_Ico, legLength]
  omega

/-- The hook of a cell has `hookLength` many elements: the numerical definition of `hookLength`
really does count the cells of the hook. -/
@[simp]
theorem card_hook : (hook μ c).card = hookLength μ c := by
  have hc : c ∉ arm μ c ∪ leg μ c := Finset.notMem_union.mpr ⟨notMem_arm_self, notMem_leg_self⟩
  rw [hook, Finset.card_insert_of_notMem hc, Finset.card_union_of_disjoint disjoint_arm_leg,
    card_arm, card_leg, hookLength]

theorem hookLength_pos : 0 < hookLength μ c := Nat.succ_pos _

variable {μ c}

/-- A cell of the diagram has hook length at most the size of the diagram. -/
theorem hookLength_le_card (h : c ∈ μ) : hookLength μ c ≤ μ.card := by
  rw [← card_hook]
  exact Finset.card_le_card (hook_subset_cells h)

/-! ### Transposition -/

variable (μ c)

/-- Transposition exchanges arms with legs: the arm of `c` in `μ.transpose` is the reflection of
the leg of `c.swap` in `μ`. -/
@[simp]
theorem arm_transpose :
    arm μ.transpose c = (leg μ c.swap).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  ext d
  rw [Finset.mem_map_equiv]
  simp [_root_.YoungDiagram.mem_transpose]

/-- Transposition exchanges legs with arms: the leg of `c` in `μ.transpose` is the reflection of
the arm of `c.swap` in `μ`. -/
@[simp]
theorem leg_transpose :
    leg μ.transpose c = (arm μ c.swap).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  ext d
  rw [Finset.mem_map_equiv]
  simp [_root_.YoungDiagram.mem_transpose]

/-- Transposition reflects hooks: the hook of `c` in `μ.transpose` is the reflection of the hook of
`c.swap` in `μ`. -/
@[simp]
theorem hook_transpose :
    hook μ.transpose c = (hook μ c.swap).map (Equiv.prodComm ℕ ℕ).toEmbedding := by
  simp only [hook, Finset.map_insert, Finset.map_union, arm_transpose, leg_transpose,
    Equiv.coe_toEmbedding, Equiv.prodComm_apply, Prod.swap_swap]
  -- the arm and the leg have traded places
  rw [Finset.union_comm]

/-- Transposition exchanges arm lengths with leg lengths. -/
@[simp]
theorem armLength_transpose : armLength μ.transpose c = legLength μ c.swap := by
  simp [armLength, legLength]

/-- Transposition exchanges leg lengths with arm lengths. -/
@[simp]
theorem legLength_transpose : legLength μ.transpose c = armLength μ c.swap := by
  simp [armLength, legLength]

/-- Transposition preserves hook lengths: the hook length of `c` in `μ.transpose` is that of
`c.swap` in `μ`. -/
@[simp]
theorem hookLength_transpose : hookLength μ.transpose c = hookLength μ c.swap := by
  simp only [hookLength, armLength_transpose, legLength_transpose]
  omega

/-- Transposing a Young diagram permutes its cells, and hence its hook lengths; in particular the
product of all hook lengths is a transposition invariant. -/
theorem prod_hookLength_transpose :
    ∏ c ∈ μ.transpose.cells, hookLength μ.transpose c = ∏ c ∈ μ.cells, hookLength μ c := by
  exact Finset.prod_equiv (Equiv.prodComm ℕ ℕ) (by simp) (by simp)

/-! ### Monotonicity along rows and columns -/

variable {μ c}

@[simp]
theorem armLength_eq_zero_iff : armLength μ c = 0 ↔ (c.1, c.2 + 1) ∉ μ := by
  rw [_root_.YoungDiagram.mem_iff_lt_rowLen, armLength_def]
  omega

@[simp]
theorem legLength_eq_zero_iff : legLength μ c = 0 ↔ (c.1 + 1, c.2) ∉ μ := by
  rw [_root_.YoungDiagram.mem_iff_lt_colLen, legLength_def]
  omega

/-- A cell has hook length `1` exactly when the cell to its right and the cell below it are both
absent from the diagram; for a cell of `μ` this says that it is a corner. -/
@[simp]
theorem hookLength_eq_one_iff :
    hookLength μ c = 1 ↔ (c.1, c.2 + 1) ∉ μ ∧ (c.1 + 1, c.2) ∉ μ := by
  rw [← armLength_eq_zero_iff, ← legLength_eq_zero_iff, hookLength_def]
  omega

/-- Hook lengths strictly decrease from left to right along a row. -/
theorem hookLength_lt_hookLength_of_col_lt (μ : YoungDiagram) {i j₁ j₂ : ℕ}
    (h : (i, j₂) ∈ μ) (hj : j₁ < j₂) :
    hookLength μ (i, j₂) < hookLength μ (i, j₁) := by
  have hrow : j₂ < μ.rowLen i := _root_.YoungDiagram.mem_iff_lt_rowLen.mp h
  have hcol : μ.colLen j₂ ≤ μ.colLen j₁ := μ.colLen_anti j₁ j₂ hj.le
  simp only [hookLength, armLength, legLength]
  omega

/-- Hook lengths strictly decrease from top to bottom down a column. -/
theorem hookLength_lt_hookLength_of_row_lt (μ : YoungDiagram) {i₁ i₂ j : ℕ}
    (h : (i₂, j) ∈ μ) (hi : i₁ < i₂) :
    hookLength μ (i₂, j) < hookLength μ (i₁, j) := by
  have hcol : i₂ < μ.colLen j := _root_.YoungDiagram.mem_iff_lt_colLen.mp h
  have hrow : μ.rowLen i₂ ≤ μ.rowLen i₁ := μ.rowLen_anti i₁ i₂ hi.le
  simp only [hookLength, armLength, legLength]
  omega

/-! ### Diagrams with a single row or a single column

A Young diagram `μ` has at most one row exactly when `μ.colLen 0 ≤ 1`.  Its hook lengths are then
`μ.card, μ.card - 1, …, 1`, so they multiply to `μ.card !`; the one-column case follows by
transposition.  These are the two instances of the multiplicative hook-length formula
`standardCount μ * ∏ c ∈ μ.cells, hookLength μ c = μ.card !` in which the number of standard Young
tableaux is `1`; that count is not computed here. -/

theorem cells_eq_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.cells = {0} ×ˢ Finset.range (μ.rowLen 0) := by
  have hrow : μ.cells = μ.row 0 := by
    refine (Finset.filter_true_of_mem fun d hd => ?_).symm
    have := _root_.YoungDiagram.mem_iff_lt_colLen.mp hd
    have := μ.colLen_anti 0 d.2 (Nat.zero_le _)
    omega
  rw [hrow, _root_.YoungDiagram.row_eq_prod]

theorem card_eq_rowLen_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    μ.card = μ.rowLen 0 := by
  simp [_root_.YoungDiagram.card, cells_eq_of_colLen_le_one h]

theorem hookLength_eq_rowLen_sub_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) {j : ℕ}
    (hj : j < μ.rowLen 0) :
    hookLength μ (0, j) = μ.rowLen 0 - j := by
  have hmem : (0, j) ∈ μ := _root_.YoungDiagram.mem_iff_lt_rowLen.mpr hj
  have hcol : 0 < μ.colLen j := _root_.YoungDiagram.mem_iff_lt_colLen.mp hmem
  have hcol' : μ.colLen j ≤ μ.colLen 0 := μ.colLen_anti 0 j (Nat.zero_le _)
  simp only [hookLength, armLength, legLength]
  omega

/-- The hook-length formula for a Young diagram with at most one row: the hook lengths multiply to
`μ.card !`. -/
theorem prod_hookLength_eq_factorial_of_colLen_le_one {μ : YoungDiagram} (h : μ.colLen 0 ≤ 1) :
    ∏ c ∈ μ.cells, hookLength μ c = Nat.factorial μ.card := by
  set m := μ.rowLen 0 with hm
  have hreflect : ∀ j ∈ Finset.range m, m - (m - 1 - j) = j + 1 := by
    intro j hj
    have := Finset.mem_range.mp hj
    omega
  rw [cells_eq_of_colLen_le_one h, Finset.prod_product, Finset.prod_singleton,
    card_eq_rowLen_of_colLen_le_one h, ← hm]
  rw [Finset.prod_congr rfl fun j hj =>
    hookLength_eq_rowLen_sub_of_colLen_le_one h (Finset.mem_range.mp hj)]
  rw [← Finset.prod_range_reflect (fun j => m - j) m]
  rw [Finset.prod_congr rfl hreflect]
  exact Finset.prod_range_add_one_eq_factorial m

/-- The hook-length formula for a Young diagram with at most one column: the hook lengths multiply
to `μ.card !`. -/
theorem prod_hookLength_eq_factorial_of_rowLen_le_one {μ : YoungDiagram} (h : μ.rowLen 0 ≤ 1) :
    ∏ c ∈ μ.cells, hookLength μ c = Nat.factorial μ.card := by
  rw [← prod_hookLength_transpose μ,
    prod_hookLength_eq_factorial_of_colLen_le_one (by simpa using h), card_transpose]

end YoungDiagram

end TauCeti
