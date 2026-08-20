/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.AddBox
public import TauCeti.Combinatorics.Young.Interlacing

/-!
# The local count behind the Pieri rule

Fix two Young diagrams `ρ` and `ν`.  This file counts the cells that may be added to `ρ` so that
`ν` still interlaces the result, and matches that count against the corners of `ν` whose deletion
leaves a shape interlaced by `ρ`:

`#{c addable to ρ | ν interlaces ρ + c} = [ν interlaces ρ] + #{c corner of ν | ρ + nothing ⋯}`,

precisely `YoungDiagram.card_filter_addableCells_interlacedBy`.  Summed against the number of
standard Young tableaux, this is the inductive step of the dual Pieri rule
`TauCeti.sum_standardCount_interlacedBy`, and through it of the Schur--Weyl dimension count.

Both sides are counted by the row in which the cell sits, which turns the statement into
arithmetic of row lengths.  Write `rᵢ` and `vᵢ` for the row lengths of `ρ` and `ν`.  If `ν`
interlaces `ρ`, the cell added must sit in row `0`, or in a row `i` with `rᵢ < v_{i-1}`, and the
corners of `ν` that may be deleted are exactly the rows `i` with `r_{i+1} < vᵢ`; shifting the index
by one matches the two lists and leaves the row `0` over, which is the `1` in the formula.  If `ν`
does not interlace `ρ`, then a cell can be added, or a corner deleted, only at a row `i` where the
single failure of interlacing sits, and it must be `vᵢ = rᵢ + 1`; there the added cell and the
deleted corner are literally the same cell `(i, rᵢ)`, so the two counts agree.

## Main results

* `YoungDiagram.interlacedBy_iff_forall_lt`: interlacing is decided by finitely many rows, whence
  `YoungDiagram.instDecidableInterlacedBy`.
* `YoungDiagram.card_filter_addableCells_interlacedBy`: the count.

## References

* [W. Fulton, *Young Tableaux*][fulton1997], Section 2.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 8: Schur-Weyl duality
-/

public section

namespace YoungDiagram

variable {ρ ν : YoungDiagram} {N : ℕ}

/-! ### Deciding interlacing -/

/-- **Interlacing is decided by finitely many rows**: only the rows within the height of the
diagram interlaced can fail, since past that height the interlacing condition at the last row
forces both diagrams to be empty. -/
theorem interlacedBy_iff_forall_lt (μ ν : YoungDiagram) :
    InterlacedBy μ ν ↔
      ∀ i < μ.colLen 0 + 1, μ.rowLen (i + 1) ≤ ν.rowLen i ∧ ν.rowLen i ≤ μ.rowLen i := by
  refine ⟨fun h i _ => ⟨h.rowLen_succ_le i, h.rowLen_le i⟩,
    fun h => interlacedBy_iff.mpr fun i => ?_⟩
  rcases lt_or_ge i (μ.colLen 0 + 1) with hi | hi
  · exact h i hi
  · have h0 : μ.rowLen (μ.colLen 0) = 0 := rowLen_eq_zero_of_colLen_le le_rfl
    have hz : ν.rowLen (μ.colLen 0) = 0 := by
      have := (h (μ.colLen 0) (by omega)).2
      omega
    have h1 : ν.rowLen i = 0 :=
      Nat.le_zero.mp (hz ▸ ν.rowLen_anti (μ.colLen 0) i (by omega))
    have h2 : μ.rowLen (i + 1) = 0 := rowLen_eq_zero_of_colLen_le (by omega)
    have h3 : μ.rowLen i = 0 := rowLen_eq_zero_of_colLen_le (by omega)
    omega

instance instDecidableInterlacedBy (μ ν : YoungDiagram) : Decidable (InterlacedBy μ ν) :=
  decidable_of_iff _ (interlacedBy_iff_forall_lt μ ν).symm

/-! ### Counting by rows -/

/-- The rows below `N` in which a cell may be added to `ρ` keeping `ν` interlacing. -/
private def rowsAdd (ρ ν : YoungDiagram) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i =>
    IsAddable ρ (i, ρ.rowLen i) ∧ InterlacedBy (addBox ρ (i, ρ.rowLen i)) ν

/-- The rows below `N` in which a corner may be deleted from `ν` keeping it interlaced by `ρ`. -/
private def rowsCorner (ρ ν : YoungDiagram) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun i =>
    IsCorner ν (i, ν.rowLen i - 1) ∧ InterlacedBy ρ (erase ν (i, ν.rowLen i - 1))

private theorem mem_rowsAdd {i : ℕ} :
    i ∈ rowsAdd ρ ν N ↔ i < N ∧ IsAddable ρ (i, ρ.rowLen i) ∧
      InterlacedBy (addBox ρ (i, ρ.rowLen i)) ν := by
  simp only [rowsAdd, Finset.mem_filter, Finset.mem_range]

private theorem mem_rowsCorner {i : ℕ} :
    i ∈ rowsCorner ρ ν N ↔ i < N ∧ IsCorner ν (i, ν.rowLen i - 1) ∧
      InterlacedBy ρ (erase ν (i, ν.rowLen i - 1)) := by
  simp only [rowsCorner, Finset.mem_filter, Finset.mem_range]

/-- Counting addable cells by their rows. -/
private theorem card_filter_addableCells_eq (ρ ν : YoungDiagram) (hN : ρ.colLen 0 < N) :
    ((addableCells ρ).filter fun c => InterlacedBy (addBox ρ c) ν).card = (rowsAdd ρ ν N).card := by
  refine Finset.card_nbij' (fun c => c.1) (fun i => (i, ρ.rowLen i)) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_addableCells] at hc
    have hsnd : c = (c.1, ρ.rowLen c.1) := by rw [← hc.1.snd_eq]
    refine Finset.mem_coe.mpr (mem_rowsAdd.mpr ⟨lt_of_le_of_lt hc.1.fst_le_colLen hN, ?_, ?_⟩)
    · exact hsnd ▸ hc.1
    · exact hsnd ▸ hc.2
  · intro i hi
    obtain ⟨-, hadd, hint⟩ := mem_rowsAdd.mp (Finset.mem_coe.mp hi)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_addableCells.mpr hadd, hint⟩)
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_addableCells] at hc
    exact (by rw [← hc.1.snd_eq] : c = (c.1, ρ.rowLen c.1)).symm
  · intro i _
    rfl

/-- Counting deletable corners by their rows. -/
private theorem card_filter_corners_eq (ρ ν : YoungDiagram) (hN : ν.colLen 0 ≤ N) :
    ((corners ν).filter fun c => InterlacedBy ρ (erase ν c)).card = (rowsCorner ρ ν N).card := by
  refine Finset.card_nbij' (fun c => c.1) (fun i => (i, ν.rowLen i - 1)) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_corners] at hc
    have hrow : c.2 + 1 = ν.rowLen c.1 := (isCorner_iff_rowLen.mp (by simpa using hc.1)).1
    have hsnd : c = (c.1, ν.rowLen c.1 - 1) := by
      rw [show ν.rowLen c.1 - 1 = c.2 from by omega]
    refine Finset.mem_coe.mpr
      (mem_rowsCorner.mpr ⟨lt_of_lt_of_le hc.1.fst_lt_colLen hN, ?_, ?_⟩)
    · exact hsnd ▸ hc.1
    · exact hsnd ▸ hc.2
  · intro i hi
    obtain ⟨-, hcor, hint⟩ := mem_rowsCorner.mp (Finset.mem_coe.mp hi)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨mem_corners.mpr hcor, hint⟩)
  · intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, mem_corners] at hc
    have hrow : c.2 + 1 = ν.rowLen c.1 := (isCorner_iff_rowLen.mp (by simpa using hc.1)).1
    exact (by rw [show ν.rowLen c.1 - 1 = c.2 from by omega] :
      c = (c.1, ν.rowLen c.1 - 1)).symm
  · intro i _
    rfl

/-! ### The rows, when `ν` interlaces `ρ` -/

private theorem rowLen_addBox_row (ρ : YoungDiagram) {i : ℕ}
    (h : IsAddable ρ (i, ρ.rowLen i)) (j : ℕ) :
    (addBox ρ (i, ρ.rowLen i)).rowLen j = if j = i then ρ.rowLen j + 1 else ρ.rowLen j :=
  h.rowLen_addBox j

private theorem rowLen_erase_row (ν : YoungDiagram) {i : ℕ}
    (h : IsCorner ν (i, ν.rowLen i - 1)) (j : ℕ) :
    (erase ν (i, ν.rowLen i - 1)).rowLen j = if j = i then ν.rowLen j - 1 else ν.rowLen j :=
  h.rowLen_erase j

private theorem mem_rowsAdd_zero (h : InterlacedBy ρ ν) (hN : 0 < N) : 0 ∈ rowsAdd ρ ν N := by
  have hadd : IsAddable ρ (0, ρ.rowLen 0) := (isAddable_row ρ 0).mpr (by omega)
  refine mem_rowsAdd.mpr ⟨hN, hadd, interlacedBy_iff.mpr fun j => ?_⟩
  rw [rowLen_addBox_row ρ hadd (j + 1), rowLen_addBox_row ρ hadd j]
  have h1 := h.rowLen_succ_le j
  have h2 := h.rowLen_le j
  refine ⟨?_, ?_⟩
  · rw [ite_eq_right (by omega : ¬j + 1 = 0)]
    exact h1
  · split_ifs with hc <;> omega

private theorem mem_rowsAdd_succ (h : InterlacedBy ρ ν) (k : ℕ) :
    k + 1 ∈ rowsAdd ρ ν N ↔ k + 1 < N ∧ ρ.rowLen (k + 1) < ν.rowLen k := by
  constructor
  · intro hk
    obtain ⟨hlt, hadd, hint⟩ := mem_rowsAdd.mp hk
    have hj := hint.rowLen_succ_le k
    rw [rowLen_addBox_row ρ hadd (k + 1)] at hj
    split_ifs at hj with hc
    · exact ⟨hlt, by omega⟩
    · omega
  · rintro ⟨hlt, hrow⟩
    have hmono : ∀ j < k + 1, ρ.rowLen (k + 1) < ρ.rowLen j := by
      intro j hj
      have h1 : ν.rowLen k ≤ ρ.rowLen k := h.rowLen_le k
      have h2 : ρ.rowLen k ≤ ρ.rowLen j := ρ.rowLen_anti j k (by omega)
      omega
    have hadd : IsAddable ρ (k + 1, ρ.rowLen (k + 1)) := (isAddable_row ρ (k + 1)).mpr hmono
    refine mem_rowsAdd.mpr ⟨hlt, hadd, interlacedBy_iff.mpr fun j => ?_⟩
    rw [rowLen_addBox_row ρ hadd (j + 1), rowLen_addBox_row ρ hadd j]
    have h1 := h.rowLen_succ_le j
    have h2 := h.rowLen_le j
    refine ⟨?_, ?_⟩
    · split_ifs with hc
      · have hjk : j = k := by omega
        subst hjk
        omega
      · exact h1
    · split_ifs with hc <;> omega

private theorem mem_rowsCorner_iff_of_interlaced (h : InterlacedBy ρ ν) (i : ℕ) :
    i ∈ rowsCorner ρ ν N ↔ i < N ∧ ρ.rowLen (i + 1) < ν.rowLen i := by
  constructor
  · intro hi
    obtain ⟨hlt, hcor, hint⟩ := mem_rowsCorner.mp hi
    have hpos : 0 < ν.rowLen i := by
      have := (isCorner_iff_rowLen.mp hcor).1
      omega
    have hj := hint.rowLen_succ_le i
    rw [rowLen_erase_row ν hcor i] at hj
    split_ifs at hj with hc
    · exact ⟨hlt, by omega⟩
    · omega
  · rintro ⟨hlt, hrow⟩
    have hpos : 0 < ν.rowLen i := by omega
    have hbelow : ν.rowLen (i + 1) ≤ ν.rowLen i - 1 := by
      have := h.rowLen_le (i + 1)
      omega
    have hcor : IsCorner ν (i, ν.rowLen i - 1) :=
      isCorner_iff_rowLen.mpr ⟨by omega, by omega⟩
    refine mem_rowsCorner.mpr ⟨hlt, hcor, interlacedBy_iff.mpr fun j => ?_⟩
    rw [rowLen_erase_row ν hcor j]
    have h1 := h.rowLen_succ_le j
    have h2 := h.rowLen_le j
    refine ⟨?_, ?_⟩
    · split_ifs with hc
      · subst hc
        omega
      · exact h1
    · split_ifs with hc <;> omega

/-! ### The rows, when `ν` does not interlace `ρ` -/

/-- The one shape a failure of interlacing can take at a row that still admits a cell: the row is
one longer in `ν` than in `ρ`, and interlacing holds everywhere else. -/
private abbrev Defect (ρ ν : YoungDiagram) (i : ℕ) : Prop :=
  ν.rowLen i = ρ.rowLen i + 1 ∧ (∀ j, j ≠ i → ν.rowLen j ≤ ρ.rowLen j) ∧
    ∀ j, ρ.rowLen (j + 1) ≤ ν.rowLen j

private theorem lt_colLen_of_defect {i : ℕ} (hd : Defect ρ ν i) : i < ν.colLen 0 := by
  have hmem : ((i, 0) : ℕ × ℕ) ∈ ν := mem_iff_lt_rowLen.mpr (by omega)
  exact mem_iff_lt_colLen.mp hmem

private theorem mem_rowsAdd_iff_defect (h : ¬ InterlacedBy ρ ν) (i : ℕ) :
    i ∈ rowsAdd ρ ν N ↔ i < N ∧ Defect ρ ν i := by
  constructor
  · intro hi
    obtain ⟨hlt, hadd, hint⟩ := mem_rowsAdd.mp hi
    have hlow : ∀ j, ρ.rowLen (j + 1) ≤ ν.rowLen j := by
      intro j
      have hj := hint.rowLen_succ_le j
      rw [rowLen_addBox_row ρ hadd (j + 1)] at hj
      split_ifs at hj <;> omega
    have hup : ∀ j, j ≠ i → ν.rowLen j ≤ ρ.rowLen j := by
      intro j hj
      have hjj := hint.rowLen_le j
      rw [rowLen_addBox_row ρ hadd j, ite_eq_right hj] at hjj
      exact hjj
    have hupi : ν.rowLen i ≤ ρ.rowLen i + 1 := by
      have hjj := hint.rowLen_le i
      rw [rowLen_addBox_row ρ hadd i] at hjj
      split_ifs at hjj <;> omega
    refine ⟨hlt, ?_, hup, hlow⟩
    by_contra hne
    refine h (interlacedBy_iff.mpr fun j => ⟨hlow j, ?_⟩)
    rcases eq_or_ne j i with rfl | hj
    · omega
    · exact hup j hj
  · rintro ⟨hlt, heq, hup, hlow⟩
    have hprev : ∀ j < i, ρ.rowLen i < ρ.rowLen j := by
      intro j hj
      have h1 : ν.rowLen i ≤ ν.rowLen (i - 1) := ν.rowLen_anti (i - 1) i (by omega)
      have h2 : ν.rowLen (i - 1) ≤ ρ.rowLen (i - 1) := hup (i - 1) (by omega)
      have h3 : ρ.rowLen (i - 1) ≤ ρ.rowLen j := ρ.rowLen_anti j (i - 1) (by omega)
      omega
    have hadd : IsAddable ρ (i, ρ.rowLen i) := (isAddable_row ρ i).mpr hprev
    refine mem_rowsAdd.mpr ⟨hlt, hadd, interlacedBy_iff.mpr fun j => ?_⟩
    rw [rowLen_addBox_row ρ hadd (j + 1), rowLen_addBox_row ρ hadd j]
    have hlj := hlow j
    refine ⟨?_, ?_⟩
    · split_ifs with hc
      · subst hc
        have h1 : ν.rowLen (j + 1) ≤ ν.rowLen j := ν.rowLen_anti j (j + 1) (by omega)
        omega
      · exact hlj
    · split_ifs with hc
      · subst hc
        omega
      · exact hup j hc

private theorem mem_rowsCorner_iff_defect (h : ¬ InterlacedBy ρ ν) (i : ℕ) :
    i ∈ rowsCorner ρ ν N ↔ i < N ∧ Defect ρ ν i := by
  constructor
  · intro hi
    obtain ⟨hlt, hcor, hint⟩ := mem_rowsCorner.mp hi
    have hpos : 0 < ν.rowLen i := by
      have := (isCorner_iff_rowLen.mp hcor).1
      omega
    have hlow : ∀ j, ρ.rowLen (j + 1) ≤ ν.rowLen j := by
      intro j
      have hj := hint.rowLen_succ_le j
      rw [rowLen_erase_row ν hcor j] at hj
      split_ifs at hj <;> omega
    have hup : ∀ j, j ≠ i → ν.rowLen j ≤ ρ.rowLen j := by
      intro j hj
      have hjj := hint.rowLen_le j
      rw [rowLen_erase_row ν hcor j, ite_eq_right hj] at hjj
      exact hjj
    have hupi : ν.rowLen i - 1 ≤ ρ.rowLen i := by
      have hjj := hint.rowLen_le i
      rw [rowLen_erase_row ν hcor i] at hjj
      split_ifs at hjj <;> omega
    refine ⟨hlt, ?_, hup, hlow⟩
    by_contra hne
    refine h (interlacedBy_iff.mpr fun j => ⟨hlow j, ?_⟩)
    rcases eq_or_ne j i with rfl | hj
    · omega
    · exact hup j hj
  · rintro ⟨hlt, heq, hup, hlow⟩
    have hnext : ν.rowLen (i + 1) ≤ ρ.rowLen (i + 1) := hup (i + 1) (by omega)
    have hanti : ρ.rowLen (i + 1) ≤ ρ.rowLen i := ρ.rowLen_anti i (i + 1) (by omega)
    have hcor : IsCorner ν (i, ν.rowLen i - 1) :=
      isCorner_iff_rowLen.mpr ⟨by omega, by omega⟩
    refine mem_rowsCorner.mpr ⟨hlt, hcor, interlacedBy_iff.mpr fun j => ?_⟩
    rw [rowLen_erase_row ν hcor j]
    have hlj := hlow j
    refine ⟨?_, ?_⟩
    · split_ifs with hc
      · subst hc
        omega
      · exact hlj
    · split_ifs with hc
      · subst hc
        omega
      · exact hup j hc

/-! ### The count -/

/-- **The local count behind the Pieri rule.**  The cells that may be added to `ρ` so that `ν`
still interlaces the result are as many as the corners of `ν` whose deletion leaves a shape
interlaced by `ρ`, plus one if `ν` interlaces `ρ` itself. -/
theorem card_filter_addableCells_interlacedBy (ρ ν : YoungDiagram) :
    ((addableCells ρ).filter fun c => InterlacedBy (addBox ρ c) ν).card =
      (if InterlacedBy ρ ν then 1 else 0) +
        ((corners ν).filter fun c => InterlacedBy ρ (erase ν c)).card := by
  set N := max (ρ.colLen 0) (ν.colLen 0) with hNdef
  rw [card_filter_addableCells_eq (N := N + 1) ρ ν (by omega),
    card_filter_corners_eq (N := N) ρ ν (le_max_right _ _)]
  by_cases h : InterlacedBy ρ ν
  · rw [ite_eq_left h]
    have hset : rowsAdd ρ ν (N + 1) = insert 0 ((rowsCorner ρ ν N).image (· + 1)) := by
      ext i
      rcases i with - | k
      · simp only [Finset.mem_insert, true_or, iff_true]
        exact mem_rowsAdd_zero h (by omega)
      · rw [mem_rowsAdd_succ h k, Finset.mem_insert]
        simp only [Finset.mem_image, Nat.succ_ne_zero, false_or]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨k, (mem_rowsCorner_iff_of_interlaced h k).mpr ⟨by omega, h2⟩, rfl⟩
        · rintro ⟨m, hm, hmk⟩
          obtain ⟨h1, h2⟩ := (mem_rowsCorner_iff_of_interlaced h m).mp hm
          have hmk' : m = k := by omega
          subst hmk'
          exact ⟨by omega, h2⟩
    rw [hset, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (fun a b hab => by omega)]
    omega
  · rw [ite_eq_right h]
    have hset : rowsAdd ρ ν (N + 1) = rowsCorner ρ ν N := by
      ext i
      rw [mem_rowsAdd_iff_defect h i, mem_rowsCorner_iff_defect h i]
      constructor
      · rintro ⟨-, hd⟩
        exact ⟨lt_of_lt_of_le (lt_colLen_of_defect hd) (le_max_right _ _), hd⟩
      · rintro ⟨hlt, hd⟩
        exact ⟨by omega, hd⟩
    rw [hset]
    omega

end YoungDiagram
