/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.Disjoint

/-!
# Side-column overlap in two-step rectangle decompositions

A term in the square of the grid differential is a pair of composable rectangles. The
juxtaposition proof of `∂² = 0` splits according to how the two pairs of vertical sides meet.
This file makes that split exact: the pairs are disjoint, have one common column, or coincide.
The last case occurs exactly when the two rectangle moves return to the source state.

The finite set `GridRectangleDecomposition.commonSideColumns` is the intersection of the two
two-element side sets. Its cardinality is therefore at most two. Cardinality zero is the existing
predicate `HasDisjointSides`; cardinality one is named `HasOneCommonSide`; and cardinality two is
equivalent to equality of the source and target states. Consequently a nondiagonal coefficient
of the differential square has precisely the two geometric cases used by the later pairing:
disjoint rectangles or rectangles sharing exactly one side column.

## Main definitions

* `TauCeti.GridRectangleDecomposition.commonSideColumns`: the side columns used by both
  rectangles in a decomposition.
* `TauCeti.GridRectangleDecomposition.HasOneCommonSide`: the two rectangles share exactly one
  side column.

## Main results

* `TauCeti.GridRectangleDecomposition.card_commonSideColumns_le_two`: at most two side columns
  are common.
* `TauCeti.GridRectangleDecomposition.card_commonSideColumns_eq_two_iff`: both side columns are
  common exactly for a diagonal two-step path.
* `TauCeti.GridRectangleDecomposition.hasDisjointSides_or_hasOneCommonSide_or_eq`: every
  decomposition belongs to one of the three cases.
* `TauCeti.GridRectangleDecomposition.target_ne_source_iff`: a decomposition is nondiagonal
  exactly when its sides are disjoint or have exactly one column in common.

## References

This supplies the side-overlap case split for
`TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and `∂² = 0`".
The split is the opening bookkeeping of the juxtaposition proof in
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-- The columns which are sides of both rectangles in a two-step decomposition. -/
def commonSideColumns (D : GridRectangleDecomposition x z) : Finset (Fin n) :=
  D.first.sideColumns ∩ D.second.sideColumns

/-- A column is common to the two rectangles exactly when it is a side of each one. -/
@[simp]
theorem mem_commonSideColumns (D : GridRectangleDecomposition x z) (c : Fin n) :
    c ∈ D.commonSideColumns ↔
      c ∈ D.first.sideColumns ∧ c ∈ D.second.sideColumns := by
  simp [commonSideColumns]

/-- At most two columns are sides of both rectangles in a decomposition. -/
theorem card_commonSideColumns_le_two (D : GridRectangleDecomposition x z) :
    D.commonSideColumns.card ≤ 2 :=
  (Finset.card_le_card Finset.inter_subset_left).trans_eq D.first.card_sideColumns

/-- Two rectangles in a decomposition share exactly one side column. -/
def HasOneCommonSide (D : GridRectangleDecomposition x z) : Prop :=
  D.commonSideColumns.card = 1

/-- Having one common side means that there is a unique column which is a side of both
rectangles. -/
theorem hasOneCommonSide_iff_existsUnique (D : GridRectangleDecomposition x z) :
    D.HasOneCommonSide ↔
      ∃! c : Fin n, c ∈ D.first.sideColumns ∧ c ∈ D.second.sideColumns := by
  rw [HasOneCommonSide, Finset.card_eq_one_iff_existsUnique]
  simp only [mem_commonSideColumns]

/-- The two side pairs are disjoint exactly when their common-side set is empty. -/
@[simp]
theorem commonSideColumns_eq_empty_iff (D : GridRectangleDecomposition x z) :
    D.commonSideColumns = ∅ ↔ D.HasDisjointSides := by
  rw [D.hasDisjointSides_iff]
  simp only [commonSideColumns, GridRectangleBetween.sideColumns, Finset.ext_iff,
    Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
    iff_false, not_and, not_or]
  aesop

/-- The common-side set has cardinality zero exactly when the side pairs are disjoint.

This is not a separate simp lemma: `Finset.card_eq_zero` followed by
`commonSideColumns_eq_empty_iff` already gives the same normal form. -/
theorem card_commonSideColumns_eq_zero_iff (D : GridRectangleDecomposition x z) :
    D.commonSideColumns.card = 0 ↔ D.HasDisjointSides := by
  rw [Finset.card_eq_zero, D.commonSideColumns_eq_empty_iff]

/-- A two-step rectangle path returns to its source exactly when its two rectangles use the same
unordered pair of side columns. -/
theorem target_eq_source_iff_sideColumns_eq (D : GridRectangleDecomposition x z) :
    z = x ↔ D.first.sideColumns = D.second.sideColumns := by
  constructor
  · intro hzx
    have hpairs := x.sym2_mk_eq_of_swapColumns_swapColumns_eq_self
      D.first.left_ne_right D.second.left_ne_right (by
        calc
          (x.swapColumns D.first.left D.first.right).swapColumns
              D.second.left D.second.right =
              D.middle.swapColumns D.second.left D.second.right := by
                rw [← D.first.target_eq_swapColumns]
          _ = z := D.second.target_eq_swapColumns.symm
          _ = x := hzx)
    simpa only [GridRectangleBetween.sideColumns, Sym2.toFinset_mk_eq] using
      congrArg Sym2.toFinset hpairs
  · intro hsides
    have hpairs :
        s(D.first.left, D.first.right) = s(D.second.left, D.second.right) := by
      apply Sym2.ext
      intro c
      simpa only [Sym2.mem_iff, D.first.mem_sideColumns, D.second.mem_sideColumns] using
        iff_of_eq (congrArg (fun s : Finset (Fin n) => c ∈ s) hsides)
    calc
      z = D.middle.swapColumns D.second.left D.second.right :=
        D.second.target_eq_swapColumns
      _ = (x.swapColumns D.first.left D.first.right).swapColumns
          D.second.left D.second.right := by rw [← D.first.target_eq_swapColumns]
      _ = x :=
        (x.swapColumns_swapColumns_eq_self_iff_sym2_mk_eq
          D.first.left_ne_right D.second.left_ne_right).mpr hpairs

/-- Both side columns are common exactly when the two-step rectangle path returns to its source. -/
@[simp]
theorem card_commonSideColumns_eq_two_iff (D : GridRectangleDecomposition x z) :
    D.commonSideColumns.card = 2 ↔ z = x := by
  rw [D.target_eq_source_iff_sideColumns_eq]
  constructor
  · intro hcard
    have hfirst : D.commonSideColumns = D.first.sideColumns :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by simp [hcard])
    have hsecond : D.commonSideColumns = D.second.sideColumns :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by simp [hcard])
    exact hfirst.symm.trans hsecond
  · intro hsides
    rw [commonSideColumns, hsides, Finset.inter_self, D.second.card_sideColumns]

/-- Every two-step rectangle decomposition has disjoint sides, exactly one common side, or equal
source and target. -/
theorem hasDisjointSides_or_hasOneCommonSide_or_eq
    (D : GridRectangleDecomposition x z) :
    D.HasDisjointSides ∨ D.HasOneCommonSide ∨ z = x := by
  have hcard := D.card_commonSideColumns_le_two
  by_cases hzero : D.commonSideColumns.card = 0
  · exact Or.inl (D.card_commonSideColumns_eq_zero_iff.mp hzero)
  by_cases hone : D.commonSideColumns.card = 1
  · exact Or.inr (Or.inl hone)
  · exact Or.inr (Or.inr (D.card_commonSideColumns_eq_two_iff.mp (by omega)))

/-- In a nondiagonal two-step rectangle decomposition, the side pairs are disjoint or share
exactly one column. This is the two-case split used by the nondiagonal juxtaposition pairing. -/
theorem hasDisjointSides_or_hasOneCommonSide_of_ne
    (D : GridRectangleDecomposition x z) (hzx : z ≠ x) :
    D.HasDisjointSides ∨ D.HasOneCommonSide := by
  rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hzx h).elim

/-- A two-step rectangle decomposition is nondiagonal exactly when its side pairs are disjoint or
share exactly one column. -/
theorem target_ne_source_iff (D : GridRectangleDecomposition x z) :
    z ≠ x ↔ D.HasDisjointSides ∨ D.HasOneCommonSide := by
  constructor
  · exact D.hasDisjointSides_or_hasOneCommonSide_of_ne
  · intro h hzx
    have htwo := D.card_commonSideColumns_eq_two_iff.mpr hzx
    rcases h with h | h
    · have hzero := D.card_commonSideColumns_eq_zero_iff.mpr h
      omega
    · rw [HasOneCommonSide] at h
      omega

/-- A decomposition with disjoint side pairs is necessarily nondiagonal. -/
theorem target_ne_source_of_hasDisjointSides (D : GridRectangleDecomposition x z)
    (h : D.HasDisjointSides) : z ≠ x :=
  D.target_ne_source_iff.mpr (Or.inl h)

/-- A decomposition with one common side is necessarily nondiagonal. -/
theorem target_ne_source_of_hasOneCommonSide (D : GridRectangleDecomposition x z)
    (h : D.HasOneCommonSide) : z ≠ x :=
  D.target_ne_source_iff.mpr (Or.inr h)

/-- The disjoint-side and one-common-side cases are mutually exclusive. -/
theorem not_hasDisjointSides_of_hasOneCommonSide (D : GridRectangleDecomposition x z)
    (h : D.HasOneCommonSide) : ¬D.HasDisjointSides := by
  intro hdisjoint
  have hzero := D.card_commonSideColumns_eq_zero_iff.mpr hdisjoint
  rw [HasOneCommonSide] at h
  omega

end GridRectangleDecomposition

end TauCeti
