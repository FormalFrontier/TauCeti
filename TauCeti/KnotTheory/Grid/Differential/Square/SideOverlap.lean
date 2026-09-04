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
* `TauCeti.GridRectangleDecomposition.hasDisjointSides_of_disjoint`: a decomposition whose target
  applies two disjoint column transpositions has disjoint side pairs.
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

/-- If two rectangles share exactly one side column, that column occurs in one of the four
possible ordered-side positions, and the two noncommon sides are distinct. -/
theorem side_eq_cases_of_hasOneCommonSide (D : GridRectangleDecomposition x z)
    (h : D.HasOneCommonSide) :
    (D.first.left = D.second.left ∧ D.first.right ≠ D.second.right) ∨
      (D.first.left = D.second.right ∧ D.first.right ≠ D.second.left) ∨
      (D.first.right = D.second.left ∧ D.first.left ≠ D.second.right) ∨
        (D.first.right = D.second.right ∧ D.first.left ≠ D.second.left) := by
  obtain ⟨c, hc, hunique⟩ := D.hasOneCommonSide_iff_existsUnique.mp h
  rcases D.first.mem_sideColumns c |>.mp hc.1 with hcfirst | hcfirst <;>
    rcases D.second.mem_sideColumns c |>.mp hc.2 with hcsecond | hcsecond
  · left
    refine ⟨hcfirst.symm.trans hcsecond, fun hother => ?_⟩
    have := hunique D.first.right ⟨by simp, by simp [← hother]⟩
    exact D.first.left_ne_right (hcfirst.symm.trans this.symm)
  · right; left
    refine ⟨hcfirst.symm.trans hcsecond, fun hother => ?_⟩
    have := hunique D.first.right ⟨by simp, by simp [← hother]⟩
    exact D.first.left_ne_right (hcfirst.symm.trans this.symm)
  · right; right; left
    refine ⟨hcfirst.symm.trans hcsecond, fun hother => ?_⟩
    have := hunique D.first.left ⟨by simp, by simp [← hother]⟩
    exact D.first.left_ne_right (this.trans hcfirst)
  · right; right; right
    refine ⟨hcfirst.symm.trans hcsecond, fun hother => ?_⟩
    have := hunique D.first.left ⟨by simp, by simp [← hother]⟩
    exact D.first.left_ne_right (this.trans hcfirst)

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

/-- Two disjoint column transpositions move four columns, so no two-step rectangle decomposition
of the resulting state can share a side column.

This is the entry point that puts a two-step term over such a target in the disjoint-side case of
`hasDisjointSides_or_hasOneCommonSide_or_eq`. -/
theorem hasDisjointSides_of_disjoint (x : GridState n) {a b c d : Fin n} (hab : a ≠ b)
    (hcd : c ≠ d) (hdisjoint : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    (D : GridRectangleDecomposition x ((x.swapColumns a b).swapColumns c d)) :
    D.HasDisjointSides := by
  -- The two rectangles of a decomposition fix every column outside their four side columns.
  -- Sharing a side column would leave only three such columns, and sharing both would return to
  -- the source.
  obtain ⟨hac, had⟩ : a ≠ c ∧ a ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      Finset.disjoint_left.mp hdisjoint (by simp : a ∈ ({a, b} : Finset (Fin n)))
  obtain ⟨hbc, hbd⟩ : b ≠ c ∧ b ≠ d := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
      Finset.disjoint_left.mp hdisjoint (by simp : b ∈ ({a, b} : Finset (Fin n)))
  -- the four columns the two transpositions move, and their images
  have hza : (x.swapColumns a b).swapColumns c d a = x b := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hac had]
  have hzb : (x.swapColumns a b).swapColumns c d b = x a := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd]
  have hzc : (x.swapColumns a b).swapColumns c d c = x d := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hzd : (x.swapColumns a b).swapColumns c d d = x c := by
    simp [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm]
  have hmoved : ∀ e ∈ ({a, b, c, d} : Finset (Fin n)),
      e ∈ D.first.sideColumns ∪ D.second.sideColumns := by
    intro e he
    by_contra hnot
    rw [Finset.mem_union, not_or] at hnot
    have hfix := D.target_apply_of_notMem_sideColumns hnot.1 hnot.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact hab (x.toPerm.injective (hza ▸ hfix).symm)
    · exact hab (x.toPerm.injective (hzb ▸ hfix))
    · exact hcd (x.toPerm.injective (hzc ▸ hfix).symm)
    · exact hcd (x.toPerm.injective (hzd ▸ hfix))
  rcases D.hasDisjointSides_or_hasOneCommonSide_or_eq with hcase | hcase | hcase
  · exact hcase
  · exfalso
    have hinter : D.commonSideColumns = D.first.sideColumns ∩ D.second.sideColumns := rfl
    have hcard : D.commonSideColumns.card = 1 := hcase
    have hsum := Finset.card_union_add_card_inter D.first.sideColumns D.second.sideColumns
    rw [D.first.card_sideColumns, D.second.card_sideColumns, ← hinter, hcard] at hsum
    have hfour : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]),
        Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    have hle := Finset.card_le_card hmoved
    rw [hfour] at hle
    omega
  · exfalso
    have hxa : x a = x b := by rw [← hza, hcase]
    exact hab (x.toPerm.injective hxa)

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
