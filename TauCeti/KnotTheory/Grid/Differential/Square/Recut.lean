/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Square.OverlapOrder
public import TauCeti.KnotTheory.Grid.Differential.Square.Repartition
public import TauCeti.KnotTheory.Grid.Rectangle.Juxtaposition

/-!
# Recutting a two-step grid rectangle decomposition along its other internal edge

A nondiagonal term in the square of the unblocked grid differential `∂⁻` is a pair of composable
empty rectangles whose two pairs of side columns are either disjoint or share exactly one column.
In the second case the two rectangles meet at a corner and their union is an L-shaped hexagon,
which can be cut into two rectangles in exactly one other way. This file builds that alternate cut
in the orientation where the two rectangles share their *initial* side column, and shows that it
is again a decomposition by two rectangles the unblocked differential counts, carrying the same
weight and passing through a different intermediate grid state.

The relation between the two cuts is packaged as `GridRectangleDecomposition.IsRepartition`: the
rectangles of each cut cover disjoint sets of squares, and the two unions agree. The geometric
construction separately proves that the two cuts have different intermediate states, and records
the intermediate state and the side columns of the new cut. The domain relation is exactly the
amount of information a weight needs: any multiplicative function of squares has the same product
on the two cuts, and in particular the `O`-monomials multiply to the same polynomial and
`X`-avoidance transfers.

The geometric input is the cyclic order forced by emptiness
(`cyclicOrder_of_isEmpty_of_left_eq_left`) and the finite-domain repartition identity for the
covered squares (`GridRectangle.coveredSquares_union_eq_of_mem_cIoo` and its complementary form).
Emptiness of the new rectangles is not part of that identity: it is proved here, and it is where
emptiness of *both* old rectangles is used, one for the columns below the cut and one for the
columns above it.

Three orientations of the shared side column remain: the two rectangles may share their terminal
side, or the terminal side of one may be the initial side of the other. Those three, and the
assembly of the disjoint, overlapping and annular cases into `∂⁻ ∘ ∂⁻ = 0`, are separate steps.

## Main results

* `TauCeti.GridRectangleDecomposition.exists_isRepartition_of_isEmpty_of_left_eq_left`: two
  composable empty rectangles sharing their initial side column admit a recut by two empty
  rectangles, whose intermediate state and side columns are computed.
* `GridRectangleDecomposition.exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_left`:
  for each two-step term of `∂⁻ ∘ ∂⁻` whose two rectangles share their initial side column there
  is a unique second such term through a different intermediate state.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping case of its juxtaposition case analysis. The recut follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangleDecomposition

variable {n : ℕ} {x z : GridState n}

/-! ### The two old rectangles read in the source state -/

/-- When the two rectangles share their initial side, that side differs from the second
rectangle's terminal side. -/
private theorem first_left_ne_second_right_of_left_eq_left
    (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) : D.first.left ≠ D.second.right := by
  rw [hleft]
  exact D.second.left_ne_right

/-- The common initial side and distinct terminal sides determine the source-state values of the
intermediate state at the common side and the second terminal side. -/
private theorem middle_apply_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right) :
    D.middle D.first.left = x D.first.right ∧
      D.middle D.second.right = x D.second.right :=
  ⟨D.first.map_left,
    D.first.map_of_ne _ (D.first_left_ne_second_right_of_left_eq_left hleft).symm hright.symm⟩

/-- The second rectangle of a decomposition whose two rectangles share their initial side column,
written in terms of the source state: its two horizontal sides are the rows of the source state at
the terminal columns of the two rectangles. -/
private theorem toGridRectangle_second_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right) :
    D.second.toGridRectangle =
      { left := D.first.left, right := D.second.right, bottom := x D.first.right,
        top := x D.second.right } := by
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_left_eq_left hleft hright
  have hbottom : D.middle D.second.left = x D.first.right := by
    rw [← hleft, hmid_first]
  rw [D.second.toGridRectangle_eq, hbottom, hmid_second, ← hleft]

/-- Emptiness of the second rectangle of a decomposition whose two rectangles share their initial
side column, read back in the source state.

Away from the two side columns of the first rectangle the intermediate state agrees with the
source state, so emptiness may be tested against the source state there. -/
private theorem forall_notMem_cIoo_second_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hsecond : D.second.IsEmpty) :
    ∀ c ∈ Grid.cIoo D.first.left D.second.right, c ≠ D.first.left → c ≠ D.first.right →
      x c ∉ Grid.cIoo (x D.first.right) (x D.second.right) := by
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_left_eq_left hleft hright
  have h := hsecond
  rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, ← hleft, hmid_first,
    hmid_second] at h
  intro c hc hca hcb
  have hcm := h c hc
  rwa [D.first.map_of_ne c hca hcb] at hcm

/-! ### Building the recut -/

/-- If a column belongs to both old column spans, the emptiness of the old rectangles excludes
its grid-state point from the open arc between the two extreme corner rows. -/
private theorem notMem_cIoo_of_mem_cIoo_of_mem_cIoo {a b d c : Fin n}
    (hrow : x b ∈ Grid.cIoo (x a) (x d))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo a d, c ≠ a → c ≠ b →
      x c ∉ Grid.cIoo (x b) (x d))
    (hcab : c ∈ Grid.cIoo a b) (hcad : c ∈ Grid.cIoo a d) :
    x c ∉ Grid.cIoo (x a) (x d) := by
  intro hmem
  have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hcab
  have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hcab
  have hcut : x c ∈ Grid.cIoo (x a) (x b) ∪ insert (x b) (Grid.cIoo (x b) (x d)) := by
    rw [Grid.cIoo_union_insert_cIoo_eq_cIoo_of_mem_cIoo hrow]
    exact hmem
  rw [Finset.mem_union, Finset.mem_insert] at hcut
  rcases hcut with hcut | hcut | hcut
  · exact hfirst c hcab hcut
  · exact hcb (x.toPerm.injective hcut)
  · exact hsecond c hcad hca hcb hcut

/-- The recut in the configuration where the terminal side of the first rectangle lies strictly
inside the column span of the second one.

The two rectangles `{a, b} × {x a, x b}` and `{a, d} × {x b, x d}` are cut apart along the column
line `b` instead of the row line `x b`. -/
private theorem exists_isRepartition_col_cut {a b d : Fin n}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hz : z = (x.swapColumns a b).swapColumns a d)
    (hcol : b ∈ Grid.cIoo a d) (hrow : x b ∈ Grid.cIoo (x a) (x d))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo a d, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x b) (x d)) :
    ∃ E : GridRectangleDecomposition x z,
      (E.middle = x.swapColumns b d ∧ E.first.left = b ∧ E.first.right = d ∧
          E.second.left = a ∧ E.second.right = b) ∧
        E.first.toGridRectangle = { left := b, right := d, bottom := x b, top := x d } ∧
          E.second.toGridRectangle = { left := a, right := b, bottom := x a, top := x d } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns b d).swapColumns a b := by
    rw [hz, GridState.swapColumns_swapColumns_conj x b d a b, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm]
  have hmid_a : (x.swapColumns b d) a = x a := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab had]
  have hmid_b : (x.swapColumns b d) b = x d := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_left]
  refine ⟨{ middle := x.swapColumns b d
            first := GridRectangleBetween.ofSwapColumns x _ b d hbd rfl
            second := GridRectangleBetween.ofSwapColumns _ z a b hab hz' },
          ⟨rfl, by simp, by simp, by simp, by simp⟩, by simp, by simp [hmid_a, hmid_b], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc
    have hcad : c ∈ Grid.cIoo a d := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcol hc
    have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hcad
    have hcb : c ≠ b := Grid.ne_left_of_mem_cIoo hc
    exact hsecond c hcad hca hcb
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_a,
      hmid_b]
    intro c hc hmem
    have hcb : c ≠ b := Grid.ne_right_of_mem_cIoo hc
    have hcad : c ∈ Grid.cIoo a d := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcol hc
    have hcd : c ≠ d := Grid.ne_right_of_mem_cIoo hcad
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hcb hcd] at hmem
    exact notMem_cIoo_of_mem_cIoo_of_mem_cIoo hrow hfirst hsecond hc hcad hmem

/-- The recut in the configuration where the terminal side of the second rectangle lies strictly
inside the column span of the first one.

The two rectangles `{a, b} × {x a, x b}` and `{a, d} × {x b, x d}` are cut apart along the column
line `d` instead of the row line `x b`. -/
private theorem exists_isRepartition_complementary_col_cut {a b d : Fin n}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hz : z = (x.swapColumns a b).swapColumns a d)
    (hcol : d ∈ Grid.cIoo a b) (hrow : x b ∈ Grid.cIoo (x a) (x d))
    (hfirst : ∀ c ∈ Grid.cIoo a b, x c ∉ Grid.cIoo (x a) (x b))
    (hsecond : ∀ c ∈ Grid.cIoo a d, c ≠ a → c ≠ b → x c ∉ Grid.cIoo (x b) (x d)) :
    ∃ E : GridRectangleDecomposition x z,
      (E.middle = x.swapColumns a d ∧ E.first.left = a ∧ E.first.right = d ∧
          E.second.left = d ∧ E.second.right = b) ∧
        E.first.toGridRectangle = { left := a, right := d, bottom := x a, top := x d } ∧
          E.second.toGridRectangle = { left := d, right := b, bottom := x a, top := x b } ∧
            E.first.IsEmpty ∧ E.second.IsEmpty := by
  have hz' : z = (x.swapColumns a d).swapColumns d b := by
    rw [hz, GridState.swapColumns_swapColumns_conj x a b a d, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
  have hmid_d : (x.swapColumns a d) d = x a := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_right]
  have hmid_b : (x.swapColumns a d) b = x b := by
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hbd]
  refine ⟨{ middle := x.swapColumns a d
            first := GridRectangleBetween.ofSwapColumns x _ a d had rfl
            second := GridRectangleBetween.ofSwapColumns _ z d b hbd.symm hz' },
          ⟨rfl, by simp, by simp, by simp, by simp⟩, by simp, by simp [hmid_d, hmid_b], ?_, ?_⟩
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top]
    intro c hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_right_of_mem_cIoo hcol hc
    exact notMem_cIoo_of_mem_cIoo_of_mem_cIoo hrow hfirst hsecond hcab hc
  · rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo]
    simp only [GridRectangleBetween.ofSwapColumns_left, GridRectangleBetween.ofSwapColumns_right,
      GridRectangleBetween.ofSwapColumns_bottom, GridRectangleBetween.ofSwapColumns_top, hmid_d,
      hmid_b]
    intro c hc
    have hcab : c ∈ Grid.cIoo a b := Grid.cIoo_subset_cIoo_left_of_mem_cIoo hcol hc
    have hca : c ≠ a := Grid.ne_left_of_mem_cIoo hcab
    have hcd : c ≠ d := Grid.ne_left_of_mem_cIoo hc
    rw [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hca hcd]
    exact hfirst c hcab

/-! ### The recut of a decomposition sharing its initial side column -/

/-- Two composable empty rectangles that share their initial side column and no other side admit
a *recut*: the L-shaped union of their domains has a second decomposition into two empty
rectangles, through a different intermediate grid state.

The two cyclic orders of the three side columns give the two shapes of the new cut, and in each
of them the intermediate state and the four side columns of the recut are computed, which by
`GridRectangleDecomposition.ext` determine it.

Emptiness of both rectangles enters twice. It fixes the cyclic order of the three side columns
and of the three corner rows, and it then transfers to the two new rectangles: the part of a new
rectangle below the cut is controlled by the first old rectangle and the part above it by the
second. -/
theorem exists_isRepartition_of_isEmpty_of_left_eq_left (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first.IsEmpty) (hsecond : D.second.IsEmpty) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧ E.first.IsEmpty ∧ E.second.IsEmpty ∧
        E.first.right = D.second.right ∧ E.second.right = D.first.right ∧
          ((D.first.right ∈ Grid.cIoo D.first.left D.second.right ∧
              E.middle = x.swapColumns D.first.right D.second.right ∧
                E.first.left = D.first.right ∧ E.second.left = D.first.left) ∨
            (D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
              E.middle = x.swapColumns D.first.left D.second.right ∧
                E.first.left = D.first.left ∧ E.second.left = D.second.right)) := by
  -- The three side columns, the target state and the two old rectangles, all read in the source
  -- state `x`.
  have hab : D.first.left ≠ D.first.right := D.first.left_ne_right
  have had := D.first_left_ne_second_right_of_left_eq_left hleft
  obtain ⟨hmid_first, hmid_second⟩ := D.middle_apply_of_left_eq_left hleft hright
  have hmid : D.middle = x.swapColumns D.first.left D.first.right :=
    D.first.target_eq_swapColumns
  have hz : z = (x.swapColumns D.first.left D.first.right).swapColumns D.first.left
      D.second.right := by
    rw [← hmid, hleft]
    exact D.second.target_eq_swapColumns
  obtain ⟨hcolcase, hrow⟩ := D.cyclicOrder_of_isEmpty_of_left_eq_left hleft hright hfirst hsecond
  simp only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, hmid_second] at hrow
  have hfirst' : ∀ c ∈ Grid.cIoo D.first.left D.first.right,
      x c ∉ Grid.cIoo (x D.first.left) (x D.first.right) := by
    have h := hfirst
    rw [GridRectangleBetween.isEmpty_iff_forall_notMem_cIoo] at h
    simpa only [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def] using h
  have hsecond' := D.forall_notMem_cIoo_second_of_left_eq_left hleft hright hsecond
  have hD1 : D.first.toGridRectangle =
      { left := D.first.left, right := D.first.right, bottom := x D.first.left,
        top := x D.first.right } := D.first.toGridRectangle_eq
  have hD2 := D.toGridRectangle_second_of_left_eq_left hleft hright
  have hDdisj : Disjoint D.first.toGridRectangle.coveredSquares
      D.second.toGridRectangle.coveredSquares := by
    rw [hD1, hD2]
    exact GridRectangle.disjoint_coveredSquares_of_row_cut hrow
  have hcol_exclusive : ¬(D.first.right ∈ Grid.cIoo D.first.left D.second.right ∧
      D.second.right ∈ Grid.cIoo D.first.left D.first.right) := by
    rw [Grid.mem_cIoo, Grid.mem_cIoo]
    rintro ⟨⟨_, hfirstRight⟩, ⟨_, hsecondRight⟩⟩
    split_ifs at hfirstRight hsecondRight <;> omega
  rcases hcolcase with hcol | hcol
  -- The terminal side of the first rectangle lies inside the column span of the second one: the
  -- new cut runs along that column.
  · obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_isRepartition_col_cut hab had hright hz hcol hrow hfirst' hsecond'
    have hmiddle : E.middle ≠ D.middle := by
      intro h
      have hval : E.middle D.first.left = D.middle D.first.left := by rw [h]
      rw [hmidE, hmid_first] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab had] at hval
      exact hab (x.toPerm.injective hval)
    have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
        E.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2]
      exact (GridRectangle.disjoint_coveredSquares_of_col_cut hcol).symm
    have hunion : E.first.toGridRectangle.coveredSquares ∪
        E.second.toGridRectangle.coveredSquares =
          D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo hcol hrow).symm
    refine ⟨E, ⟨⟨hDdisj, hEdisj, hunion⟩, hmiddle, hEfirst, hEsecond, hE1right,
      hE2right, Or.inl ⟨hcol, hmidE, hE1left, hE2left⟩⟩, ?_⟩
    intro E' hE'
    rcases hE' with ⟨_, _, _, _, hE1right', hE2right', hcols'⟩
    have hlefts : E'.first.left = D.first.right ∧
        E'.second.left = D.first.left := by
      rcases hcols' with ⟨_, _, hE1left', hE2left'⟩ |
          ⟨hcol', _, _, _⟩
      · exact ⟨hE1left', hE2left'⟩
      · exact (hcol_exclusive ⟨hcol, hcol'⟩).elim
    exact GridRectangleDecomposition.ext (hlefts.1.trans hE1left.symm)
      (hE1right'.trans hE1right.symm) (hlefts.2.trans hE2left.symm)
      (hE2right'.trans hE2right.symm)
  -- The terminal side of the second rectangle lies inside the column span of the first one: the
  -- new cut runs along that column instead.
  · obtain ⟨E, ⟨hmidE, hE1left, hE1right, hE2left, hE2right⟩, hE1, hE2, hEfirst, hEsecond⟩ :=
      exists_isRepartition_complementary_col_cut hab had hright hz hcol hrow hfirst' hsecond'
    have hmiddle : E.middle ≠ D.middle := by
      intro h
      have hval : E.middle D.first.right = D.middle D.first.right := by rw [h]
      rw [hmidE, D.first.map_right] at hval
      simp only [GridState.swapColumns_apply, Equiv.swap_apply_of_ne_of_ne hab.symm hright] at hval
      exact hab (x.toPerm.injective hval).symm
    have hEdisj : Disjoint E.first.toGridRectangle.coveredSquares
        E.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2]
      exact GridRectangle.disjoint_coveredSquares_of_col_cut hcol
    have hunion : E.first.toGridRectangle.coveredSquares ∪
        E.second.toGridRectangle.coveredSquares =
          D.first.toGridRectangle.coveredSquares ∪
            D.second.toGridRectangle.coveredSquares := by
      rw [hE1, hE2, hD1, hD2]
      exact (GridRectangle.coveredSquares_union_eq_of_mem_cIoo_complementary_col_cut hcol
        hrow).symm
    refine ⟨E, ⟨⟨hDdisj, hEdisj, hunion⟩, hmiddle, hEfirst, hEsecond, hE1right,
      hE2right, Or.inr ⟨hcol, hmidE, hE1left, hE2left⟩⟩, ?_⟩
    intro E' hE'
    rcases hE' with ⟨_, _, _, _, hE1right', hE2right', hcols'⟩
    have hlefts : E'.first.left = D.first.left ∧
        E'.second.left = D.second.right := by
      rcases hcols' with ⟨hcol', _, _, _⟩ |
          ⟨_, _, hE1left', hE2left'⟩
      · exact (hcol_exclusive ⟨hcol', hcol⟩).elim
      · exact ⟨hE1left', hE2left'⟩
    exact GridRectangleDecomposition.ext (hlefts.1.trans hE1left.symm)
      (hE1right'.trans hE1right.symm) (hlefts.2.trans hE2left.symm)
      (hE2right'.trans hE2right.symm)

/-- For each two-step term of `∂⁻ ∘ ∂⁻` whose two rectangles share their initial side column
there is a unique second such term through a different intermediate grid state. Its domain is a
repartition of the original domain, so its weight agrees over every coefficient ring. -/
theorem exists_isRepartition_of_mem_unblockedRectangles_of_left_eq_left (G : GridDiagram n)
    (D : GridRectangleDecomposition x z)
    (hleft : D.first.left = D.second.left) (hright : D.first.right ≠ D.second.right)
    (hfirst : D.first ∈ G.unblockedRectangles x D.middle)
    (hsecond : D.second ∈ G.unblockedRectangles D.middle z) :
    ∃! E : GridRectangleDecomposition x z,
      D.IsRepartition E ∧ E.middle ≠ D.middle ∧
        E.first ∈ G.unblockedRectangles x E.middle ∧
          E.second ∈ G.unblockedRectangles E.middle z ∧
            E.first.right = D.second.right ∧ E.second.right = D.first.right ∧
              ((D.first.right ∈ Grid.cIoo D.first.left D.second.right ∧
                  E.middle = x.swapColumns D.first.right D.second.right ∧
                    E.first.left = D.first.right ∧ E.second.left = D.first.left) ∨
                (D.second.right ∈ Grid.cIoo D.first.left D.first.right ∧
                  E.middle = x.swapColumns D.first.left D.second.right ∧
                    E.first.left = D.first.left ∧ E.second.left = D.second.right)) := by
  obtain ⟨E, ⟨hrecut, hmiddle, hEfirst, hEsecond, hE1right, hE2right, hcols⟩, hunique⟩ :=
    D.exists_isRepartition_of_isEmpty_of_left_eq_left hleft hright
    (G.isEmpty_of_mem_unblockedRectangles hfirst) (G.isEmpty_of_mem_unblockedRectangles hsecond)
  have hX₁ := G.disjoint_XSet_of_mem_unblockedRectangles hfirst
  have hX₂ := G.disjoint_XSet_of_mem_unblockedRectangles hsecond
  refine ⟨E, ⟨hrecut, hmiddle,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEfirst, hrecut.disjoint_coveredSquares_first hX₁ hX₂⟩,
    (G.mem_unblockedRectangles _).mpr
      ⟨hEsecond, hrecut.disjoint_coveredSquares_second hX₁ hX₂⟩,
    hE1right, hE2right, hcols⟩, ?_⟩
  intro E' hE'
  apply hunique E'
  exact ⟨hE'.1, hE'.2.1, (G.mem_unblockedRectangles _).mp hE'.2.2.1 |>.1,
    (G.mem_unblockedRectangles _).mp hE'.2.2.2.1 |>.1, hE'.2.2.2.2⟩

end GridRectangleDecomposition

end TauCeti
