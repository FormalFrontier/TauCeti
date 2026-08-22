/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.Grading.Change
public import TauCeti.KnotTheory.Grid.Rectangle.Squares

/-!
# The grading changes across a rectangle are marking counts

`Grading/Change.lean` localizes the grading changes across a rectangle move to the four corners
of the rectangle: each change is an alternating combination of the pairings of the two source
corners and the two target corners against the marking sets, plus, for the Maslov gradings, the
pairings of those corners against each other and against the squares the two states share. This
file evaluates all of those combinations and so puts the grading changes in the closed form the
rest of the theory uses,

`A(x) - A(y) = #(𝕏 ∩ r) - #(𝕆 ∩ r)` for every rectangle, and
`M_O(x) - M_O(y) = 2 #(x ∩ r) - 1 - 2 #(𝕆 ∩ r)` for every rectangle. For an empty
rectangle the latter specializes to `M_O(x) - M_O(y) = 1 - 2 #(𝕆 ∩ r)`,

where `r` is the set of squares the rectangle covers (`GridRectangle.coveredSquares`).

The evaluation is pointwise in the marking. Writing `u`, `v`, `s`, `t` for the indicators of the
four comparisons `left ≤ c`, `right ≤ c`, `bottom ≤ r`, `top ≤ r` of a marked square `(c, r)`,
the four corner terms contribute `2 (u - v) (s - t)` to twice the alternating combination, an
identity of polynomials in four variables. The factor `u - v` is the indicator of the covered
columns when the rectangle does not wrap around the torus horizontally, and that indicator minus
one when it does; likewise for `s - t` and the covered rows. Summing over a marking set therefore
produces the count of markings inside the rectangle, corrected by terms proportional to the
number of covered columns, the number of covered rows and the grid size. Those corrections are
the same for `𝕆` and for `𝕏`, because each marking set meets every column and every row exactly
once, so they cancel in the Alexander grading and the wrapping of the rectangle leaves no trace.

The same evaluation, applied to the two `J`-terms that the Maslov grading change carries in
addition, gives the general Maslov formula above. For an **empty** rectangle, the rectangle covers
only one occupied square of its source state, its own lower-left corner, yielding the familiar
constant `1`. Here the wrapping corrections do not cancel between two marking sets; instead they
cancel against the corner pairings and the shared squares.

Together the two formulas give bidegree `(-1, 0)` when an empty rectangle's
`GridRectangle.coveredSquares` are disjoint from the markings. This square-disjointness is
stronger than the existing, interior-based `GridRectangle.AvoidsMarkings` predicate and does not
follow from it. Two further consequences are recorded: the Alexander grading changes by an
integer across any rectangle move, even though the grading itself is a priori only rational, and
a square-disjoint rectangle preserves it outright.

## Main results

* `TauCeti.GridDiagram.alexander_sub_alexander_eq_card_sub_card`: the Alexander grading change
  across a rectangle move is the number of `X`-markings in the squares the rectangle covers minus
  the number of `O`-markings there.
* `TauCeti.GridDiagram.maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card`,
  `TauCeti.GridDiagram.maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card`: the Maslov
  grading changes across any rectangle move in terms of the covered source-state squares and
  corresponding marking count.
* `TauCeti.GridDiagram.maslovO_sub_maslovO_eq_one_sub_two_mul_card`,
  `TauCeti.GridDiagram.maslovX_sub_maslovX_eq_one_sub_two_mul_card`: the Maslov grading changes
  across an *empty* rectangle move are one minus twice the corresponding marking count.
* `TauCeti.GridDiagram.alexander_eq_alexander_of_disjoint_coveredSquares`,
  `TauCeti.GridDiagram.maslovO_sub_maslovO_eq_one_of_disjoint_coveredSquares`,
  `TauCeti.GridDiagram.maslovX_sub_maslovX_eq_one_of_disjoint_coveredSquares`: a square-disjoint
  empty rectangle move preserves the Alexander grading and drops either Maslov grading by one.
* `TauCeti.GridDiagram.exists_int_alexander_sub_alexander`: the Alexander gradings of two grid
  states joined by a rectangle differ by an integer.

## References

This supplies `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2, "Gradings.
The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`; grading-change formulas across a
rectangle", in the closed form Lanes G.3 and G.4 consume. The
formulas are Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.3, where the
grading changes across a rectangle `r` from `x` to `y` are `A(x) - A(y) = #(r ∩ 𝕏) - #(r ∩ 𝕆)`
and, for an empty rectangle, `M_O(x) - M_O(y) = 1 - 2 #(r ∩ 𝕆)`.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- Twice the pairing of a single grid point against a set of marked squares, written as a sum
over the marked squares of a product of column and row indicators. A marked square contributes
exactly when it is weakly northeast of the point, or the point is strictly northeast of it. -/
private theorem two_mul_JCenter_singleton_left_eq_sum (p : Fin n × Fin n)
    (P : Finset (Fin n × Fin n)) :
    2 * JCenter {p} P =
      ∑ q ∈ P,
        ((if p.1 ≤ q.1 then (1 : ℚ) else 0) * (if p.2 ≤ q.2 then (1 : ℚ) else 0) +
          (1 - if p.1 ≤ q.1 then (1 : ℚ) else 0) * (1 - if p.2 ≤ q.2 then (1 : ℚ) else 0)) := by
  classical
  rw [two_mul_JCenter_singleton_left, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hle : (p ≤ q) ↔ (p.1 ≤ q.1 ∧ p.2 ≤ q.2) := Prod.le_def
  have hsw : IsSouthWest q p ↔ (¬ p.1 ≤ q.1 ∧ ¬ p.2 ≤ q.2) := by
    simp only [isSouthWest_iff, not_le, Fin.lt_def]
  simp only [hle, hsw]
  by_cases h1 : p.1 ≤ q.1 <;> by_cases h2 : p.2 ≤ q.2 <;> simp [h1, h2]

/-- The alternating combination of the pairings of the four corners of a rectangle against a set
of marked squares, as a single sum over the marked squares. The two source corners
`(left, bottom)`, `(right, top)` enter with a plus sign and the two target corners
`(left, top)`, `(right, bottom)` with a minus sign, and the summand factors as a product of a
column difference and a row difference. -/
private theorem JCenter_corner_alternating (left right bottom top : Fin n)
    (P : Finset (Fin n × Fin n)) :
    JCenter {(left, bottom)} P + JCenter {(right, top)} P -
        (JCenter {(left, top)} P + JCenter {(right, bottom)} P) =
      ∑ q ∈ P,
        ((if left ≤ q.1 then (1 : ℚ) else 0) - (if right ≤ q.1 then (1 : ℚ) else 0)) *
          ((if bottom ≤ q.2 then (1 : ℚ) else 0) - (if top ≤ q.2 then (1 : ℚ) else 0)) := by
  refine mul_left_cancel₀ (a := (2 : ℚ)) (by norm_num) ?_
  rw [mul_sub, mul_add, mul_add, two_mul_JCenter_singleton_left_eq_sum,
    two_mul_JCenter_singleton_left_eq_sum, two_mul_JCenter_singleton_left_eq_sum,
    two_mul_JCenter_singleton_left_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- Away from the row and column through `p`, the strict grid-point pairing agrees with the
center-shifted marking pairing. -/
private theorem J_singleton_left_eq_JCenter (p : Fin n × Fin n)
    (S : Finset (Fin n × Fin n))
    (hS : ∀ q ∈ S, q.1 ≠ p.1 ∧ q.2 ≠ p.2) : J {p} S = JCenter {p} S := by
  have hfilter :
      S.filter (fun q => IsSouthWest p q ∨ IsSouthWest q p) =
        S.filter (fun q => p ≤ q ∨ IsSouthWest q p) := by
    apply Finset.filter_congr
    intro q hq
    constructor
    · rintro (hpq | hqp)
      · exact Or.inl (Prod.le_def.mpr ⟨hpq.1.le, hpq.2.le⟩)
      · exact Or.inr hqp
    · rintro (hpq | hqp)
      · obtain ⟨hcol, hrow⟩ := hS q hq
        have hcolval : p.1.val ≠ q.1.val := fun e => hcol (Fin.val_inj.mp e.symm)
        have hrowval : p.2.val ≠ q.2.val := fun e => hrow (Fin.val_inj.mp e.symm)
        exact Or.inl ⟨lt_of_le_of_ne hpq.1 hcolval, lt_of_le_of_ne hpq.2 hrowval⟩
      · exact Or.inr hqp
  rw [J_singleton_left, JCenter_singleton_left, hfilter]

/-- The alternating combination of the `J`-pairings of the four corners of a rectangle against a
set of grid points that avoids all four sides of the rectangle. Off the four sides every strict
comparison against a side agrees with the corresponding weak one, so the sum takes the same shape
as for the pairing against markings. -/
private theorem J_corner_alternating (left right bottom top : Fin n)
    (S : Finset (Fin n × Fin n))
    (hS : ∀ q ∈ S, q.1 ≠ left ∧ q.1 ≠ right ∧ q.2 ≠ bottom ∧ q.2 ≠ top) :
    J {(left, bottom)} S + J {(right, top)} S -
        (J {(left, top)} S + J {(right, bottom)} S) =
      ∑ q ∈ S,
        ((if left ≤ q.1 then (1 : ℚ) else 0) - (if right ≤ q.1 then (1 : ℚ) else 0)) *
          ((if bottom ≤ q.2 then (1 : ℚ) else 0) - (if top ≤ q.2 then (1 : ℚ) else 0)) := by
  rw [J_singleton_left_eq_JCenter (left, bottom) S fun q hq =>
      ⟨(hS q hq).1, (hS q hq).2.2.1⟩,
    J_singleton_left_eq_JCenter (right, top) S fun q hq =>
      ⟨(hS q hq).2.1, (hS q hq).2.2.2⟩,
    J_singleton_left_eq_JCenter (left, top) S fun q hq =>
      ⟨(hS q hq).1, (hS q hq).2.2.2⟩,
    J_singleton_left_eq_JCenter (right, bottom) S fun q hq =>
      ⟨(hS q hq).2.1, (hS q hq).2.2.1⟩]
  exact JCenter_corner_alternating left right bottom top S

/-- For distinct grid coordinates the two weak comparisons are the wrapping indicator and its
complement. -/
private theorem ite_le_of_ne {a b : Fin n} (h : a ≠ b) :
    (if b ≤ a then (1 : ℚ) else 0) = (if b.val < a.val then (1 : ℚ) else 0) ∧
      (if a ≤ b then (1 : ℚ) else 0) = 1 - (if b.val < a.val then (1 : ℚ) else 0) := by
  have hne : a.val ≠ b.val := fun e => h (Fin.val_inj.mp e)
  constructor <;> simp only [Fin.le_def] <;> split_ifs <;>
    first | (exfalso; omega) | norm_num

/-- The difference of the indicators of the two side comparisons is the indicator of the
half-open arc between them, corrected by one when the arc wraps around the torus. -/
private theorem sub_ite_le_eq_sub_ite_mem_cIco (a b x : Fin n) :
    (if a ≤ x then (1 : ℚ) else 0) - (if b ≤ x then (1 : ℚ) else 0) =
      (if x ∈ Grid.cIco a b then (1 : ℚ) else 0) - (if b.val < a.val then (1 : ℚ) else 0) := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · simp only [Grid.mem_cIco_iff_of_left_lt_right h, Fin.le_def]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · have hab : a = b := Fin.val_inj.mp h
    subst hab
    simp
  · simp only [Grid.mem_cIco_iff_of_right_lt_left h, Fin.le_def]
    split_ifs <;> first | (exfalso; omega) | norm_num

end GridPoint

namespace GridState

variable {n : ℕ}

/-- A grid state meets a product of a set of columns and a set of rows in the occupied squares
lying in that product. -/
private theorem sum_ite_mem_product (w : GridState n) (C D : Finset (Fin n)) :
    ∑ q ∈ w.pointSet, (if q.1 ∈ C then (1 : ℚ) else 0) * (if q.2 ∈ D then (1 : ℚ) else 0) =
      ((w.pointSet ∩ C ×ˢ D).card : ℚ) := by
  classical
  have hprod : ∀ q : Fin n × Fin n,
      (if q.1 ∈ C then (1 : ℚ) else 0) * (if q.2 ∈ D then (1 : ℚ) else 0) =
        if q ∈ C ×ˢ D then (1 : ℚ) else 0 := by
    intro q
    by_cases hC : q.1 ∈ C <;> by_cases hD : q.2 ∈ D <;> simp [hC, hD, Finset.mem_product]
  simp only [hprod]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter]

end GridState

namespace GridRectangle

variable {n : ℕ}

/-- The sum, over the occupied squares of a grid state, of the product of the two side
differences of a toroidal rectangle. It counts the occupied squares the rectangle covers, up to a
correction that depends only on whether the rectangle wraps around the torus in each direction
and on how many columns and rows it covers. The correction does not mention the grid state, which
is what makes it cancel below. -/
private theorem sum_pointSet_side_product (R : GridRectangle n) (w : GridState n) :
    ∑ q ∈ w.pointSet,
        ((if R.left ≤ q.1 then (1 : ℚ) else 0) - (if R.right ≤ q.1 then (1 : ℚ) else 0)) *
          ((if R.bottom ≤ q.2 then (1 : ℚ) else 0) - (if R.top ≤ q.2 then (1 : ℚ) else 0)) =
      ((w.pointSet ∩ R.coveredSquares).card : ℚ) -
        (if R.top.val < R.bottom.val then (1 : ℚ) else 0) * (R.coveredColumns.card : ℚ) -
        (if R.right.val < R.left.val then (1 : ℚ) else 0) * (R.coveredRows.card : ℚ) +
        (if R.right.val < R.left.val then (1 : ℚ) else 0) *
          (if R.top.val < R.bottom.val then (1 : ℚ) else 0) * (n : ℚ) := by
  classical
  have expand : ∀ q : Fin n × Fin n,
      ((if R.left ≤ q.1 then (1 : ℚ) else 0) - (if R.right ≤ q.1 then (1 : ℚ) else 0)) *
          ((if R.bottom ≤ q.2 then (1 : ℚ) else 0) - (if R.top ≤ q.2 then (1 : ℚ) else 0)) =
        (if q.1 ∈ R.coveredColumns then (1 : ℚ) else 0) *
            (if q.2 ∈ R.coveredRows then (1 : ℚ) else 0) -
          (if R.top.val < R.bottom.val then (1 : ℚ) else 0) *
            (if q.1 ∈ R.coveredColumns then (1 : ℚ) else 0) -
          (if R.right.val < R.left.val then (1 : ℚ) else 0) *
            (if q.2 ∈ R.coveredRows then (1 : ℚ) else 0) +
          (if R.right.val < R.left.val then (1 : ℚ) else 0) *
            (if R.top.val < R.bottom.val then (1 : ℚ) else 0) := by
    intro q
    rw [GridPoint.sub_ite_le_eq_sub_ite_mem_cIco, GridPoint.sub_ite_le_eq_sub_ite_mem_cIco]
    simp only [mem_coveredColumns, mem_coveredRows]
    ring
  simp only [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_const, GridState.sum_ite_mem_columns,
    GridState.sum_ite_mem_rows, GridState.sum_ite_mem_product, GridState.card_pointSet,
    nsmul_eq_mul, coveredSquares_def]
  ring

/-- The four-corner alternating pairing of a toroidal rectangle against the occupied squares of a
grid state counts the occupied squares the rectangle covers, up to the wrapping correction of
`GridRectangle.sum_pointSet_side_product`. -/
private theorem JCenter_corner_alternating_pointSet (R : GridRectangle n) (w : GridState n) :
    GridPoint.JCenter {(R.left, R.bottom)} w.pointSet +
          GridPoint.JCenter {(R.right, R.top)} w.pointSet -
        (GridPoint.JCenter {(R.left, R.top)} w.pointSet +
          GridPoint.JCenter {(R.right, R.bottom)} w.pointSet) =
      ((w.pointSet ∩ R.coveredSquares).card : ℚ) -
        (if R.top.val < R.bottom.val then (1 : ℚ) else 0) * (R.coveredColumns.card : ℚ) -
        (if R.right.val < R.left.val then (1 : ℚ) else 0) * (R.coveredRows.card : ℚ) +
        (if R.right.val < R.left.val then (1 : ℚ) else 0) *
          (if R.top.val < R.bottom.val then (1 : ℚ) else 0) * (n : ℚ) := by
  rw [GridPoint.JCenter_corner_alternating]
  exact R.sum_pointSet_side_product w

end GridRectangle

namespace GridRectangleBetween

variable {n : ℕ} {x y : GridState n} (R : GridRectangleBetween x y)

/-- A square shared by the source and target of a rectangle move avoids all four sides of the
rectangle: the two side columns carry the four corners, and the two side rows are the rows the
source state uses on those columns. -/
private theorem avoids_sides_of_mem_pointSet_inter {p : Fin n × Fin n}
    (hp : p ∈ x.pointSet ∩ y.pointSet) :
    p.1 ≠ R.left ∧ p.1 ≠ R.right ∧ p.2 ≠ R.bottom ∧ p.2 ≠ R.top := by
  obtain ⟨hx, hleft, hright⟩ := (R.mem_pointSet_inter_iff p).mp hp
  have hxp : x p.1 = p.2 := (GridState.mem_pointSet x p).mp hx
  refine ⟨hleft, hright, fun h => hleft ?_, fun h => hright ?_⟩
  · exact x.toPerm.injective (hxp.trans (h.trans R.bottom_def))
  · exact x.toPerm.injective (hxp.trans (h.trans R.top_def))

/-- A sum over the source state's occupied squares splits off the two source corners of a
rectangle move, leaving the sum over the squares shared with the target. -/
private theorem sum_pointSet_eq (f : Fin n × Fin n → ℚ) :
    ∑ q ∈ x.pointSet, f q =
      f (R.left, R.bottom) + f (R.right, R.top) + ∑ q ∈ x.pointSet ∩ y.pointSet, f q := by
  have hmem : (R.left, R.bottom) ∉ insert (R.right, R.top) (x.pointSet ∩ y.pointSet) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨fun h => R.left_ne_right (Prod.ext_iff.mp h).1, R.left_bottom_notMem_inter⟩
  conv_lhs => rw [R.source_pointSet_eq]
  rw [Finset.sum_insert hmem, Finset.sum_insert R.right_top_notMem_inter, add_assoc]

/-- A sum over the shared squares of a rectangle move is the sum over the source state's squares
with the two source corners removed. -/
private theorem sum_pointSet_inter_eq (f : Fin n × Fin n → ℚ) :
    ∑ q ∈ x.pointSet ∩ y.pointSet, f q =
      (∑ q ∈ x.pointSet, f q) - f (R.left, R.bottom) - f (R.right, R.top) := by
  rw [R.sum_pointSet_eq f]
  ring

/-- An empty rectangle covers exactly one occupied square of its source state, its lower-left
corner: any other covered occupied square would lie strictly inside. -/
private theorem pointSet_inter_coveredSquares (hR : R.IsEmpty) :
    x.pointSet ∩ R.toGridRectangle.coveredSquares = {(R.left, R.bottom)} := by
  ext p
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hsq⟩
    have hxp : x p.1 = p.2 := (GridState.mem_pointSet x p).mp hx
    by_contra hne
    have h1 : p.1 ≠ R.left := by
      intro h
      exact hne (Prod.ext h (by simpa only [h, ← R.bottom_def] using hxp.symm))
    have h2 : p.2 ≠ R.bottom := fun h =>
      h1 (x.toPerm.injective (hxp.trans (h.trans R.bottom_def)))
    rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows] at hsq
    exact Finset.disjoint_left.mp hR
      ((R.toGridRectangle.mem_interior p).mpr
        ⟨Grid.mem_cIoo_of_mem_cIco hsq.1 h1, Grid.mem_cIoo_of_mem_cIco hsq.2 h2⟩) hx
  · rintro rfl
    refine ⟨R.left_bottom_mem_source, ?_⟩
    rw [GridRectangle.mem_coveredSquares, GridRectangle.mem_coveredColumns,
      GridRectangle.mem_coveredRows]
    exact ⟨Grid.left_mem_cIco R.left_ne_right,
      Grid.left_mem_cIco R.bottom_ne_top⟩

/-- The `J`-pairing of the two source corners of a rectangle against each other, minus that of
the two target corners: it records only how the rectangle wraps around the torus. -/
private theorem J_corner_corner :
    GridPoint.J {(R.left, R.bottom)} {(R.right, R.top)} -
        GridPoint.J {(R.left, R.top)} {(R.right, R.bottom)} =
      (1 - 2 * (if R.right.val < R.left.val then (1 : ℚ) else 0)) *
        (1 - 2 * (if R.top.val < R.bottom.val then (1 : ℚ) else 0)) / 2 := by
  have hLR : R.left.val ≠ R.right.val := fun e => R.left_ne_right (Fin.val_inj.mp e)
  have hBT : R.bottom.val ≠ R.top.val := fun e => R.bottom_ne_top (Fin.val_inj.mp e)
  simp only [GridPoint.J_singleton_singleton, GridPoint.isSouthWest_iff]
  split_ifs <;> first | (exfalso; omega) | (push_cast; ring)

/-- The alternating combination of the `J`-pairings of the four rectangle corners against the
squares its source and target states share, expressed using the source-state squares covered by
the rectangle. -/
private theorem J_corner_alternating_inter :
    GridPoint.J {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
          GridPoint.J {(R.right, R.top)} (x.pointSet ∩ y.pointSet) -
        (GridPoint.J {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
          GridPoint.J {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet)) =
      ((x.pointSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
            (if R.top.val < R.bottom.val then (1 : ℚ) else 0) *
              (R.toGridRectangle.coveredColumns.card : ℚ) -
            (if R.right.val < R.left.val then (1 : ℚ) else 0) *
              (R.toGridRectangle.coveredRows.card : ℚ) +
            (if R.right.val < R.left.val then (1 : ℚ) else 0) *
              (if R.top.val < R.bottom.val then (1 : ℚ) else 0) * (n : ℚ) -
          (1 - (if R.right.val < R.left.val then (1 : ℚ) else 0)) *
            (1 - (if R.top.val < R.bottom.val then (1 : ℚ) else 0)) -
          (if R.right.val < R.left.val then (1 : ℚ) else 0) *
            (if R.top.val < R.bottom.val then (1 : ℚ) else 0) := by
  have hside := R.toGridRectangle.sum_pointSet_side_product x
  rw [toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
    toGridRectangle_top] at hside
  have halt := GridPoint.J_corner_alternating R.left R.right R.bottom R.top
    (x.pointSet ∩ y.pointSet) fun q hq => R.avoids_sides_of_mem_pointSet_inter hq
  have hsplit := R.sum_pointSet_inter_eq fun q =>
    ((if R.left ≤ q.1 then (1 : ℚ) else 0) - (if R.right ≤ q.1 then (1 : ℚ) else 0)) *
      ((if R.bottom ≤ q.2 then (1 : ℚ) else 0) - (if R.top ≤ q.2 then (1 : ℚ) else 0))
  obtain ⟨hcw, hcw'⟩ := GridPoint.ite_le_of_ne R.left_ne_right
  obtain ⟨hrw, hrw'⟩ := GridPoint.ite_le_of_ne R.bottom_ne_top
  rw [halt, hsplit, hside]
  simp only [le_refl, ite_true, hcw, hcw', hrw, hrw']
  ring

/-- The Maslov grading change across a rectangle move, before naming the marking set: the
source-state term counts covered occupied squares, while the marking pairing counts covered
markings. -/
private theorem maslov_change_eq (w : GridState n) :
    2 * (GridPoint.J {(R.left, R.bottom)} {(R.right, R.top)} +
              GridPoint.J {(R.left, R.bottom)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.top)} (x.pointSet ∩ y.pointSet) -
            (GridPoint.J {(R.left, R.top)} {(R.right, R.bottom)} +
              GridPoint.J {(R.left, R.top)} (x.pointSet ∩ y.pointSet) +
              GridPoint.J {(R.right, R.bottom)} (x.pointSet ∩ y.pointSet))) -
        2 * (GridPoint.JCenter {(R.left, R.bottom)} w.pointSet +
              GridPoint.JCenter {(R.right, R.top)} w.pointSet -
            (GridPoint.JCenter {(R.left, R.top)} w.pointSet +
              GridPoint.JCenter {(R.right, R.bottom)} w.pointSet)) =
      2 * ((x.pointSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) - 1 -
        2 * ((w.pointSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  have hcenter := R.toGridRectangle.JCenter_corner_alternating_pointSet w
  rw [toGridRectangle_left, toGridRectangle_right, toGridRectangle_bottom,
    toGridRectangle_top] at hcenter
  linear_combination 2 * R.J_corner_corner + 2 * R.J_corner_alternating_inter - 2 * hcenter

end GridRectangleBetween

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) {x y : GridState n}

/-- The Alexander grading change across a rectangle move is the number of `X`-markings in the
squares the rectangle covers minus the number of `O`-markings there.

This is the closed form of `GridDiagram.alexander_change_rectangle`: the corner pairings evaluate
to marking counts, and the corrections recording how the rectangle wraps around the torus are the
same for the two marking sets, so they cancel. -/
theorem alexander_sub_alexander_eq_card_sub_card (R : GridRectangleBetween x y) :
    G.alexander x - G.alexander y =
      ((G.XSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) -
        ((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  have hX := R.toGridRectangle.JCenter_corner_alternating_pointSet G.X
  have hO := R.toGridRectangle.JCenter_corner_alternating_pointSet G.O
  rw [GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top] at hX hO
  rw [G.alexander_change_rectangle R, XSet, OSet, hX, hO]
  ring

/-- The `O`-Maslov grading change across any rectangle move is twice the number of covered
source-state squares, minus one, minus twice the number of covered `O`-markings. -/
theorem maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card
    (R : GridRectangleBetween x y) :
    G.maslovO x - G.maslovO y =
      2 * ((x.pointSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) - 1 -
        2 * ((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  rw [G.maslovO_change_rectangle R, OSet]
  exact R.maslov_change_eq G.O

/-- The `X`-Maslov grading change across any rectangle move is twice the number of covered
source-state squares, minus one, minus twice the number of covered `X`-markings. -/
theorem maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card
    (R : GridRectangleBetween x y) :
    G.maslovX x - G.maslovX y =
      2 * ((x.pointSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) - 1 -
        2 * ((G.XSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  rw [G.maslovX_change_rectangle R, XSet]
  exact R.maslov_change_eq G.X

/-- The `O`-Maslov grading change across an *empty* rectangle move is one minus twice the number
of `O`-markings in the squares the rectangle covers.

Unlike the Alexander formula, this one needs the rectangle to be empty: the source state's
occupied squares inside the rectangle would otherwise contribute. -/
theorem maslovO_sub_maslovO_eq_one_sub_two_mul_card (R : GridRectangleBetween x y)
    (hR : R.IsEmpty) :
    G.maslovO x - G.maslovO y =
      1 - 2 * ((G.OSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  rw [G.maslovO_sub_maslovO_eq_two_mul_card_sub_one_sub_two_mul_card R,
    R.pointSet_inter_coveredSquares hR, Finset.card_singleton, Nat.cast_one]
  ring

/-- The `X`-Maslov grading change across an empty rectangle move is one minus twice the number of
`X`-markings in the squares the rectangle covers. -/
theorem maslovX_sub_maslovX_eq_one_sub_two_mul_card (R : GridRectangleBetween x y)
    (hR : R.IsEmpty) :
    G.maslovX x - G.maslovX y =
      1 - 2 * ((G.XSet ∩ R.toGridRectangle.coveredSquares).card : ℚ) := by
  rw [G.maslovX_sub_maslovX_eq_two_mul_card_sub_one_sub_two_mul_card R,
    R.pointSet_inter_coveredSquares hR, Finset.card_singleton, Nat.cast_one]
  ring

/-- An empty rectangle move whose squares carry no `O`-marking drops the `O`-Maslov grading by
exactly one. Disjointness from `coveredSquares` is stronger than the interior-based
`GridRectangle.AvoidsMarkings` predicate. Together with
`GridDiagram.alexander_eq_alexander_of_disjoint_coveredSquares`, this gives the Maslov part of
bidegree `(-1, 0)`. -/
theorem maslovO_sub_maslovO_eq_one_of_disjoint_coveredSquares (R : GridRectangleBetween x y)
    (hR : R.IsEmpty) (h : Disjoint R.toGridRectangle.coveredSquares G.OSet) :
    G.maslovO x - G.maslovO y = 1 := by
  have hO : G.OSet ∩ R.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp h.symm
  rw [G.maslovO_sub_maslovO_eq_one_sub_two_mul_card R hR, hO]
  norm_num

/-- An empty rectangle move whose covered squares carry no `X`-marking drops the `X`-Maslov
grading by exactly one. This square-disjointness is stronger than the interior-based
`GridRectangle.AvoidsMarkings` predicate. -/
theorem maslovX_sub_maslovX_eq_one_of_disjoint_coveredSquares (R : GridRectangleBetween x y)
    (hR : R.IsEmpty) (h : Disjoint R.toGridRectangle.coveredSquares G.XSet) :
    G.maslovX x - G.maslovX y = 1 := by
  have hX : G.XSet ∩ R.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp h.symm
  rw [G.maslovX_sub_maslovX_eq_one_sub_two_mul_card R hR, hX]
  norm_num

/-- A rectangle move whose covered squares carry no marking preserves the Alexander grading.
This square-disjointness is stronger than the interior-based `GridRectangle.AvoidsMarkings`
predicate. -/
theorem alexander_eq_alexander_of_disjoint_coveredSquares (R : GridRectangleBetween x y)
    (h : Disjoint R.toGridRectangle.coveredSquares (G.OSet ∪ G.XSet)) :
    G.alexander x = G.alexander y := by
  have hO : G.OSet ∩ R.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (h.mono_right Finset.subset_union_left).symm
  have hX : G.XSet ∩ R.toGridRectangle.coveredSquares = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (h.mono_right Finset.subset_union_right).symm
  have key := G.alexander_sub_alexander_eq_card_sub_card R
  rw [hO, hX] at key
  simp only [Finset.card_empty, Nat.cast_zero, sub_self] at key
  exact sub_eq_zero.mp key

/-- The Alexander gradings of two grid states joined by a rectangle differ by an integer, even
though the Alexander grading is a priori only rational. -/
theorem exists_int_alexander_sub_alexander (R : GridRectangleBetween x y) :
    ∃ m : ℤ, G.alexander x - G.alexander y = (m : ℚ) :=
  ⟨(G.XSet ∩ R.toGridRectangle.coveredSquares).card -
      (G.OSet ∩ R.toGridRectangle.coveredSquares).card, by
    rw [G.alexander_sub_alexander_eq_card_sub_card R]
    push_cast
    ring⟩

end GridDiagram

end TauCeti
