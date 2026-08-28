/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import TauCeti.KnotTheory.Grid.Rectangle.Squares

/-!
# Juxtaposing toroidal grid rectangles

Two rectangles in a nondiagonal term of the grid differential square can share one corner.
Cutting their L-shaped union along its other internal edge gives the alternate two-rectangle
decomposition. This file proves the finite-domain identity behind that cut.

The one-dimensional input is that an interior point `b` cuts the clockwise half-open interval
from `a` to `c` into the disjoint intervals from `a` to `b` and from `b` to `c`. Applying this in
both coordinates gives two forms of the L-shaped identity for `GridRectangle.coveredSquares`.
The coordinate cuts and `GridRectangle.disjoint_coveredSquares_iff` ensure that both displayed
unions are honest partitions, not merely equal unions with hidden overlap.

These identities use the square-centred, half-open domains counted by the unblocked grid
differential. They are the geometric step needed to show that the alternate decomposition
preserves `X`-avoidance and the product of the `O`-monomial weights in the one-common-side case.
They do not yet apply to `GridRectangle.AvoidsMarkings`, which tests the open grid-line interior;
that predicate must first be aligned with the square-centred convention.

## Main results

The following results are in the `TauCeti.GridRectangle` namespace:

* `coveredSquares_union_eq_of_mem_cIoo`: the first L-shaped repartition identity.
* `coveredSquares_union_eq_of_mem_cIoo_complementary_column_cut`: the complementary column-cut
  orientation of the same identity.
* `coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column` and
  `coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column_row_swap`: the two orientations
  whose original rectangles share their terminal column.
* `prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo`: any multiplicative weight is
  preserved by the first repartition.
* `prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_complementary_column_cut`: any
  multiplicative weight is preserved by the complementary column-cut repartition.
* `prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_shared_terminal_column` and its
  row-swapped orientation: any multiplicative weight is preserved by the terminal-column
  repartitions.
* `disjoint_coveredSquares_of_mem_cIoo_columns` and
  `disjoint_coveredSquares_of_mem_cIoo_rows`: the coordinate-cut facts ensuring that every
  displayed union is disjoint.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping-rectangle case of the juxtaposition proof. The cut
follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ}

private theorem prod_mul_prod_eq_of_disjoint_of_union_eq {M : Type*} [CommMonoid M]
    [DecidableEq α] (f : α → M) {s₁ s₂ s₃ s₄ : Finset α} (h₁₂ : Disjoint s₁ s₂)
    (h₃₄ : Disjoint s₃ s₄) (hunion : s₁ ∪ s₂ = s₃ ∪ s₄) :
    (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x = (∏ x ∈ s₃, f x) * ∏ x ∈ s₄, f x := by
  rw [← Finset.prod_union h₁₂, hunion, Finset.prod_union h₃₄]

/-- If `b` and `v` lie between the corresponding outer sides, the two indicated pairs of
rectangles are the two cuts of the same L-shaped set of squares. -/
theorem coveredSquares_union_eq_of_mem_cIoo {a b c u v w : Fin n}
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := b, bottom := u, top := w } : GridRectangle n).coveredSquares := by
  simp only [coveredSquares_def, coveredColumns_def, coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  simp only [Finset.union_product, Finset.product_union]
  ac_rfl

/-- If `v` lies between `u` and `w` and `c` lies between `a` and `b`, the L-shape
`[a,b) × [u,v) ∪ [a,c) × [v,w)` recuts as
`[a,c) × [u,w) ∪ [c,b) × [u,v)`. Here the column cut point is a side of the first
rectangle rather than of the second. -/
theorem coveredSquares_union_eq_of_mem_cIoo_complementary_column_cut {a b c u v w : Fin n}
    (hcol : c ∈ Grid.cIoo a b) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares := by
  simp only [coveredSquares_def, coveredColumns_def, coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  simp only [Finset.union_product, Finset.product_union]
  ac_rfl

/-- If the original rectangles share their terminal column and their rows meet in cyclic order,
the resulting L-shape can be recut along the other internal column edge. -/
theorem coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column {a b c u v w : Fin n}
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := b, right := c, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := a, right := b, bottom := v, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := b, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares := by
  simp only [coveredSquares_def, coveredColumns_def, coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  simp only [Finset.union_product, Finset.product_union]
  ac_rfl

/-- The row-swapped orientation of
`coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column`. -/
theorem coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column_row_swap
    {a b c u v w : Fin n} (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := u, top := v } : GridRectangle n).coveredSquares =
      ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := b, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares := by
  simp only [coveredSquares_def, coveredColumns_def, coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  simp only [Finset.union_product, Finset.product_union]
  ac_rfl

/-- Recutting the first L-shaped domain preserves the product of any commutative weight on its
covered squares. In the unblocked differential, specializing the weight to the variables of the
covered `O`-markings gives preservation of the product of rectangle monomials. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo
    {a b c u v w : Fin n} {M : Type*} [CommMonoid M] (f : Fin n × Fin n → M)
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    (∏ p ∈ ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares,
        f p) *
        ∏ p ∈ ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares,
          f p =
      (∏ p ∈ ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares,
          f p) *
        ∏ p ∈ ({ left := a, right := b, bottom := u, top := w } : GridRectangle n).coveredSquares,
          f p := by
  exact prod_mul_prod_eq_of_disjoint_of_union_eq f
    (disjoint_coveredSquares_of_mem_cIoo_rows hrow)
    (disjoint_coveredSquares_of_mem_cIoo_columns hcol).symm
    (coveredSquares_union_eq_of_mem_cIoo hcol hrow)

/-- Recutting the complementary L-shaped domain preserves the product of any commutative weight
on its covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_complementary_column_cut
    {a b c u v w : Fin n} {M : Type*} [CommMonoid M] (f : Fin n × Fin n → M)
    (hcol : c ∈ Grid.cIoo a b) (hrow : v ∈ Grid.cIoo u w) :
    (∏ p ∈ ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares,
        f p) *
        ∏ p ∈ ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares,
          f p =
      (∏ p ∈ ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares,
          f p) *
        ∏ p ∈ ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares,
          f p := by
  exact prod_mul_prod_eq_of_disjoint_of_union_eq f
    (disjoint_coveredSquares_of_mem_cIoo_rows hrow)
    (disjoint_coveredSquares_of_mem_cIoo_columns hcol)
    (coveredSquares_union_eq_of_mem_cIoo_complementary_column_cut hcol hrow)

/-- Recutting an L-shaped domain whose original rectangles share their terminal column preserves
the product of any commutative weight on its covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_shared_terminal_column
    {a b c u v w : Fin n} {M : Type*} [CommMonoid M] (f : Fin n × Fin n → M)
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    (∏ p ∈ ({ left := b, right := c, bottom := u, top := v } : GridRectangle n).coveredSquares,
        f p) *
        ∏ p ∈ ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares,
          f p =
      (∏ p ∈ ({ left := a, right := b, bottom := v, top := w } : GridRectangle n).coveredSquares,
          f p) *
        ∏ p ∈ ({ left := b, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares,
          f p := by
  exact prod_mul_prod_eq_of_disjoint_of_union_eq f
    (disjoint_coveredSquares_of_mem_cIoo_rows hrow)
    (disjoint_coveredSquares_of_mem_cIoo_columns hcol)
    (coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column hcol hrow)

/-- The row-swapped orientation of
`prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_shared_terminal_column`. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_shared_terminal_column_row_swap
    {a b c u v w : Fin n} {M : Type*} [CommMonoid M] (f : Fin n × Fin n → M)
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    (∏ p ∈ ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares,
        f p) *
        ∏ p ∈ ({ left := a, right := c, bottom := u, top := v } : GridRectangle n).coveredSquares,
          f p =
      (∏ p ∈ ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares,
          f p) *
        ∏ p ∈ ({ left := b, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares,
          f p := by
  exact prod_mul_prod_eq_of_disjoint_of_union_eq f
    (disjoint_coveredSquares_of_mem_cIoo_rows hrow).symm
    (disjoint_coveredSquares_of_mem_cIoo_columns hcol)
    (coveredSquares_union_eq_of_mem_cIoo_shared_terminal_column_row_swap hcol hrow)

end GridRectangle

end TauCeti
