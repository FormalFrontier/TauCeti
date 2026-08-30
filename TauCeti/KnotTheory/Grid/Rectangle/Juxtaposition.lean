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

## Main results

The following results are in the `TauCeti.GridRectangle` namespace:

* `coveredSquares_union_eq_of_mem_cIoo`: the first L-shaped repartition identity.
* `coveredSquares_union_eq_of_mem_cIoo_complementary_col_cut`: the complementary column-cut
  orientation of the same identity.
* `prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo`: any multiplicative weight is
  preserved by the first repartition.
* `prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_complementary_col_cut`: any
  multiplicative weight is preserved by the complementary column-cut repartition.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping-rectangle case of the juxtaposition proof. The cut
follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ}

private theorem product_union_eq_union_product {s s' : Finset α} {t t' : Finset β}
    [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∪ (s ∪ s') ×ˢ t' = s' ×ˢ t' ∪ s ×ˢ (t ∪ t') := by
  rw [Finset.union_product, Finset.product_union]
  ac_rfl

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
  exact product_union_eq_union_product

/-- The complementary L-shaped repartition uses the same row cut, with `v` between `u` and `w`,
while in the column coordinate `c` lies between `a` and `b`. -/
theorem coveredSquares_union_eq_of_mem_cIoo_complementary_col_cut {a b c u v w : Fin n}
    (hcol : c ∈ Grid.cIoo a b) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares := by
  simp only [coveredSquares_def, coveredColumns_def, coveredRows_def]
  rw [← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hcol,
    ← Grid.cIco_union_cIco_eq_cIco_of_mem_cIoo hrow]
  simpa only [Finset.union_comm] using
    (product_union_eq_union_product
      (s := Grid.cIco a c) (s' := Grid.cIco c b)
      (t := Grid.cIco v w) (t' := Grid.cIco u v))

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
  have hleft : Disjoint
      ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares
      ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares :=
    (disjoint_coveredSquares_iff _ _).mpr (Or.inr (by
      simpa only [coveredRows_def] using Grid.disjoint_cIco_cIco_of_mem_cIoo hrow))
  have hright : Disjoint
      ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares
      ({ left := a, right := b, bottom := u, top := w } : GridRectangle n).coveredSquares :=
    (disjoint_coveredSquares_iff _ _).mpr (Or.inl (by
      simpa only [coveredColumns_def] using
        (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol).symm))
  rw [← Finset.prod_union hleft,
    coveredSquares_union_eq_of_mem_cIoo hcol hrow,
    Finset.prod_union hright]

/-- Recutting the complementary L-shaped domain preserves the product of any commutative weight
on its covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo_complementary_col_cut
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
  have hleft : Disjoint
      ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares
      ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares :=
    (disjoint_coveredSquares_iff _ _).mpr (Or.inr (by
      simpa only [coveredRows_def] using Grid.disjoint_cIco_cIco_of_mem_cIoo hrow))
  have hright : Disjoint
      ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares
      ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares :=
    (disjoint_coveredSquares_iff _ _).mpr (Or.inl (by
      simpa only [coveredColumns_def] using Grid.disjoint_cIco_cIco_of_mem_cIoo hcol))
  rw [← Finset.prod_union hleft,
    coveredSquares_union_eq_of_mem_cIoo_complementary_col_cut hcol hrow,
    Finset.prod_union hright]

end GridRectangle

end TauCeti
