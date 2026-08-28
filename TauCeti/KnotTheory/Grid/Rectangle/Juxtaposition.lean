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
The disjointness statements record that both displayed unions are honest partitions, not merely
equal unions with hidden overlap.

These identities use the square-centred, half-open domains counted by the unblocked grid
differential. They are the geometric step needed to show that the alternate decomposition
preserves `X`-avoidance and the product of the `O`-monomial weights in the one-common-side case.

## Main results

* `TauCeti.GridRectangle.coveredSquares_union_eq_of_mem_cIoo`: the first L-shaped
  repartition identity.
* `TauCeti.GridRectangle.coveredSquares_union_eq_of_mem_cIoo'`: the complementary orientation
  of the same identity.
* `TauCeti.GridRectangle.disjoint_coveredSquares_of_mem_cIoo`: the two pieces on each side of
  the first identity are disjoint.
* `TauCeti.GridRectangle.prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo`: any
  multiplicative weight is preserved by the repartition.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3, "The complexes and
`∂² = 0`", specifically the overlapping-rectangle case of the juxtaposition proof. The cut
follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 4.6.
-/

public section

namespace TauCeti

namespace GridRectangle

variable {n : ℕ}

/-- If `b` and `v` lie between the corresponding outer sides, the two indicated pairs of
rectangles are the two cuts of the same L-shaped set of squares. -/
theorem coveredSquares_union_eq_of_mem_cIoo {a b c u v w : Fin n}
    (hcol : b ∈ Grid.cIoo a c) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := b, bottom := u, top := w } : GridRectangle n).coveredSquares := by
  ext p
  simp only [Finset.mem_union, mem_coveredSquares, mem_coveredColumns, mem_coveredRows]
  have hcols := congrArg (fun s : Finset (Fin n) => p.1 ∈ s)
    (Grid.cIco_union_cIco_eq_of_mem_cIoo hcol)
  have hrows := congrArg (fun s : Finset (Fin n) => p.2 ∈ s)
    (Grid.cIco_union_cIco_eq_of_mem_cIoo hrow)
  simp only [Finset.mem_union] at hcols hrows
  tauto

/-- The complementary L-shaped repartition: here the second outer endpoint lies between the
first two in each coordinate. -/
theorem coveredSquares_union_eq_of_mem_cIoo' {a b c u v w : Fin n}
    (hcol : c ∈ Grid.cIoo a b) (hrow : v ∈ Grid.cIoo u w) :
    ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares ∪
        ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares =
      ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares ∪
        ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares := by
  ext p
  simp only [Finset.mem_union, mem_coveredSquares, mem_coveredColumns, mem_coveredRows]
  have hcols := congrArg (fun s : Finset (Fin n) => p.1 ∈ s)
    (Grid.cIco_union_cIco_eq_of_mem_cIoo hcol)
  have hrows := congrArg (fun s : Finset (Fin n) => p.2 ∈ s)
    (Grid.cIco_union_cIco_eq_of_mem_cIoo hrow)
  simp only [Finset.mem_union] at hcols hrows
  tauto

/-- In the first L-shaped repartition, the two rectangles on the left have disjoint covered
square domains. -/
theorem disjoint_coveredSquares_of_mem_cIoo {a b c u v w : Fin n}
    (hrow : v ∈ Grid.cIoo u w) :
    Disjoint
      ({ left := a, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares
      ({ left := a, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_coveredSquares] at hp hq
  have hp2 : p.2 ∈ Grid.cIco u v :=
    (mem_coveredRows _ p.2).mp hp.2
  have hq2 : p.2 ∈ Grid.cIco v w :=
    (mem_coveredRows _ p.2).mp hq.2
  exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hrow)) hp2 hq2

/-- In the first L-shaped repartition, the two rectangles on the right have disjoint covered
square domains. -/
theorem disjoint_coveredSquares_of_mem_cIoo_alt {a b c u v w : Fin n}
    (hcol : b ∈ Grid.cIoo a c) :
    Disjoint
      ({ left := b, right := c, bottom := v, top := w } : GridRectangle n).coveredSquares
      ({ left := a, right := b, bottom := u, top := w } : GridRectangle n).coveredSquares := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_coveredSquares] at hp hq
  have hp1 : p.1 ∈ Grid.cIco b c :=
    (mem_coveredColumns _ p.1).mp hp.1
  have hq1 : p.1 ∈ Grid.cIco a b :=
    (mem_coveredColumns _ p.1).mp hq.1
  exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol).symm) hp1 hq1

/-- In the complementary L-shaped repartition, the two alternate rectangles have disjoint
covered-square domains. -/
theorem disjoint_coveredSquares_of_mem_cIoo_alt' {a b c u v w : Fin n}
    (hcol : c ∈ Grid.cIoo a b) :
    Disjoint
      ({ left := a, right := c, bottom := u, top := w } : GridRectangle n).coveredSquares
      ({ left := c, right := b, bottom := u, top := v } : GridRectangle n).coveredSquares := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_coveredSquares] at hp hq
  have hp1 : p.1 ∈ Grid.cIco a c :=
    (mem_coveredColumns _ p.1).mp hp.1
  have hq1 : p.1 ∈ Grid.cIco c b :=
    (mem_coveredColumns _ p.1).mp hq.1
  exact (Finset.disjoint_left.mp (Grid.disjoint_cIco_cIco_of_mem_cIoo hcol)) hp1 hq1

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
  rw [← Finset.prod_union (disjoint_coveredSquares_of_mem_cIoo hrow),
    coveredSquares_union_eq_of_mem_cIoo hcol hrow,
    Finset.prod_union (disjoint_coveredSquares_of_mem_cIoo_alt hcol)]

/-- Recutting the complementary L-shaped domain preserves the product of any commutative weight
on its covered squares. -/
theorem prod_coveredSquares_mul_prod_coveredSquares_eq_of_mem_cIoo'
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
  rw [← Finset.prod_union (disjoint_coveredSquares_of_mem_cIoo hrow),
    coveredSquares_union_eq_of_mem_cIoo' hcol hrow,
    Finset.prod_union (disjoint_coveredSquares_of_mem_cIoo_alt' hcol)]

end GridRectangle

end TauCeti
