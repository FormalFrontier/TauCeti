/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.JFunction.Basic

/-!
# The grid `J`-function as a neighbor count

The ordered southwest count `GridPoint.I s t` and the symmetrized `J`-function are defined in
`JFunction.lean` as cardinalities of a filtered product of point sets. This file records their
fiberwise reading: `I s t` is the sum over the left points of the number of right points strictly
northeast of them, and dually over the right points. Specializing the left (or right) argument to
a singleton turns each `J`-pairing against a single grid square into a plain count of the strictly
comparable points of the other set.

These lemmas concern the state-against-state pairing `GridPoint.J` only. The corner terms of the
rectangle grading-change localizations (`Grading/Change.lean`) pair a corner against the `O`- and
`X`-marking sets, so they are terms of `GridPoint.JCentre` instead, the markings sitting at the
centres of their squares; a counting form for those is not recorded here.

## Main results

* `TauCeti.GridPoint.I_eq_sum_card_filter`, `TauCeti.GridPoint.I_eq_sum_card_filter_right`: the
  ordered southwest count as a sum of fiber counts over the left (resp. right) point set.
* `TauCeti.GridPoint.I_singleton_left`, `TauCeti.GridPoint.I_singleton_right`: the ordered
  southwest count against a single grid square, as the number of strictly northeast (resp.
  southwest) points of the other set.
* `TauCeti.GridPoint.JNum_singleton_left`,
  `TauCeti.GridPoint.JNum_singleton_left_eq_card`: the symmetrized numerator against a single
  square, as the two directed counts and as the single count of strictly comparable points.
* `TauCeti.GridPoint.J_singleton_left`, `TauCeti.GridPoint.two_mul_J_singleton_left`: the
  `J`-pairing against a single square is half the number of strictly comparable points, so twice
  it is that integer count.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.2,
"Gradings. The `J`-function, `M_O`, `M_X`, `A`; ... grading-change formulas across a rectangle."
The `J`-function is the symmetrized northeast/southwest point-pair count of Ozsváth--Stipsicz--
Szabó, *Grid Homology for Knots and Links*, Chapter 3.2.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The ordered southwest count `I s t` is the sum, over the left points `p ∈ s`, of the number of
points of `t` strictly northeast of `p`. -/
theorem I_eq_sum_card_filter (s t : Finset (Fin n × Fin n)) :
    I s t = ∑ p ∈ s, (t.filter fun q => IsSouthWest p q).card := by
  classical
  rw [I_def, Finset.card_filter, Finset.sum_product]
  exact Finset.sum_congr rfl fun p _ => (Finset.card_filter _ _).symm

/-- The ordered southwest count `I s t` is the sum, over the right points `q ∈ t`, of the number of
points of `s` strictly southwest of `q`. -/
theorem I_eq_sum_card_filter_right (s t : Finset (Fin n × Fin n)) :
    I s t = ∑ q ∈ t, (s.filter fun p => IsSouthWest p q).card := by
  classical
  rw [I_def, Finset.card_filter, Finset.sum_product_right]
  exact Finset.sum_congr rfl fun q _ => (Finset.card_filter _ _).symm

/-- The ordered southwest count of a single grid square against a point set `t` is the number of
points of `t` strictly northeast of it. -/
theorem I_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    I {p} t = (t.filter fun q => IsSouthWest p q).card := by
  rw [I_eq_sum_card_filter, Finset.sum_singleton]

/-- The ordered southwest count of a point set `s` against a single grid square is the number of
points of `s` strictly southwest of it. -/
theorem I_singleton_right (s : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    I s {p} = (s.filter fun q => IsSouthWest q p).card := by
  rw [I_eq_sum_card_filter_right, Finset.sum_singleton]

/-- The symmetrized numerator of the `J`-function against a single grid square splits into the two
directed counts: the points of `t` strictly northeast of the square and the points strictly
southwest of it. -/
theorem JNum_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    JNum {p} t =
      (t.filter fun q => IsSouthWest p q).card + (t.filter fun q => IsSouthWest q p).card := by
  rw [JNum_def, I_singleton_left, I_singleton_right]

/-- No point of a set is both strictly northeast and strictly southwest of a fixed grid square, so
the two directed neighbor sets are disjoint. -/
private theorem disjoint_filter_isSouthWest (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    Disjoint (t.filter fun q => IsSouthWest p q) (t.filter fun q => IsSouthWest q p) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  simp only [Finset.mem_filter] at hq hq'
  exact not_isSouthWest_swap hq.2 hq'.2

/-- The symmetrized numerator of the `J`-function against a single grid square is the number of
points of `t` strictly comparable to it: those either strictly northeast or strictly southwest. The
two directions never overlap, so the two counts combine into a single filter cardinality. -/
theorem JNum_singleton_left_eq_card (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    JNum {p} t = (t.filter fun q => IsSouthWest p q ∨ IsSouthWest q p).card := by
  rw [JNum_singleton_left, ← Finset.card_union_of_disjoint (disjoint_filter_isSouthWest p t),
    ← Finset.filter_or]

/-- The `J`-pairing of a single grid square against a point set `t` is half the number of points of
`t` strictly comparable to it. -/
theorem J_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    GridPoint.J {p} t =
      (((t.filter fun q => IsSouthWest p q ∨ IsSouthWest q p).card : ℕ) : ℚ) / 2 := by
  rw [J_def, JNum_singleton_left_eq_card]

/-- Twice the `J`-pairing of a single grid square against a point set `t` is the number of points
of `t` strictly comparable to it: in particular this pairing is a half-integer whose double is a
natural number. -/
theorem two_mul_J_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    2 * GridPoint.J {p} t = ((t.filter fun q => IsSouthWest p q ∨ IsSouthWest q p).card : ℚ) := by
  rw [J_singleton_left]
  ring

end GridPoint

end TauCeti
