/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.JFunction.Count

/-!
# Pairing grid points against markings at the centers of their squares

The `J`-function of `JFunction/Basic.lean` compares two sets of grid points with the strict
southwest relation. The Maslov and Alexander gradings, however, pair a *grid state*, which
occupies grid points, against the `O`- and `X`-*markings*, which sit at the **centers** of
squares. In the planar realization of a grid, the marking of the square named by the grid point
`q` sits at `q + (1/2, 1/2)`: half a unit northeast of `q`, and never on a grid line. So a grid
point `p` lies southwest of that marking exactly when `p ≤ q` in both coordinates, whereas the
marking lies southwest of `p` exactly when `q < p` in both coordinates. Only the first of the two
comparisons changes: this file records the weakened one and builds the state-against-markings
pairing out of it.

Writing `𝒥` for the resulting pairing, the gradings are
`M_O(x) = J(x, x) - 2 𝒥(x, 𝕆) + J(𝕆, 𝕆) + 1` and likewise for `M_X`, following
Ozsváth--Stipsicz--Szabó. Note that `𝒥` is genuinely asymmetric in its two arguments: the left
argument holds grid points and the right argument names squares, so there is no analogue of
`GridPoint.J_comm`. Marking-against-marking and state-against-state pairings need no correction,
since shifting *both* point sets by `(1/2, 1/2)` preserves every strict comparison; those keep
using `GridPoint.J`.

This file corrects the grading pairing only. The older `GridRectangle.AvoidsMarkings` predicate
still interprets marking indices using the open grid-line interior; aligning that Lane G.3
differential convention with square-centered markings is a separate rectangle correction.

## Main definitions

* `TauCeti.GridPoint.ICenter`: the ordered count of pairs of a grid point and a marked square with
  the point southwest of the center of the square, that is, `GridPoint.ICount` at the weak product
  order.
* `TauCeti.GridPoint.JNumCenter`, `TauCeti.GridPoint.JCenter`: the numerator and the
  rational-valued pairing of a set of grid points against a set of marked squares.
* `TauCeti.GridDiagram.JO`, `TauCeti.GridDiagram.JX`: the pairings of a grid state against the
  `O`- and `X`-markings of a grid diagram.

## Main results

* `TauCeti.GridPoint.ICenter_graph_eq_card`, `TauCeti.GridState.JNumCenter_pointSet_eq_card`,
  `TauCeti.GridDiagram.JO_eq_card`, `TauCeti.GridDiagram.JX_eq_card`: the pairings as
  column-index counts.
* `TauCeti.card_filter_le_eq_card_filter_lt_add_card_of_injective`,
  `TauCeti.GridState.ICenter_self_pointSet_eq_I_add_card`: weakening both comparisons of a
  column-pair count along an injective row assignment, in particular pairing a grid state against
  the squares it occupies, adds exactly the `n` diagonal pairs to the strict count.
* `TauCeti.GridPoint.JCenter_insert_pair_left`: the pairing is additive in the grid points, which
  is what localizes a grading change to the corners of a rectangle.

## References

This supplies a prerequisite for `CombinatorialHeegaardFloer/README.md` in TauCetiRoadmap,
Lane G.2, "Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`;
grading-change formulas across a rectangle." The convention that the markings sit at the centers
of their squares while a grid state sits on the grid lines is that of Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapters 3.1--3.2 and 4.1 for the placement convention, and
Chapter 4.3 for the grading pairing.

* [TauCeti pull request #3135](https://github.com/TauCetiProject/TauCeti/pull/3135),
  whose square-centered marking convention and rotation-noninvariance argument this correction
  follows.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The ordered count of pairs `(p, q) ∈ s ×ˢ t` with `p` southwest of the center of the square
`q`. The left argument holds grid points and the right argument names marked squares; the marking
of the square named by `q` sits at `q + (1/2, 1/2)`, so a strict comparison against the marking is
the weak comparison `p ≤ q` of the product order. -/
def ICenter (s t : Finset (Fin n × Fin n)) : ℕ :=
  ICount (· ≤ ·) s t

/-- The southwest-of-center count is the relation-parametric ordered count at the weak product
order. -/
theorem ICenter_eq_ICount (s t : Finset (Fin n × Fin n)) :
    ICenter s t = ICount (· ≤ ·) s t :=
  by simp only [ICenter]

/-- The southwest-of-center count of one grid point is its weakly northeast fiber. -/
theorem ICenter_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    ICenter {p} t = (t.filter fun q => p ≤ q).card :=
  ICount_singleton_left _ p t

/-- The southwest-of-center count against one marked square is its weakly southwest fiber. -/
theorem ICenter_singleton_right (s : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    ICenter s {p} = (s.filter fun q => q ≤ p).card :=
  ICount_singleton_right _ s p

/-- The southwest-of-center count of two graph point sets is the number of column pairs `c ≤ d`
whose rows compare the same way. This graph-level statement does not require either row
assignment to be a permutation. -/
theorem ICenter_graph_eq_card (f g : Fin n → Fin n) :
    ICenter (Finset.univ.image fun c : Fin n => (c, f c))
        (Finset.univ.image fun c : Fin n => (c, g c)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ f p.1 ≤ g p.2).card := by
  rw [ICenter, ICount_graph_eq_card]
  exact congrArg Finset.card (Finset.filter_congr fun cd _ => by rw [Prod.mk_le_mk])

end GridPoint

/-- Weakening both comparisons of a column-pair count along an injective row assignment adds
exactly the `n` diagonal pairs: a pair `c < d` contributes to both counts or to neither, and each
of the `n` columns contributes its own diagonal pair. -/
theorem card_filter_le_eq_card_filter_lt_add_card_of_injective {n : ℕ} {f : Fin n → Fin n}
    (hf : Function.Injective f) :
    (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ f p.1 ≤ f p.2).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 < f p.2).card + n := by
  classical
  have hsplit :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ f p.1 ≤ f p.2) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 < f p.2) ∪
          (Finset.univ : Finset (Fin n)).diag := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_diag]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨h, lt_of_le_of_ne h2 fun heq => (ne_of_lt h) (hf heq)⟩
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨le_of_lt h1, le_of_lt h2⟩
      · exact ⟨le_of_eq h, le_of_eq (congrArg f h)⟩
  have hdisj :
      Disjoint (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ f p.1 < f p.2)
        ((Finset.univ : Finset (Fin n)).diag) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_diag] at hq
    exact (ne_of_lt hp.2.1) hq.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.diag_card, Finset.card_univ,
    Fintype.card_fin]

namespace GridPoint

/-- The numerator of the pairing of a set of grid points against a set of marked squares: the
grid points southwest of a marking, plus the markings southwest of a grid point. -/
def JNumCenter (s t : Finset (Fin n × Fin n)) : ℕ :=
  JNumMixed (· ≤ ·) s t

/-- The numerator of the marking pairing is the relation-parametric numerator at the weak product
order. -/
theorem JNumCenter_eq_JNumMixed (s t : Finset (Fin n × Fin n)) :
    JNumCenter s t = JNumMixed (· ≤ ·) s t :=
  by simp only [JNumCenter]

/-- The numerator of the marking pairing as a sum of its two directed counts. -/
theorem JNumCenter_def (s t : Finset (Fin n × Fin n)) :
    JNumCenter s t = ICenter s t + I t s :=
  by rw [JNumCenter, JNumMixed_def, ICenter]

/-- The numerator of the marking pairing of a single grid point against marked squares is the
sum of the numbers of markings weakly northeast and strictly southwest of the point. -/
theorem JNumCenter_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    JNumCenter {p} t =
      (t.filter fun q => p ≤ q).card + (t.filter fun q => IsSouthWest q p).card := by
  rw [JNumCenter_def, ICenter_singleton_left, I_singleton_right]

/-- The two directed fibers in the numerator of the singleton marking pairing are disjoint. -/
private theorem disjoint_filter_le_isSouthWest (p : Fin n × Fin n)
    (t : Finset (Fin n × Fin n)) :
    Disjoint (t.filter fun q => p ≤ q) (t.filter fun q => IsSouthWest q p) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  simp only [Finset.mem_filter] at hq hq'
  exact (not_lt_of_ge (Fin.le_def.mp (Prod.mk_le_mk.mp hq.2).1)) hq'.2.1

/-- The numerator of the singleton marking pairing counts the marked squares weakly northeast or
strictly southwest of the grid point. -/
theorem JNumCenter_singleton_left_eq_card (p : Fin n × Fin n)
    (t : Finset (Fin n × Fin n)) :
    JNumCenter {p} t = (t.filter fun q => p ≤ q ∨ IsSouthWest q p).card := by
  rw [JNumCenter_singleton_left,
    ← Finset.card_union_of_disjoint (disjoint_filter_le_isSouthWest p t), ← Finset.filter_or]

/-- The numerator of the marking pairing against a single marked square is the sum of the
numbers of grid points weakly southwest and strictly northeast of the marking. -/
theorem JNumCenter_singleton_right (s : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    JNumCenter s {p} =
      (s.filter fun q => q ≤ p).card + (s.filter fun q => IsSouthWest p q).card := by
  rw [JNumCenter_def, ICenter_singleton_right, I_singleton_left]

/-- The numerator of the marking pairing on singleton sets records its two comparisons. -/
@[simp]
theorem JNumCenter_singleton_singleton (p q : Fin n × Fin n) :
    JNumCenter {p} {q} =
      (if p ≤ q then 1 else 0) + (if IsSouthWest q p then 1 else 0) := by
  rw [JNumCenter, JNumMixed_def, I, ICount_singleton_singleton,
    ICount_singleton_singleton]

/-- The numerator of the marking pairing is invariant under reflecting both point sets across
the diagonal. -/
theorem JNumCenter_image_swap (s t : Finset (Fin n × Fin n)) :
    JNumCenter (s.image Prod.swap) (t.image Prod.swap) = JNumCenter s t :=
  JNumMixed_image_swap _ (fun _ _ => Prod.swap_le_swap) s t

/-- The rational-valued pairing of a set of grid points against a set of marked squares. This is
the `J`-function of the grid, corrected for the half-unit offset of the markings. -/
def JCenter (s t : Finset (Fin n × Fin n)) : ℚ :=
  JMixed (· ≤ ·) s t

/-- The marking pairing is the relation-parametric rational pairing at the weak product order. -/
theorem JCenter_eq_JMixed (s t : Finset (Fin n × Fin n)) :
    JCenter s t = JMixed (· ≤ ·) s t :=
  by simp only [JCenter]

/-- The marking pairing is half its numerator. -/
theorem JCenter_def (s t : Finset (Fin n × Fin n)) :
    JCenter s t = ((JNumCenter s t : ℕ) : ℚ) / 2 :=
  by rw [JCenter, JMixed_def, JNumCenter]

/-- Twice the marking pairing is its integer numerator. -/
theorem two_mul_JCenter (s t : Finset (Fin n × Fin n)) :
    2 * JCenter s t = ((JNumCenter s t : ℕ) : ℚ) := by
  rw [JCenter_def, mul_div_cancel₀ _ (by simp)]

/-- The marking pairing of a single grid point against marked squares is half the number of
markings weakly northeast or strictly southwest of the point. -/
theorem JCenter_singleton_left (p : Fin n × Fin n) (t : Finset (Fin n × Fin n)) :
    JCenter {p} t =
      (((t.filter fun q => p ≤ q ∨ IsSouthWest q p).card : ℕ) : ℚ) / 2 := by
  rw [JCenter_def, JNumCenter_singleton_left_eq_card]

/-- Twice the singleton marking pairing is the number of marked squares weakly northeast or
strictly southwest of the grid point. -/
theorem two_mul_JCenter_singleton_left (p : Fin n × Fin n)
    (t : Finset (Fin n × Fin n)) :
    2 * JCenter {p} t = ((t.filter fun q => p ≤ q ∨ IsSouthWest q p).card : ℚ) := by
  rw [JCenter_singleton_left, mul_div_cancel₀ _ (by simp)]

/-- The marking pairing against a single marked square is half the sum of the numbers of grid
points weakly southwest and strictly northeast of the marking. -/
theorem JCenter_singleton_right (s : Finset (Fin n × Fin n)) (p : Fin n × Fin n) :
    JCenter s {p} =
      (((s.filter fun q => q ≤ p).card +
        (s.filter fun q => IsSouthWest p q).card : ℕ) : ℚ) / 2 := by
  rw [JCenter_def, JNumCenter_singleton_right]

/-- The marking pairing on singleton sets is half its two-comparison numerator. -/
@[simp]
theorem JCenter_singleton_singleton (p q : Fin n × Fin n) :
    JCenter {p} {q} =
      (((if p ≤ q then 1 else 0) + (if IsSouthWest q p then 1 else 0) : ℕ) : ℚ) / 2 := by
  rw [JCenter_def, JNumCenter_singleton_singleton]

/-- Splitting a two-point insertion out of the grid points of the marking pairing. -/
theorem JCenter_insert_pair_left {S P : Finset (Fin n × Fin n)} {a b : Fin n × Fin n}
    (hab : a ∉ insert b S) (hb : b ∉ S) :
    JCenter (insert a (insert b S)) P =
      JCenter {a} P + JCenter {b} P + JCenter S P := by
  simp only [JCenter_eq_JMixed]
  exact JMixed_insert_pair_left (· ≤ ·) hab hb

/-- The marking pairing is invariant under reflecting both point sets across the diagonal. -/
theorem JCenter_image_swap (s t : Finset (Fin n × Fin n)) :
    JCenter (s.image Prod.swap) (t.image Prod.swap) = JCenter s t :=
  JMixed_image_swap _ (fun _ _ => Prod.swap_le_swap) s t

/-- The combination of the strict self-pairings and the doubled marking pairing is the cast of an
integer expression on arbitrary point sets. -/
theorem J_sub_two_mul_JCenter_add_J_eq_intCast (s t : Finset (Fin n × Fin n)) :
    GridPoint.J s s - 2 * JCenter s t + GridPoint.J t t =
      (((I s s : ℤ) - (JNumCenter s t : ℤ) + (I t t : ℤ) : ℤ) : ℚ) := by
  rw [J_self, two_mul_JCenter, J_self]
  simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The southwest-of-center count of the point sets of two grid states, as a column-pair
count. -/
theorem ICenter_pointSet_eq_card (x y : GridState n) :
    GridPoint.ICenter x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).card := by
  rw [pointSet, pointSet, GridPoint.ICenter_graph_eq_card]

/-- The numerator of the marking pairing on two state point sets, as a sum of two column-index
counts. -/
theorem JNumCenter_pointSet_eq_card (x y : GridState n) :
    GridPoint.JNumCenter x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card := by
  rw [GridPoint.JNumCenter_def, ICenter_pointSet_eq_card, I_pointSet_eq_card]

/-- Pairing a grid state against the squares it occupies adds exactly the `n` diagonal pairs to
the strict southwest count: the row assignment of a grid state is injective, so this is the
column-pair count `TauCeti.card_filter_le_eq_card_filter_lt_add_card_of_injective`. -/
theorem ICenter_self_pointSet_eq_I_add_card (x : GridState n) :
    GridPoint.ICenter x.pointSet x.pointSet = GridPoint.I x.pointSet x.pointSet + n := by
  rw [ICenter_pointSet_eq_card, I_self_pointSet_eq_card]
  exact card_filter_le_eq_card_filter_lt_add_card_of_injective x.toPerm.injective

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The pairing of a grid state against the `O`-markings of a grid diagram. -/
def JO (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet G.OSet

/-- `JO` is the marking pairing of a state against the `O`-markings. -/
@[simp]
theorem JO_def (x : GridState n) : GridDiagram.JO G x = GridPoint.JCenter x.pointSet G.OSet :=
  by simp only [JO]

/-- The pairing of a grid state against the `X`-markings of a grid diagram. -/
def JX (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet G.XSet

/-- `JX` is the marking pairing of a state against the `X`-markings. -/
@[simp]
theorem JX_def (x : GridState n) : GridDiagram.JX G x = GridPoint.JCenter x.pointSet G.XSet :=
  by simp only [JX]

/-- The `O`-marking pairing as a column-index count. -/
theorem JO_eq_card (x : GridState n) :
    G.JO x =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ G.O p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < x p.2).card : ℕ) :
          ℚ) / 2 := by
  rw [JO_def, OSet, GridPoint.JCenter_def, GridState.JNumCenter_pointSet_eq_card]

/-- The `X`-marking pairing as a column-index count. -/
theorem JX_eq_card (x : GridState n) :
    G.JX x =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ G.X p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < x p.2).card : ℕ) :
          ℚ) / 2 := by
  rw [JX_def, XSet, GridPoint.JCenter_def, GridState.JNumCenter_pointSet_eq_card]

/-- `JO` is invariant under reflecting the diagram and state across the diagonal. -/
theorem JO_transpose (x : GridState n) :
    GridDiagram.JO G.transpose x.transpose = GridDiagram.JO G x := by
  rw [JO_def, JO_def, GridState.transpose_pointSet, transpose_OSet, GridPoint.JCenter_image_swap]

/-- `JX` is invariant under reflecting the diagram and state across the diagonal. -/
theorem JX_transpose (x : GridState n) :
    GridDiagram.JX G.transpose x.transpose = GridDiagram.JX G x := by
  rw [JX_def, JX_def, GridState.transpose_pointSet, transpose_XSet, GridPoint.JCenter_image_swap]

/-- The marking swap exchanges the `O`-marking pairing with the `X`-marking pairing. -/
theorem JO_swapMarkings (x : GridState n) : G.swapMarkings.JO x = G.JX x :=
  by rw [JO_def, JX_def, swapMarkings_OSet]

/-- The marking swap exchanges the `X`-marking pairing with the `O`-marking pairing. -/
theorem JX_swapMarkings (x : GridState n) : G.swapMarkings.JX x = G.JO x :=
  by rw [JX_def, JO_def, swapMarkings_XSet]

end GridDiagram

end TauCeti
