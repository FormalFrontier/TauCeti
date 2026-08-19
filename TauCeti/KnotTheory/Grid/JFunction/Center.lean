/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import TauCeti.KnotTheory.Grid.JFunction.Basic

/-!
# Pairing grid points against markings at the centres of their squares

The `J`-function of `JFunction/Basic.lean` compares two sets of grid points with the strict
southwest relation. The Maslov and Alexander gradings, however, pair a *grid state*, which
occupies grid points, against the `O`- and `X`-*markings*, which sit at the **centres** of
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

## Main definitions

* `TauCeti.GridPoint.ICenter`: the ordered count of pairs of a grid point and a marked square with
  the point southwest of the centre of the square, that is, `GridPoint.Icount` at the weak product
  order.
* `TauCeti.GridPoint.JNumCenter`, `TauCeti.GridPoint.JCenter`: the symmetrized numerator and the
  rational-valued pairing of a set of grid points against a set of marked squares.
* `TauCeti.GridDiagram.JO`, `TauCeti.GridDiagram.JX`: the pairings of a grid state against the
  `O`- and `X`-markings of a grid diagram.

## Main results

* `TauCeti.GridPoint.ICenter_graph_eq_card`, `TauCeti.GridState.JNumCenter_pointSet_eq_card`,
  `TauCeti.GridDiagram.JO_eq_card`, `TauCeti.GridDiagram.JX_eq_card`: the pairings as
  column-index counts.
* `TauCeti.GridPoint.card_filter_le_eq_card_filter_lt_add`,
  `TauCeti.GridState.ICenter_self_pointSet_eq`: weakening both comparisons of a column-pair count
  along an injective row assignment, in particular pairing a grid state against the squares it
  occupies, adds exactly the `n` diagonal pairs to the strict count.
* `TauCeti.GridPoint.JCenter_insert_left`, `TauCeti.GridPoint.JCenter_union_left`: the pairing is
  additive in the grid points, which is what localizes a grading change to the corners of a
  rectangle.

## References

This supplies a prerequisite for `CombinatorialHeegaardFloer/README.md` in TauCetiRoadmap,
Lane G.2, "Gradings. The `J`-function, `M_O`, `M_X`, `A`; integer-valuedness of `A`;
grading-change formulas across a rectangle." The convention that the markings sit at the centres
of their squares while a grid state sits on the grid lines is that of Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 3.2.
-/

public section

namespace TauCeti

namespace GridPoint

variable {n : ℕ}

/-- The ordered count of pairs `(p, q) ∈ s ×ˢ t` with `p` southwest of the centre of the square
`q`. The left argument holds grid points and the right argument names marked squares; the marking
of the square named by `q` sits at `q + (1/2, 1/2)`, so a strict comparison against the marking is
the weak comparison `p ≤ q` of the product order. -/
def ICenter (s t : Finset (Fin n × Fin n)) : ℕ :=
  Icount (· ≤ ·) s t

/-- The southwest-of-centre count as the cardinality of a filtered product of point sets. -/
theorem ICenter_def (s t : Finset (Fin n × Fin n)) :
    ICenter s t =
      ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) => pq.1 ≤ pq.2).card :=
  by simpa only [ICenter] using Icount_def (· ≤ ·) s t

/-- The southwest-of-centre count is zero when there are no grid points. -/
@[simp]
theorem ICenter_empty_left (s : Finset (Fin n × Fin n)) : ICenter ∅ s = 0 :=
  Icount_empty_left _ s

/-- The southwest-of-centre count is zero when there are no marked squares. -/
@[simp]
theorem ICenter_empty_right (s : Finset (Fin n × Fin n)) : ICenter s ∅ = 0 :=
  Icount_empty_right _ s

/-- The southwest-of-centre count of singletons records the single comparison. -/
@[simp]
theorem ICenter_singleton_singleton (p q : Fin n × Fin n) :
    ICenter {p} {q} = if p ≤ q then 1 else 0 :=
  Icount_singleton_singleton _ p q

/-- The southwest-of-centre count is additive in the grid points over disjoint unions. -/
theorem ICenter_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    ICenter (s₁ ∪ s₂) t = ICenter s₁ t + ICenter s₂ t :=
  Icount_union_left _ h

/-- The southwest-of-center count is additive in the marked squares over disjoint unions. -/
theorem ICenter_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    ICenter s (t₁ ∪ t₂) = ICenter s t₁ + ICenter s t₂ :=
  Icount_union_right _ h

/-- The southwest-of-centre count after inserting a fresh grid point. -/
theorem ICenter_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    ICenter (insert p s) t = ICenter {p} t + ICenter s t :=
  Icount_insert_left _ h

/-- The southwest-of-center count after inserting a fresh marked square. -/
theorem ICenter_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    ICenter s (insert p t) = ICenter s {p} + ICenter s t :=
  Icount_insert_right _ h

/-- The southwest-of-centre count is invariant under reflecting both point sets across the
diagonal. -/
theorem ICenter_image_swap (s t : Finset (Fin n × Fin n)) :
    ICenter (s.image Prod.swap) (t.image Prod.swap) = ICenter s t :=
  Icount_image_swap _ (fun _ _ => Prod.swap_le_swap) s t

/-- The southwest-of-centre count of two graph point sets is the number of column pairs `c ≤ d`
whose rows compare the same way. This graph-level statement does not require either row
assignment to be a permutation. -/
theorem ICenter_graph_eq_card (f g : Fin n → Fin n) :
    ICenter (Finset.univ.image fun c : Fin n => (c, f c))
        (Finset.univ.image fun c : Fin n => (c, g c)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ f p.1 ≤ g p.2).card := by
  rw [ICenter, Icount_graph_eq_card]
  exact congrArg Finset.card (Finset.filter_congr fun cd _ => by rw [Prod.mk_le_mk])

/-- Weakening both comparisons of a column-pair count along an injective row assignment adds
exactly the `n` diagonal pairs: a pair `c < d` contributes to both counts or to neither, and each
of the `n` columns contributes its own diagonal pair. -/
theorem card_filter_le_eq_card_filter_lt_add {f : Fin n → Fin n} (hf : Function.Injective f) :
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

/-- The symmetrized numerator of the pairing of a set of grid points against a set of marked
squares: the grid points southwest of a marking, plus the markings southwest of a grid point. -/
def JNumCenter (s t : Finset (Fin n × Fin n)) : ℕ :=
  ICenter s t + I t s

/-- The numerator of the marking pairing as a sum of its two directed counts. -/
theorem JNumCenter_def (s t : Finset (Fin n × Fin n)) :
    JNumCenter s t = ICenter s t + I t s :=
  by simp only [JNumCenter]

/-- The numerator of the marking pairing vanishes when there are no grid points. -/
@[simp]
theorem JNumCenter_empty_left (t : Finset (Fin n × Fin n)) : JNumCenter ∅ t = 0 := by
  simp [JNumCenter_def]

/-- The numerator of the marking pairing vanishes when there are no marked squares. -/
@[simp]
theorem JNumCenter_empty_right (s : Finset (Fin n × Fin n)) : JNumCenter s ∅ = 0 := by
  simp [JNumCenter_def]

/-- The numerator of the marking pairing is additive in the grid points over disjoint unions. -/
theorem JNumCenter_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JNumCenter (s₁ ∪ s₂) t = JNumCenter s₁ t + JNumCenter s₂ t := by
  rw [JNumCenter_def, JNumCenter_def, JNumCenter_def, ICenter_union_left h, I_union_right h]
  ring

/-- The numerator of the marking pairing is additive in the marked squares over disjoint
unions. -/
theorem JNumCenter_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    JNumCenter s (t₁ ∪ t₂) = JNumCenter s t₁ + JNumCenter s t₂ := by
  rw [JNumCenter_def, JNumCenter_def, JNumCenter_def, ICenter_union_right h, I_union_left h]
  ring

/-- The numerator of the marking pairing after inserting a fresh grid point. -/
theorem JNumCenter_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JNumCenter (insert p s) t = JNumCenter {p} t + JNumCenter s t := by
  rw [← Finset.singleton_union, JNumCenter_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of the marking pairing after inserting a fresh marked square. -/
theorem JNumCenter_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    JNumCenter s (insert p t) = JNumCenter s {p} + JNumCenter s t := by
  rw [← Finset.singleton_union, JNumCenter_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of the marking pairing is invariant under reflecting both point sets across
the diagonal. -/
theorem JNumCenter_image_swap (s t : Finset (Fin n × Fin n)) :
    JNumCenter (s.image Prod.swap) (t.image Prod.swap) = JNumCenter s t := by
  rw [JNumCenter_def, JNumCenter_def, ICenter_image_swap, I_image_swap]

/-- The rational-valued pairing of a set of grid points against a set of marked squares. This is
the `J`-function of the grid, corrected for the half-unit offset of the markings. -/
def JCenter (s t : Finset (Fin n × Fin n)) : ℚ :=
  ((JNumCenter s t : ℕ) : ℚ) / 2

/-- The marking pairing is half its symmetrized numerator. -/
theorem JCenter_def (s t : Finset (Fin n × Fin n)) :
    JCenter s t = ((JNumCenter s t : ℕ) : ℚ) / 2 :=
  by simp only [JCenter]

/-- The marking pairing vanishes when there are no grid points. -/
@[simp]
theorem JCenter_empty_left (t : Finset (Fin n × Fin n)) : JCenter ∅ t = 0 := by
  simp [JCenter_def]

/-- The marking pairing vanishes when there are no marked squares. -/
@[simp]
theorem JCenter_empty_right (s : Finset (Fin n × Fin n)) : JCenter s ∅ = 0 := by
  simp [JCenter_def]

/-- The marking pairing is additive in the grid points over disjoint unions. -/
theorem JCenter_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JCenter (s₁ ∪ s₂) t = JCenter s₁ t + JCenter s₂ t := by
  rw [JCenter_def, JCenter_def, JCenter_def, JNumCenter_union_left h]
  push_cast
  ring

/-- The marking pairing is additive in the marked squares over disjoint unions. -/
theorem JCenter_union_right {s t₁ t₂ : Finset (Fin n × Fin n)} (h : Disjoint t₁ t₂) :
    JCenter s (t₁ ∪ t₂) = JCenter s t₁ + JCenter s t₂ := by
  rw [JCenter_def, JCenter_def, JCenter_def, JNumCenter_union_right h]
  push_cast
  ring

/-- The marking pairing after inserting a fresh grid point. -/
theorem JCenter_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JCenter (insert p s) t = JCenter {p} t + JCenter s t := by
  rw [← Finset.singleton_union, JCenter_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The marking pairing after inserting a fresh marked square. -/
theorem JCenter_insert_right {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ t) :
    JCenter s (insert p t) = JCenter s {p} + JCenter s t := by
  rw [← Finset.singleton_union, JCenter_union_right]
  exact Finset.disjoint_singleton_left.mpr h

/-- The marking pairing is invariant under reflecting both point sets across the diagonal. -/
theorem JCenter_image_swap (s t : Finset (Fin n × Fin n)) :
    JCenter (s.image Prod.swap) (t.image Prod.swap) = JCenter s t := by
  rw [JCenter_def, JCenter_def, JNumCenter_image_swap]

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The southwest-of-centre count of the point sets of two grid states, as a column-pair
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
column-pair count `GridPoint.card_filter_le_eq_card_filter_lt_add`. -/
theorem ICenter_self_pointSet_eq (x : GridState n) :
    GridPoint.ICenter x.pointSet x.pointSet = GridPoint.I x.pointSet x.pointSet + n := by
  rw [ICenter_pointSet_eq_card, I_self_pointSet_eq_card]
  exact GridPoint.card_filter_le_eq_card_filter_lt_add x.toPerm.injective

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The pairing of a grid state against the `O`-markings of a grid diagram. -/
@[expose] def JO (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet G.OSet

/-- `JO` is the marking pairing of a state against the `O`-markings. -/
@[simp]
theorem JO_def (x : GridState n) : GridDiagram.JO G x = GridPoint.JCenter x.pointSet G.OSet :=
  rfl

/-- The pairing of a grid state against the `X`-markings of a grid diagram. -/
@[expose] def JX (x : GridState n) : ℚ :=
  GridPoint.JCenter x.pointSet G.XSet

/-- `JX` is the marking pairing of a state against the `X`-markings. -/
@[simp]
theorem JX_def (x : GridState n) : GridDiagram.JX G x = GridPoint.JCenter x.pointSet G.XSet :=
  rfl

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
@[simp]
theorem JO_swapMarkings (x : GridState n) : G.swapMarkings.JO x = G.JX x :=
  rfl

/-- The marking swap exchanges the `X`-marking pairing with the `O`-marking pairing. -/
@[simp]
theorem JX_swapMarkings (x : GridState n) : G.swapMarkings.JX x = G.JO x :=
  rfl

end GridDiagram

end TauCeti
