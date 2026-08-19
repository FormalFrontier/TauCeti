/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Prod
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

* `TauCeti.GridPoint.IsSouthWestOfCentre`: a grid point lies southwest of the centre of a given
  square.
* `TauCeti.GridPoint.ICentre`: the ordered count of such pairs.
* `TauCeti.GridPoint.JNumCentre`, `TauCeti.GridPoint.JCentre`: the symmetrized numerator and the
  rational-valued pairing of a set of grid points against a set of marked squares.
* `TauCeti.GridDiagram.JO`, `TauCeti.GridDiagram.JX`: the pairings of a grid state against the
  `O`- and `X`-markings of a grid diagram.

## Main results

* `TauCeti.GridPoint.ICentre_graph_eq_card`, `TauCeti.GridState.JNumCentre_pointSet_eq_card`,
  `TauCeti.GridDiagram.JO_eq_card`, `TauCeti.GridDiagram.JX_eq_card`: the pairings as
  column-index counts.
* `TauCeti.GridState.ICentre_self_pointSet_eq`: pairing a grid state against the squares it
  occupies adds exactly the `n` diagonal pairs to the strict count.
* `TauCeti.GridPoint.JCentre_insert_left`, `TauCeti.GridPoint.JCentre_union_left`: the pairing is
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

/-- A grid point lies southwest of the centre of the square named by `q` exactly when it is
weakly southwest of `q` itself: the marking of that square sits at `q + (1/2, 1/2)`, so a strict
comparison against the marking is a weak comparison against the naming grid point. -/
@[expose] def IsSouthWestOfCentre (p q : Fin n × Fin n) : Prop :=
  p.1 ≤ q.1 ∧ p.2 ≤ q.2

/-- Lying southwest of the centre of a square is decidable. -/
instance decidableIsSouthWestOfCentre (p q : Fin n × Fin n) :
    Decidable (IsSouthWestOfCentre p q) :=
  inferInstanceAs (Decidable (p.1 ≤ q.1 ∧ p.2 ≤ q.2))

/-- Lying southwest of the centre of a square, in coordinate form. -/
@[simp, grind =]
theorem isSouthWestOfCentre_iff (p q : Fin n × Fin n) :
    IsSouthWestOfCentre p q ↔ p.1 ≤ q.1 ∧ p.2 ≤ q.2 :=
  Iff.rfl

/-- A grid point lies southwest of the centre of its own square. -/
theorem isSouthWestOfCentre_self (p : Fin n × Fin n) : IsSouthWestOfCentre p p :=
  ⟨le_rfl, le_rfl⟩

/-- Lying strictly southwest of a grid point implies lying southwest of the centre of its
square. -/
theorem isSouthWestOfCentre_of_isSouthWest {p q : Fin n × Fin n} (h : IsSouthWest p q) :
    IsSouthWestOfCentre p q :=
  ⟨le_of_lt h.1, le_of_lt h.2⟩

/-- The ordered count of pairs `(p, q) ∈ s ×ˢ t` with `p` southwest of the centre of the square
`q`. The left argument holds grid points and the right argument names marked squares. -/
@[expose] def ICentre (s t : Finset (Fin n × Fin n)) : ℕ :=
  ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) =>
    IsSouthWestOfCentre pq.1 pq.2).card

/-- The southwest-of-centre count as the cardinality of a filtered product of point sets. -/
theorem ICentre_def (s t : Finset (Fin n × Fin n)) :
    ICentre s t =
      ((s ×ˢ t).filter fun pq : (Fin n × Fin n) × (Fin n × Fin n) =>
        IsSouthWestOfCentre pq.1 pq.2).card :=
  rfl

/-- The southwest-of-centre count is zero when there are no grid points. -/
@[simp]
theorem ICentre_empty_left (s : Finset (Fin n × Fin n)) : ICentre ∅ s = 0 := by
  simp [ICentre]

/-- The southwest-of-centre count is zero when there are no marked squares. -/
@[simp]
theorem ICentre_empty_right (s : Finset (Fin n × Fin n)) : ICentre s ∅ = 0 := by
  simp [ICentre]

/-- The southwest-of-centre count of singletons records the single comparison. -/
@[simp]
theorem ICentre_singleton_singleton (p q : Fin n × Fin n) :
    ICentre {p} {q} = if IsSouthWestOfCentre p q then 1 else 0 := by
  simp only [ICentre, Finset.singleton_product_singleton, Finset.filter_singleton]
  by_cases h : IsSouthWestOfCentre p q
  · simp only [h, ite_true, Finset.card_singleton]
  · simp only [h, ite_false, Finset.card_empty]

/-- The southwest-of-centre count is additive in the grid points over disjoint unions. -/
theorem ICentre_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    ICentre (s₁ ∪ s₂) t = ICentre s₁ t + ICentre s₂ t := by
  dsimp [ICentre]
  rw [Finset.union_product, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.disjoint_product.mpr (Or.inl h))

/-- The southwest-of-centre count after inserting a fresh grid point. -/
theorem ICentre_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    ICentre (insert p s) t = ICentre {p} t + ICentre s t := by
  rw [← Finset.singleton_union, ICentre_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- Lying southwest of the centre of a square is preserved by the diagonal reflection. -/
theorem isSouthWestOfCentre_swap (p q : Fin n × Fin n) :
    IsSouthWestOfCentre (Prod.swap p) (Prod.swap q) ↔ IsSouthWestOfCentre p q := by
  unfold IsSouthWestOfCentre
  exact and_comm

/-- The reflection map on pairs of grid squares is injective. -/
private theorem prodMap_swap_injective' :
    Function.Injective
      (Prod.map (Prod.swap (α := Fin n) (β := Fin n)) (Prod.swap (α := Fin n) (β := Fin n))) :=
  Prod.swap_injective.prodMap Prod.swap_injective

/-- The southwest-of-centre count is invariant under reflecting both point sets across the
diagonal. -/
theorem ICentre_image_swap (s t : Finset (Fin n × Fin n)) :
    ICentre (s.image Prod.swap) (t.image Prod.swap) = ICentre s t := by
  rw [ICentre_def, ICentre_def, ← Finset.prodMap_image_product Prod.swap Prod.swap s t,
    Finset.filter_image, Finset.card_image_of_injective _ prodMap_swap_injective']
  congr 1
  exact Finset.filter_congr fun pq _ => isSouthWestOfCentre_swap pq.1 pq.2

/-- The southwest-of-centre count of two graph point sets is the number of column pairs `c ≤ d`
whose rows compare the same way. This graph-level statement does not require either row
assignment to be a permutation. -/
theorem ICentre_graph_eq_card (f g : Fin n → Fin n) :
    ICentre (Finset.univ.image fun c : Fin n => (c, f c))
        (Finset.univ.image fun c : Fin n => (c, g c)) =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ f p.1 ≤ g p.2).card := by
  classical
  have hff : Function.Injective (fun c : Fin n => (c, f c)) :=
    fun _ _ h => congrArg Prod.fst h
  have hfg : Function.Injective (fun c : Fin n => (c, g c)) :=
    fun _ _ h => congrArg Prod.fst h
  rw [ICentre_def,
    ← Finset.prodMap_image_product (fun c : Fin n => (c, f c)) (fun c : Fin n => (c, g c)),
    Finset.filter_image, Finset.card_image_of_injective _ (hff.prodMap hfg),
    Finset.univ_product_univ]
  refine congrArg Finset.card (Finset.filter_congr fun cd _ => ?_)
  simp only [Prod.map_fst, Prod.map_snd, isSouthWestOfCentre_iff, Fin.le_def]

/-- The symmetrized numerator of the pairing of a set of grid points against a set of marked
squares: the grid points southwest of a marking, plus the markings southwest of a grid point. -/
@[expose] def JNumCentre (s t : Finset (Fin n × Fin n)) : ℕ :=
  ICentre s t + I t s

/-- The numerator of the marking pairing as a sum of its two directed counts. -/
theorem JNumCentre_def (s t : Finset (Fin n × Fin n)) :
    JNumCentre s t = ICentre s t + I t s :=
  rfl

/-- The numerator of the marking pairing vanishes when there are no grid points. -/
@[simp]
theorem JNumCentre_empty_left (t : Finset (Fin n × Fin n)) : JNumCentre ∅ t = 0 := by
  simp [JNumCentre]

/-- The numerator of the marking pairing is additive in the grid points over disjoint unions. -/
theorem JNumCentre_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JNumCentre (s₁ ∪ s₂) t = JNumCentre s₁ t + JNumCentre s₂ t := by
  rw [JNumCentre, JNumCentre, JNumCentre, ICentre_union_left h, I_union_right h]
  ring

/-- The numerator of the marking pairing after inserting a fresh grid point. -/
theorem JNumCentre_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JNumCentre (insert p s) t = JNumCentre {p} t + JNumCentre s t := by
  rw [← Finset.singleton_union, JNumCentre_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The numerator of the marking pairing is invariant under reflecting both point sets across
the diagonal. -/
theorem JNumCentre_image_swap (s t : Finset (Fin n × Fin n)) :
    JNumCentre (s.image Prod.swap) (t.image Prod.swap) = JNumCentre s t := by
  rw [JNumCentre, JNumCentre, ICentre_image_swap, I_image_swap]

/-- The rational-valued pairing of a set of grid points against a set of marked squares. This is
the `J`-function of the grid, corrected for the half-unit offset of the markings. -/
@[expose] def JCentre (s t : Finset (Fin n × Fin n)) : ℚ :=
  ((JNumCentre s t : ℕ) : ℚ) / 2

/-- The marking pairing is half its symmetrized numerator. -/
theorem JCentre_def (s t : Finset (Fin n × Fin n)) :
    JCentre s t = ((JNumCentre s t : ℕ) : ℚ) / 2 :=
  rfl

/-- The marking pairing vanishes when there are no grid points. -/
@[simp]
theorem JCentre_empty_left (t : Finset (Fin n × Fin n)) : JCentre ∅ t = 0 := by
  simp [JCentre]

/-- The marking pairing is additive in the grid points over disjoint unions. -/
theorem JCentre_union_left {s₁ s₂ t : Finset (Fin n × Fin n)} (h : Disjoint s₁ s₂) :
    JCentre (s₁ ∪ s₂) t = JCentre s₁ t + JCentre s₂ t := by
  rw [JCentre, JCentre, JCentre, JNumCentre_union_left h]
  push_cast
  ring

/-- The marking pairing after inserting a fresh grid point. -/
theorem JCentre_insert_left {p : Fin n × Fin n} {s t : Finset (Fin n × Fin n)} (h : p ∉ s) :
    JCentre (insert p s) t = JCentre {p} t + JCentre s t := by
  rw [← Finset.singleton_union, JCentre_union_left]
  exact Finset.disjoint_singleton_left.mpr h

/-- The marking pairing is invariant under reflecting both point sets across the diagonal. -/
theorem JCentre_image_swap (s t : Finset (Fin n × Fin n)) :
    JCentre (s.image Prod.swap) (t.image Prod.swap) = JCentre s t := by
  rw [JCentre, JCentre, JNumCentre_image_swap]

end GridPoint

namespace GridState

variable {n : ℕ}

/-- The southwest-of-centre count of the point sets of two grid states, as a column-pair
count. -/
theorem ICentre_pointSet_eq_card (x y : GridState n) :
    GridPoint.ICentre x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).card := by
  rw [pointSet, pointSet, GridPoint.ICentre_graph_eq_card]

/-- The numerator of the marking pairing on two state point sets, as a sum of two column-index
counts. -/
theorem JNumCentre_pointSet_eq_card (x y : GridState n) :
    GridPoint.JNumCentre x.pointSet y.pointSet =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ y p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ y p.1 < x p.2).card := by
  rw [GridPoint.JNumCentre_def, ICentre_pointSet_eq_card, I_pointSet_eq_card]

/-- Pairing a grid state against the squares it occupies adds exactly the `n` diagonal pairs to
the strict southwest count: a column pair `c < d` contributes to both counts or to neither, and
each of the `n` columns contributes its own square. -/
theorem ICentre_self_pointSet_eq (x : GridState n) :
    GridPoint.ICentre x.pointSet x.pointSet = GridPoint.I x.pointSet x.pointSet + n := by
  classical
  rw [ICentre_pointSet_eq_card, I_self_pointSet_eq_card]
  have hsplit :
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ x p.2) =
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2) ∪
          (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨h, lt_of_le_of_ne h2 fun heq => (ne_of_lt h) (x.toPerm.injective heq)⟩
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨le_of_lt h1, le_of_lt h2⟩
      · exact ⟨le_of_eq h, le_of_eq (congrArg x h)⟩
  have hdisj :
      Disjoint (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ x p.1 < x p.2)
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    rw [Finset.mem_filter] at hp hq
    exact (ne_of_lt hp.2.1) hq.2
  have hdiag : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2).card = n := by
    have hset : (Finset.univ.filter fun p : Fin n × Fin n => p.1 = p.2) =
        (Finset.univ : Finset (Fin n)).diag := by
      ext p
      simp [Finset.mem_diag]
    rw [hset, Finset.diag_card, Finset.card_univ, Fintype.card_fin]
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hdiag]

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The pairing of a grid state against the `O`-markings of a grid diagram. -/
@[expose] def JO (x : GridState n) : ℚ :=
  GridPoint.JCentre x.pointSet G.OSet

/-- `JO` is the marking pairing of a state against the `O`-markings. -/
@[simp]
theorem JO_def (x : GridState n) : GridDiagram.JO G x = GridPoint.JCentre x.pointSet G.OSet :=
  rfl

/-- The pairing of a grid state against the `X`-markings of a grid diagram. -/
@[expose] def JX (x : GridState n) : ℚ :=
  GridPoint.JCentre x.pointSet G.XSet

/-- `JX` is the marking pairing of a state against the `X`-markings. -/
@[simp]
theorem JX_def (x : GridState n) : GridDiagram.JX G x = GridPoint.JCentre x.pointSet G.XSet :=
  rfl

/-- The `O`-marking pairing as a column-index count. -/
theorem JO_eq_card (x : GridState n) :
    G.JO x =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ G.O p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.O p.1 < x p.2).card : ℕ) :
          ℚ) / 2 := by
  rw [JO_def, OSet, GridPoint.JCentre_def, GridState.JNumCentre_pointSet_eq_card]

/-- The `X`-marking pairing as a column-index count. -/
theorem JX_eq_card (x : GridState n) :
    G.JX x =
      (((Finset.univ.filter fun p : Fin n × Fin n => p.1 ≤ p.2 ∧ x p.1 ≤ G.X p.2).card +
        (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.X p.1 < x p.2).card : ℕ) :
          ℚ) / 2 := by
  rw [JX_def, XSet, GridPoint.JCentre_def, GridState.JNumCentre_pointSet_eq_card]

/-- `JO` is invariant under reflecting the diagram and state across the diagonal. -/
theorem JO_transpose (x : GridState n) :
    GridDiagram.JO G.transpose x.transpose = GridDiagram.JO G x := by
  rw [JO_def, JO_def, GridState.transpose_pointSet, transpose_OSet, GridPoint.JCentre_image_swap]

/-- `JX` is invariant under reflecting the diagram and state across the diagonal. -/
theorem JX_transpose (x : GridState n) :
    GridDiagram.JX G.transpose x.transpose = GridDiagram.JX G x := by
  rw [JX_def, JX_def, GridState.transpose_pointSet, transpose_XSet, GridPoint.JCentre_image_swap]

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
