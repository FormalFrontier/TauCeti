/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Support.Cardinality

/-!
# Two-step support for the fully blocked grid differential

This file records the finite support bookkeeping for applying the fully blocked grid
differential twice. The one-step support theorem says that `∂ x` is supported on the states
obtained from `x` by one nontrivial column transposition. Applying that theorem again gives a
small ambient set for `∂ (∂ x)`: the union of the column-swap neighbours of those neighbours.

The actual `∂² = 0` proof is not asserted here. These lemmas only isolate the finite target set
on which the later rectangle-pairing argument has to check cancellation.

## Main results

* `TauCeti.GridState.twoStepColumnSwapNeighbors`: the states reachable from `x` by two
  nontrivial column transpositions.
* `TauCeti.GridDiagram.fullyBlockedDifferential_sq_single_support_subset`: the support of
  `∂ (∂ x)` lies in that two-step neighbour set.
* `TauCeti.GridDiagram.fullyBlockedDifferential_sq_support_subset_biUnion`: the corresponding
  support bound for an arbitrary finitely supported chain.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`". The one-step column-transposition support condition follows
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters 3 and 4; this file
packages the direct two-step consequence needed before the square-zero rectangle pairing.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- The grid states reachable from `x` by two nontrivial column transpositions.

This is the finite ambient set for the support of `∂ (∂ x)` before the rectangle-pairing
argument proves that all of its coefficients cancel. -/
def twoStepColumnSwapNeighbors (x : GridState n) : Finset (GridState n) :=
  x.columnSwapNeighbors.biUnion fun y => y.columnSwapNeighbors

/-- Membership in the two-step column-swap neighbour set. -/
@[simp]
theorem mem_twoStepColumnSwapNeighbors {x z : GridState n} :
    z ∈ x.twoStepColumnSwapNeighbors ↔
      ∃ y : GridState n, y ∈ x.columnSwapNeighbors ∧ z ∈ y.columnSwapNeighbors := by
  simp [twoStepColumnSwapNeighbors]

/-- An expanded membership form for the two-step column-swap neighbour set. -/
theorem mem_twoStepColumnSwapNeighbors_iff_exists_swaps {x z : GridState n} :
    z ∈ x.twoStepColumnSwapNeighbors ↔
      ∃ y : GridState n, ∃ a b c d : Fin n,
        a ≠ b ∧ c ≠ d ∧ y = x.swapColumns a b ∧ z = y.swapColumns c d := by
  rw [mem_twoStepColumnSwapNeighbors]
  constructor
  · rintro ⟨y, hy, hz⟩
    rw [mem_columnSwapNeighbors] at hy hz
    obtain ⟨a, b, hab, rfl⟩ := hy
    obtain ⟨c, d, hcd, hz⟩ := hz
    exact ⟨x.swapColumns a b, a, b, c, d, hab, hcd, rfl, hz⟩
  · rintro ⟨y, a, b, c, d, hab, hcd, hy, hz⟩
    refine ⟨y, ?_, ?_⟩
    · rw [mem_columnSwapNeighbors]
      exact ⟨a, b, hab, hy⟩
    · rw [mem_columnSwapNeighbors]
      exact ⟨c, d, hcd, hz⟩

/-- The two-step neighbour set has at most `(n.choose 2) ^ 2` states. -/
theorem card_twoStepColumnSwapNeighbors_le (x : GridState n) :
    x.twoStepColumnSwapNeighbors.card ≤ (n.choose 2) ^ 2 := by
  rw [twoStepColumnSwapNeighbors, sq]
  exact (Finset.card_biUnion_le_card_mul x.columnSwapNeighbors
      (fun y : GridState n => y.columnSwapNeighbors) (n.choose 2)
      fun y _ => y.card_columnSwapNeighbors_le).trans
    (by rw [x.card_columnSwapNeighbors])

/-- In grid size at most `1`, no state is reachable by two nontrivial column swaps. -/
theorem twoStepColumnSwapNeighbors_eq_empty_of_le_one (x : GridState n) (hn : n ≤ 1) :
    x.twoStepColumnSwapNeighbors = ∅ := by
  have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hn)
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero
    ((x.card_twoStepColumnSwapNeighbors_le).trans (by rw [hchoose, zero_pow (by decide)]))

/-- In grid size `0`, no state is reachable by two nontrivial column swaps. -/
@[simp]
theorem twoStepColumnSwapNeighbors_eq_empty_of_zero (x : GridState 0) :
    x.twoStepColumnSwapNeighbors = ∅ :=
  x.twoStepColumnSwapNeighbors_eq_empty_of_le_one (Nat.zero_le 1)

/-- In grid size `1`, no state is reachable by two nontrivial column swaps. -/
@[simp]
theorem twoStepColumnSwapNeighbors_eq_empty_of_one (x : GridState 1) :
    x.twoStepColumnSwapNeighbors = ∅ :=
  x.twoStepColumnSwapNeighbors_eq_empty_of_le_one le_rfl

end GridState

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The support of `∂ (∂ c)` is contained in the union of the two-step neighbour sets attached
to the states appearing in the input chain. -/
theorem fullyBlockedDifferential_sq_support_subset_biUnion (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential (G.fullyBlockedDifferential c)).support ⊆
      c.support.biUnion fun x : GridState n => x.twoStepColumnSwapNeighbors := by
  intro z hz
  have hz' :=
    G.fullyBlockedDifferential_support_subset_biUnion (G.fullyBlockedDifferential c) hz
  obtain ⟨y, hy, hzy⟩ := Finset.mem_biUnion.mp hz'
  have hy' := G.fullyBlockedDifferential_support_subset_biUnion c hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp hy'
  rw [Finset.mem_biUnion]
  refine ⟨x, hx, ?_⟩
  rw [GridState.mem_twoStepColumnSwapNeighbors]
  exact ⟨y, hyx, hzy⟩

/-- If a state is not in any two-step neighbour set attached to the input support, its
coefficient in `∂ (∂ c)` is zero. -/
theorem fullyBlockedDifferential_sq_apply_eq_zero_of_notMem_support_biUnion
    (c : GridChain (ZMod 2) n) {z : GridState n}
    (hz : z ∉ c.support.biUnion fun x : GridState n => x.twoStepColumnSwapNeighbors) :
    G.fullyBlockedDifferential (G.fullyBlockedDifferential c) z = 0 :=
  Finsupp.notMem_support_iff.mp fun hsupport =>
    hz (G.fullyBlockedDifferential_sq_support_subset_biUnion c hsupport)

/-- The support of `∂ (∂ c)` has cardinality at most
`c.support.card * (n.choose 2) ^ 2`. -/
theorem fullyBlockedDifferential_sq_support_card_le (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential (G.fullyBlockedDifferential c)).support.card ≤
      c.support.card * (n.choose 2) ^ 2 :=
  (Finset.card_le_card (G.fullyBlockedDifferential_sq_support_subset_biUnion c)).trans
    (Finset.card_biUnion_le_card_mul c.support
      (fun x : GridState n => x.twoStepColumnSwapNeighbors) ((n.choose 2) ^ 2)
      fun x _ => x.card_twoStepColumnSwapNeighbors_le)

/-- The support of `∂ (∂ x)` is contained in the states reachable from `x` by two
column transpositions. This is the finite search space for the later rectangle-pairing proof of
`∂² = 0` on generators. -/
theorem fullyBlockedDifferential_sq_single_support_subset (x : GridState n) :
    (G.fullyBlockedDifferential (G.fullyBlockedDifferential (Finsupp.single x 1))).support ⊆
        x.twoStepColumnSwapNeighbors := by
  intro z hz
  have hz' := G.fullyBlockedDifferential_sq_support_subset_biUnion (Finsupp.single x 1) hz
  simpa using hz'

/-- If a state is not reachable by two column swaps from `x`, its coefficient in
`∂ (∂ x)` is zero. -/
theorem fullyBlockedDifferential_sq_single_apply_eq_zero_of_notMem_twoStep
    (x : GridState n) {z : GridState n} (hz : z ∉ x.twoStepColumnSwapNeighbors) :
    G.fullyBlockedDifferential
      (G.fullyBlockedDifferential (Finsupp.single x 1)) z = 0 :=
  Finsupp.notMem_support_iff.mp fun hsupport =>
    hz (G.fullyBlockedDifferential_sq_single_support_subset x hsupport)

/-- The support of `∂ (∂ x)` has at most `(n.choose 2) ^ 2` states. -/
theorem fullyBlockedDifferential_sq_single_support_card_le (x : GridState n) :
    (G.fullyBlockedDifferential (G.fullyBlockedDifferential (Finsupp.single x 1))).support.card ≤
        (n.choose 2) ^ 2 :=
  (Finset.card_le_card (G.fullyBlockedDifferential_sq_single_support_subset x)).trans
    x.card_twoStepColumnSwapNeighbors_le

end GridDiagram

end TauCeti
