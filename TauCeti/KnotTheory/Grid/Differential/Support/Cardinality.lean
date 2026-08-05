/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.KnotTheory.Grid.Differential.Support.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Nat.Choose.Basic

/-!
# Cardinality bounds for the fully blocked grid differential support

The fully blocked grid differential is already known to be supported on the
column-swap neighbours of a grid state. This file makes that computability statement
quantitative: those neighbours are the image of Mathlib's off-diagonal finite set of ordered
distinct column pairs. The two orders of the same column swap give the same target state, so
Mathlib's `Sym2.card_image_offDiag` turns this into the `n.choose 2` bound for possible targets.

The same estimate extends to arbitrary finitely supported chains by taking the finite
union of the neighbour sets attached to the input support. These bounds are the
finite-row bookkeeping needed before the `∂² = 0` rectangle-pairing proof and before
evaluating the fully blocked complex on small explicit grids.

## Main results

* `TauCeti.GridDiagram.fullyBlockedDifferentialOnGenerator_support_card_le_choose`:
  the same bound for the support of a differential row.
* `TauCeti.GridDiagram.fullyBlockedDifferential_support_subset_biUnion` and
  `TauCeti.GridDiagram.fullyBlockedDifferential_support_card_le`:
  support and cardinality bounds for the differential of an arbitrary chain.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`,
Lane G.3, "The complexes and `∂² = 0`", and for the roadmap's standing requirement that
the grid differential compute on explicit small grids. The column-transposition support
condition follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapters
3 and 4.
-/

public section

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-- The support of the fully blocked differential of one generator has at most
`n.choose 2` states. This is the quantitative form of the column-transposition
support theorem. -/
theorem fullyBlockedDifferentialOnGenerator_support_card_le_choose (x : GridState n) :
    (G.fullyBlockedDifferentialOnGenerator x).support.card ≤ n.choose 2 :=
  (G.fullyBlockedDifferentialOnGenerator_support_card_le x).trans x.card_columnSwapNeighbors_le

/-- The support of the fully blocked differential of one generator is empty in grid
size at most `1`. -/
theorem fullyBlockedDifferentialOnGenerator_support_eq_empty_of_le_one
    (G : GridDiagram n) (hn : n ≤ 1) (x : GridState n) :
    (G.fullyBlockedDifferentialOnGenerator x).support = ∅ := by
  have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hn)
  apply Finset.card_eq_zero.mp
  exact Nat.eq_zero_of_le_zero
    ((G.fullyBlockedDifferentialOnGenerator_support_card_le_choose x).trans (by rw [hchoose]))

/-- The support of the fully blocked differential of one generator is empty in grid
size `0`. -/
theorem fullyBlockedDifferentialOnGenerator_support_eq_empty_of_zero (G : GridDiagram 0)
    (x : GridState 0) : (G.fullyBlockedDifferentialOnGenerator x).support = ∅ :=
  G.fullyBlockedDifferentialOnGenerator_support_eq_empty_of_le_one (Nat.zero_le 1) x

/-- The fully blocked differential of a generator is zero in grid size at most `1`. -/
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_le_one
    (G : GridDiagram n) (hn : n ≤ 1) (x : GridState n) :
    G.fullyBlockedDifferentialOnGenerator x = 0 :=
  Finsupp.support_eq_empty.mp
    (G.fullyBlockedDifferentialOnGenerator_support_eq_empty_of_le_one hn x)

/-- The fully blocked differential of a generator is zero in grid size `0`. -/
@[simp]
theorem fullyBlockedDifferentialOnGenerator_eq_zero_of_zero (G : GridDiagram 0) (x : GridState 0) :
    G.fullyBlockedDifferentialOnGenerator x = 0 :=
  G.fullyBlockedDifferentialOnGenerator_eq_zero_of_le_one (Nat.zero_le 1) x

/-- The support of the fully blocked differential of a chain is contained in the union
of the column-swap neighbour sets of the states appearing in the input chain. -/
theorem fullyBlockedDifferential_support_subset_biUnion (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential c).support ⊆
      c.support.biUnion fun x : GridState n => x.columnSwapNeighbors := by
  rw [fullyBlockedDifferential_apply]
  refine Finsupp.support_sum.trans ?_
  intro y hy
  rw [Finset.mem_biUnion] at hy ⊢
  obtain ⟨x, hx, hyx⟩ := hy
  refine ⟨x, hx, ?_⟩
  exact G.fullyBlockedDifferentialOnGenerator_support_subset x (Finsupp.support_smul hyx)

/-- A coefficient of the fully blocked differential vanishes if its target is not in the
union of column-swap neighbours of the input support. -/
theorem fullyBlockedDifferential_apply_eq_zero_of_notMem_support_biUnion
    (c : GridChain (ZMod 2) n) {y : GridState n}
    (h : y ∉ c.support.biUnion fun x : GridState n => x.columnSwapNeighbors) :
    G.fullyBlockedDifferential c y = 0 :=
  Finsupp.notMem_support_iff.mp fun hy =>
    h (G.fullyBlockedDifferential_support_subset_biUnion c hy)

/-- The support of the fully blocked differential of an arbitrary chain has cardinality
at most the size of the input support times `n.choose 2`. -/
theorem fullyBlockedDifferential_support_card_le (c : GridChain (ZMod 2) n) :
    (G.fullyBlockedDifferential c).support.card ≤ c.support.card * n.choose 2 :=
  (Finset.card_le_card (G.fullyBlockedDifferential_support_subset_biUnion c)).trans
    (Finset.card_biUnion_le_card_mul c.support (fun x : GridState n => x.columnSwapNeighbors)
      (n.choose 2) fun x _ => x.card_columnSwapNeighbors_le)

/-- The fully blocked differential is zero on every chain in grid size at most `1`. -/
theorem fullyBlockedDifferential_eq_zero_of_le_one (G : GridDiagram n) (hn : n ≤ 1) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) n →ₗ[ZMod 2] GridChain (ZMod 2) n) := by
  apply LinearMap.ext
  intro c
  apply Finsupp.ext
  intro y
  have hsupport : (G.fullyBlockedDifferential c).support = ∅ := by
    have hchoose : n.choose 2 = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le hn)
    apply Finset.card_eq_zero.mp
    exact Nat.eq_zero_of_le_zero
      ((G.fullyBlockedDifferential_support_card_le c).trans (by rw [hchoose, mul_zero]))
  have hy_not : y ∉ (G.fullyBlockedDifferential c).support := by
    rw [hsupport]
    simp
  simpa using Finsupp.notMem_support_iff.mp hy_not

/-- The fully blocked differential is zero on every chain in grid size `0`. -/
@[simp]
theorem fullyBlockedDifferential_eq_zero_of_zero (G : GridDiagram 0) :
    G.fullyBlockedDifferential = (0 : GridChain (ZMod 2) 0 →ₗ[ZMod 2] GridChain (ZMod 2) 0) :=
  G.fullyBlockedDifferential_eq_zero_of_le_one (Nat.zero_le 1)

end GridDiagram

end TauCeti
