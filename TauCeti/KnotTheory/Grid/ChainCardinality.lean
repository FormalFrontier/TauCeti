/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Fintype
public import TauCeti.KnotTheory.Grid.Complex
public import TauCeti.KnotTheory.Grid.StateCardinality

/-!
# Cardinality of fully blocked grid chains

The fully blocked grid chain module is the finite free `ZMod 2`-module on grid states. Since
`GridState n` has `n!` elements, the underlying finite set of chains has `2^(n!)` elements.
This file records that bookkeeping, together with a generic finite-coefficient form.

The statements are intentionally about the ambient chain module, not about cycles, boundaries,
or homology. They are the finite-size API needed by later explicit computations of small grid
complexes.

## Main results

* `TauCeti.GridChain.card`: for a finite coefficient type `R`, the number of chains is
  `#R ^ n!`.
* `TauCeti.GridChain.support_card_le_factorial`: every chain has support of size at most `n!`.
* `TauCeti.GridChain.card_zmod_two`: the fully blocked `ZMod 2` chain module has `2 ^ n!`
  elements.
* `TauCeti.GridChain.card_zmod_two_zero`, `TauCeti.GridChain.card_zmod_two_one`, and
  `TauCeti.GridChain.card_zmod_two_two`: small-grid sanity checks for the first explicit
  computations.

## References

This supplies a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.3,
"The complexes and `∂² = 0`", and the standing convention "Keep computes as a requirement",
which asks that the grid complexes be evaluable on explicit small grids. The formal counting
argument reuses Mathlib's `Fintype.card_finsupp`.
-/

public section

namespace TauCeti

namespace GridChain

/-- The number of chains over a finite coefficient type is `#R ^ n!`.

This is the exact size of the finite search space for the ambient free module on grid states. -/
theorem card (R : Type*) [Zero R] [Fintype R] (n : ℕ) :
    Fintype.card (GridChain R n) = Fintype.card R ^ n.factorial := by
  rw [Fintype.card_finsupp, GridState.card]

/-- The natural cardinality of chains over a finite coefficient type is `Nat.card R ^ n!`. -/
theorem natCard (R : Type*) [Zero R] [Finite R] (n : ℕ) :
    Nat.card (GridChain R n) = Nat.card R ^ n.factorial := by
  classical
  let : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card, card, Nat.card_eq_fintype_card]

/-- The support of any grid chain has at most `n!` generators.

This is the chain-level version of `GridState.card_univ`; it bounds the number of potentially
nonzero coefficients in any explicit finite chain. -/
theorem support_card_le_factorial {R : Type*} [Zero R] {n : ℕ} (c : GridChain R n) :
    c.support.card ≤ n.factorial := by
  rw [← GridState.card_univ n]
  exact Finset.card_le_univ c.support

/-- The fully blocked `ZMod 2` chain module has `2 ^ n!` elements. -/
theorem card_zmod_two (n : ℕ) :
    Fintype.card (GridChain (ZMod 2) n) = 2 ^ n.factorial := by
  rw [card]
  rw [ZMod.card]

/-- The natural cardinality of the fully blocked `ZMod 2` chain module is `2 ^ n!`. -/
theorem natCard_zmod_two (n : ℕ) :
    Nat.card (GridChain (ZMod 2) n) = 2 ^ n.factorial := by
  rw [natCard, Nat.card_eq_fintype_card, ZMod.card]

/-- There are two `ZMod 2` chains on the empty grid. -/
theorem card_zmod_two_zero : Fintype.card (GridChain (ZMod 2) 0) = 2 := by
  simp

/-- There are two `ZMod 2` chains on a `1 × 1` grid. -/
theorem card_zmod_two_one : Fintype.card (GridChain (ZMod 2) 1) = 2 := by
  simp

/-- There are four `ZMod 2` chains on a `2 × 2` grid. -/
theorem card_zmod_two_two : Fintype.card (GridChain (ZMod 2) 2) = 4 := by
  simp

/-- A finite coefficient grid chain module is finite. -/
instance finite (R : Type*) [Zero R] [Finite R] (n : ℕ) : Finite (GridChain R n) := by
  classical
  let : Fintype R := Fintype.ofFinite R
  infer_instance

end GridChain

end TauCeti
