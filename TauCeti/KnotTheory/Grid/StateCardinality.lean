/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
public import TauCeti.KnotTheory.Grid.Diagram.Basic

/-!
# Cardinality of grid states

This file records the finite size of the generator set for an `n × n` grid complex. A grid state
is encoded in `TauCeti.KnotTheory.Grid.Diagram.Basic` as a permutation graph on the columns, so the
set of grid states is equivalent to `Equiv.Perm (Fin n)` and has cardinality `n!`.

The statements here are deliberately about the generator set only. They are the counting API
needed before explicit computations of small fully blocked grid complexes, whose chain module is
the free `ZMod 2`-module on `GridState n`.

## Main results

* `TauCeti.GridState.card`: there are `n!` grid states on an `n × n` grid.
* `TauCeti.GridState.card_univ`: the finite generator set has cardinality `n!`.
* `TauCeti.GridState.subsingletonOfLeOne`: for `n ≤ 1`, grid states are unique.
* `TauCeti.GridState.card_zero`, `TauCeti.GridState.card_one`, `TauCeti.GridState.card_two`:
  small-grid cardinalities used as sanity checks for later computations.
* `TauCeti.GridState.twoByTwoId` and `TauCeti.GridState.twoByTwoSwap`: the two named states in
  grid size two.
* `TauCeti.GridState.eq_twoByTwoId_or_eq_twoByTwoSwap`: every `2 × 2` grid state is one of the
  two named states.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.1, "Grid diagrams
and grid states", and the standing convention that the grid complexes should compute on explicit
small grids. The encoding follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Chapter 3: a grid state is one occupied square in every row and every column.
-/

public section

namespace TauCeti

namespace GridState

variable {n : ℕ}

/-- The number of grid states on an `n × n` grid is `n!`. -/
@[simp]
theorem card (n : ℕ) : Fintype.card (GridState n) = n.factorial := by
  rw [Fintype.card_congr (equivPerm n), Fintype.card_perm, Fintype.card_fin]

/-- The universe finite set of grid states has cardinality `n!`. -/
theorem card_univ (n : ℕ) : (Finset.univ : Finset (GridState n)).card = n.factorial := by
  rw [Finset.card_univ, card]

/-- The natural cardinality of grid states is `n!`. -/
theorem natCard (n : ℕ) : Nat.card (GridState n) = n.factorial := by
  rw [Nat.card_eq_fintype_card, card]

/-- There is one grid state on the empty grid. -/
theorem card_zero : Fintype.card (GridState 0) = 1 := by
  simp

/-- There is one grid state on a `1 × 1` grid. -/
theorem card_one : Fintype.card (GridState 1) = 1 := by
  simp

/-- There are two grid states on a `2 × 2` grid. -/
theorem card_two : Fintype.card (GridState 2) = 2 := by
  simp

/-- Any two grid states are equal whenever the grid has at most one row and column. -/
theorem subsingletonOfLeOne (hn : n ≤ 1) : Subsingleton (GridState n) := by
  have hcard : Fintype.card (GridState n) ≤ 1 := by
    rw [card]
    rcases n with _ | n
    · simp
    · rcases n with _ | n
      · simp
      · omega
  exact Fintype.card_le_one_iff_subsingleton.mp hcard

/-- There is a unique grid state on the empty grid. -/
instance instUniqueZero : Unique (GridState 0) :=
  letI : Subsingleton (GridState 0) := subsingletonOfLeOne (Nat.zero_le 1)
  { default := (equivPerm 0).symm 1
    uniq := fun _ => Subsingleton.elim _ _ }

/-- The unique empty-grid state is the state associated to the identity permutation. -/
theorem default_zero_eq : (default : GridState 0) = (equivPerm 0).symm 1 :=
  Subsingleton.elim _ _

/-- There is a unique grid state on a `1 × 1` grid. -/
instance instUniqueOne : Unique (GridState 1) :=
  letI : Subsingleton (GridState 1) := subsingletonOfLeOne (Nat.le_refl 1)
  { default := (equivPerm 1).symm 1
    uniq := fun _ => Subsingleton.elim _ _ }

/-- The unique `1 × 1` grid state sends the only column to the only row. -/
@[simp]
theorem apply_eq_zero (x : GridState 1) (c : Fin 1) : x c = 0 := by
  fin_cases c
  exact Subsingleton.elim _ _

/-- The two grid states on a `2 × 2` grid are exactly the identity and the transposition. -/
theorem eq_equivPerm_symm_one_or_eq_equivPerm_symm_swap (x : GridState 2) :
    x = (equivPerm 2).symm 1 ∨ x = (equivPerm 2).symm (Equiv.swap 0 1) := by
  have hne : x 1 ≠ x 0 := fun h => Fin.zero_ne_one (x.toPerm.injective h.symm)
  have hx : x.toPerm = 1 ∨ x.toPerm = Equiv.swap 0 1 := by
    rcases eq_or_ne (x 0) 0 with h0 | h0
    · left
      have h1 : x 1 = 1 := Fin.eq_one_of_ne_zero (x 1) fun hx1 => hne (hx1.trans h0.symm)
      apply Equiv.ext
      intro c
      fin_cases c
      · simpa using h0
      · simpa using h1
    · right
      have hx0 : x 0 = 1 := Fin.eq_one_of_ne_zero (x 0) h0
      have hx1 : x 1 = 0 := by
        by_contra hx1
        exact hne ((Fin.eq_one_of_ne_zero (x 1) hx1).trans hx0.symm)
      apply Equiv.ext
      intro c
      fin_cases c
      · simpa [Equiv.swap_apply_left] using hx0
      · simpa [Equiv.swap_apply_right] using hx1
  rcases hx with h | h
  · exact Or.inl (by rw [Equiv.eq_symm_apply, equivPerm_apply, h])
  · exact Or.inr (by rw [Equiv.eq_symm_apply, equivPerm_apply, h])

/-- The identity grid state on a `2 × 2` grid. -/
abbrev twoByTwoId : GridState 2 :=
  (equivPerm 2).symm 1

/-- The transposition grid state on a `2 × 2` grid. -/
abbrev twoByTwoSwap : GridState 2 :=
  (equivPerm 2).symm (Equiv.swap 0 1)

/-- The identity two-by-two state sends column `0` to row `0`. -/
@[simp]
theorem twoByTwoId_zero : twoByTwoId 0 = 0 :=
  rfl

/-- The identity two-by-two state sends column `1` to row `1`. -/
@[simp]
theorem twoByTwoId_one : twoByTwoId 1 = 1 :=
  rfl

/-- The transposition two-by-two state sends column `0` to row `1`. -/
theorem twoByTwoSwap_zero : twoByTwoSwap 0 = 1 := by
  simp [twoByTwoSwap]

/-- The transposition two-by-two state sends column `1` to row `0`. -/
theorem twoByTwoSwap_one : twoByTwoSwap 1 = 0 := by
  simp [twoByTwoSwap]

/-- The two named `2 × 2` grid states are distinct. -/
theorem twoByTwoId_ne_twoByTwoSwap : twoByTwoId ≠ twoByTwoSwap := by
  intro h
  exact (Fin.zero_ne_one : (0 : Fin 2) ≠ 1) (by
    simpa using congrArg (fun x : GridState 2 => x 0) h)

/-- Every `2 × 2` grid state is either the identity state or the transposition state. -/
theorem eq_twoByTwoId_or_eq_twoByTwoSwap (x : GridState 2) :
    x = twoByTwoId ∨ x = twoByTwoSwap :=
  by simpa [twoByTwoId, twoByTwoSwap] using eq_equivPerm_symm_one_or_eq_equivPerm_symm_swap x

end GridState

end TauCeti
