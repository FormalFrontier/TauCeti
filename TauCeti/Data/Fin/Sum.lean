/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The two-element sum as `Fin 2`

`Unit ⊕ Unit` and `Fin 2` are the two ways a two-element index type arises: one variable per
named slot, or one variable per numeral. Translating between them is pure bookkeeping, needed
wherever an object indexed by named slots must be presented against an API indexed by `Fin 2`.

This is Mathlib's own composition — `finOneEquiv` on each summand, then `finSumFinEquiv` — given
a name and the four evaluation lemmas, so that call sites reindexing a two-variable object can
rewrite rather than unfold it.

## Main definitions

* `unitSumUnitEquivFinTwo`: the equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to
  `0` and the right to `1`.

## Implementation notes

The composition is an implementation detail: the four evaluation lemmas characterise the
equivalence completely, so `Mathlib.Logic.Equiv.Fin.Basic`, which supplies `finOneEquiv` and
`finSumFinEquiv` and is used only in the definition body, is imported privately rather than
re-exported. Only `Mathlib.Logic.Equiv.Defs`, needed for the type of the declaration, is public.
-/

public section

/-- The equivalence `Unit ⊕ Unit ≃ Fin 2`, sending the left summand to `0` and the right to `1`.

An `Equiv` rather than a bare `Function.Embedding`: injectivity is what turns a coefficient under
a reindexing into an equality rather than a sum over a fibre, but surjectivity is what lets a
statement about *every* `Fin 2` index be pulled back, and both directions are wanted downstream. -/
def unitSumUnitEquivFinTwo : (Unit ⊕ Unit) ≃ Fin 2 :=
  (Equiv.sumCongr finOneEquiv.symm finOneEquiv.symm).trans finSumFinEquiv

@[simp]
theorem unitSumUnitEquivFinTwo_inl : unitSumUnitEquivFinTwo (Sum.inl ()) = 0 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_inr : unitSumUnitEquivFinTwo (Sum.inr ()) = 1 := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_zero :
    unitSumUnitEquivFinTwo.symm 0 = Sum.inl () := by decide

@[simp]
theorem unitSumUnitEquivFinTwo_symm_one :
    unitSumUnitEquivFinTwo.symm 1 = Sum.inr () := by decide
