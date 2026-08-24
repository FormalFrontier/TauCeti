/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# The measurable structure on lists over a countable type

Mathlib equips no type of lists with a measurable structure. For a **countable** `α` there is only
one reasonable choice: `List α` is then itself countable, and Mathlib gives every countable type it
names outright — `ℕ`, `ℤ`, `ℚ`, `Bool`, `Fin n` — the discrete σ-algebra. This file records that
structure, so that a process whose values are finite words over a countable alphabet, such as the
excursion process of a path, is a measurable object.

The `Countable α` hypothesis is what confines the instance to the situation it is right for. Over
an uncountable `α` the discrete σ-algebra on `List α` is not the intended one — the structure
transported from `Σ n, Fin n → α` is — and the instance below deliberately does not apply there.

## Main definitions

* `TauCeti.instMeasurableSpaceList`: the discrete measurable structure on `List α` for countable
  `α`.
-/

public section

namespace TauCeti

variable {α : Type*} [Countable α]

/-- **Lists over a countable type carry the discrete measurable structure.** -/
instance instMeasurableSpaceList : MeasurableSpace (List α) := ⊤

/-- Every set of lists over a countable type is measurable. `MeasurableSingletonClass (List α)`
follows through `DiscreteMeasurableSpace.toMeasurableSingletonClass`. -/
instance instDiscreteMeasurableSpaceList : DiscreteMeasurableSpace (List α) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end TauCeti

end
