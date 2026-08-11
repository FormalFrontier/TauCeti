/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Shift.Basic
public import TauCeti.Probability.Process.BlockAverage

/-!
# Birkhoff averages of the one-sided shift

The shift instance of `birkhoffAverage_eq_prefixAverage`: for the one-sided shift on `ℕ → α` and a
single-coordinate observable, a Birkhoff average *is* a prefix average of the process.

This is the bridge from the generic mean-ergodic theorem — which speaks of Birkhoff averages of a
single observable under a measure-preserving map — to the block-average API, which speaks of
averages of a process over a selection of coordinates. Neither side needs to know about the other:
they are the same function.

Nothing here involves a measure, and nothing is specific to any de Finetti route.
-/

public section

open Filter MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*}

/-- **The coordinate instance.** For the one-sided shift and a single-coordinate observable,
`birkhoffAverage ℝ (shift α) (fun x => f (x 0)) n` is `prefixAverage (fun i x => f (x i)) n`.

This is the bridge from the generic mean-ergodic theorem — which speaks of Birkhoff averages of a
single observable under a measure-preserving map — to the block-average API, which speaks of
averages of a process over a selection of coordinates. Neither side needs to know about the other:
they are the same function. -/
@[simp]
theorem birkhoffAverage_shift_eq_prefixAverage (f : α → ℝ) (n : ℕ) :
    birkhoffAverage ℝ (shift α) (fun x => f (x 0)) n
      = prefixAverage (fun i (x : ℕ → α) => f (x i)) n := by
  rw [birkhoffAverage_eq_prefixAverage]
  simp [shift_iterate_apply]


end Probability

end TauCeti

end
