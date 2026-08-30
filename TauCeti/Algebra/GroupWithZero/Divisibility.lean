/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# `NeZero` passes to divisors

Mathlib's `ne_zero_of_dvd_ne_zero` says that a divisor of a nonzero element is nonzero, as the
proposition `p ≠ 0`. Instance resolution needs the same fact as the class `NeZero p`, and a
caller holding `[NeZero q]` together with `p ∣ q` has to repackage the conclusion by hand;
Mathlib does exactly that inline in `Mathlib/GroupTheory/Index.lean` and
`Mathlib/GroupTheory/Schreier.lean`. This file names the repackaging once, so that a divisibility
hypothesis can discharge a `NeZero` side condition in one term.

## Main results

* `NeZero.of_dvd`: a divisor of an element carrying `NeZero` carries `NeZero`.
-/

public section

namespace NeZero

/-- **`NeZero` passes to divisors.** If `q` carries `NeZero` and `p ∣ q`, then so does `p`. This
is `ne_zero_of_dvd_ne_zero` with the conclusion packaged as an instance instead of as `p ≠ 0`.
Composed with `dvd_of_mul_right_dvd` and `dvd_of_mul_left_dvd` it discharges both side conditions
carried by a hypothesis of the shape `d * M ∣ N`. -/
theorem of_dvd {α : Type*} [MonoidWithZero α] {p q : α} [NeZero q] (h : p ∣ q) : NeZero p :=
  ⟨ne_zero_of_dvd_ne_zero (NeZero.ne q) h⟩

end NeZero
