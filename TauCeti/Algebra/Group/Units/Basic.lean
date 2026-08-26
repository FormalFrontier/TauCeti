/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Group.Units.Defs

import Mathlib.Algebra.Group.Commute.Units

/-!
# Squares of units

This file relates squares in a monoid to squares in its group of units.

## Main results

* `TauCeti.isSquare_units_val_iff`: a unit is a square exactly when its underlying monoid element
  is a square.
-/

public section

namespace TauCeti

/-- A unit is a square exactly when its underlying monoid element is a square. -/
theorem isSquare_units_val_iff {K : Type*} [Monoid K] {u : Kˣ} :
    IsSquare (u : K) ↔ IsSquare u := by
  constructor
  · rintro ⟨x, hx⟩
    have hxu : IsUnit x := isUnit_mul_self_iff.mp (hx ▸ u.isUnit)
    exact ⟨hxu.unit, Units.ext (by simpa using hx)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(v : K), by simp⟩

end TauCeti
