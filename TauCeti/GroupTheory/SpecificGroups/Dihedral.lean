/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Exponents of the small dihedral groups

`DihedralGroup.exponent` computes the exponent of `DihedralGroup n` as `lcm n 2`. This file
evaluates it at the two orders the worked examples of the Burnside--Dixon--Schneider character-table
algorithm are run on.

## Main results

* `TauCeti.exponent_dihedralGroup_three`: `DihedralGroup 3`, of order `6`, has exponent `6`.
* `TauCeti.exponent_dihedralGroup_four`: `DihedralGroup 4`, of order `8`, has exponent `4`.
-/

public section

namespace TauCeti

/-- The dihedral group of order `6`, the symmetric group on three letters, has exponent `6`. -/
@[simp]
theorem exponent_dihedralGroup_three : Monoid.exponent (DihedralGroup 3) = 6 := by
  rw [DihedralGroup.exponent]
  decide

/-- The dihedral group of order `8` has exponent `4`. -/
@[simp]
theorem exponent_dihedralGroup_four : Monoid.exponent (DihedralGroup 4) = 4 := by
  rw [DihedralGroup.exponent]
  decide

end TauCeti
