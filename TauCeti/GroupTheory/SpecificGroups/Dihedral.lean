/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The dihedral groups, enumerated

`DihedralGroup n` is finite, but `Fintype` alone does not hand back a list of its elements, since
`Finset.toList` is noncomputable. This file writes that list down, and evaluates
`DihedralGroup.exponent` — which computes the exponent of `DihedralGroup n` as `lcm n 2` — at the
two orders the worked examples of the Burnside--Dixon--Schneider character-table algorithm are run
on.

## Main definitions

* `TauCeti.dihedralElements`: a computable enumeration of `DihedralGroup n`.

## Main results

* `TauCeti.mem_dihedralElements`: that enumeration exhausts the group.
* `TauCeti.exponent_dihedralGroup_three`: `DihedralGroup 3`, of order `6`, has exponent `6`.
* `TauCeti.exponent_dihedralGroup_four`: `DihedralGroup 4`, of order `8`, has exponent `4`.
-/

public section

namespace TauCeti

/-- The rotations `r 0, …, r (n-1)` of `DihedralGroup n`, each followed by the corresponding
reflection. For `n ≠ 0` this lists all `2 * n` elements of the group, which is
`TauCeti.mem_dihedralElements`. The body is exposed because a kernel computation over the group —
such as the class data of `TauCeti.dihedralClassData` — has to reduce it. -/
@[expose] def dihedralElements (n : ℕ) : List (DihedralGroup n) :=
  (List.range n).flatMap fun i : ℕ => [DihedralGroup.r (i : ZMod n), DihedralGroup.sr (i : ZMod n)]

/-- The enumeration `TauCeti.dihedralElements` exhausts the dihedral group. -/
theorem mem_dihedralElements {n : ℕ} [NeZero n] (g : DihedralGroup n) : g ∈ dihedralElements n := by
  have hmem : ∀ i : ZMod n, i.val ∈ List.range n := fun i => List.mem_range.mpr (ZMod.val_lt i)
  cases g with
  | r i =>
    refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
    rw [ZMod.natCast_rightInverse i]
    simp
  | sr i =>
    refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
    rw [ZMod.natCast_rightInverse i]
    simp

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
