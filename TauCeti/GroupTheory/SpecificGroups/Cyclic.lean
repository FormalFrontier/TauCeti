/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A computable enumeration of finite cyclic groups

For `n ≠ 0`, this file gives the standard computable enumeration of
`Multiplicative (ZMod n)`, transported from the additive group `ZMod n`.

## Main definitions

* `TauCeti.cyclicElements`: a computable enumeration of `Multiplicative (ZMod n)`.

## Main results

* `TauCeti.mem_cyclicElements`: the enumeration exhausts the group when `n ≠ 0`.

## References

The construction follows the enumeration pattern of `TauCeti.dihedralElements`.
-/

public section

namespace TauCeti

/-- For `n ≠ 0`, the standard computable enumeration of the finite cyclic group
`Multiplicative (ZMod n)`. For `n = 0`, this list is empty. -/
@[expose] def cyclicElements (n : ℕ) : List (Multiplicative (ZMod n)) :=
  List.map (fun i : ℕ => Multiplicative.ofAdd (i : ZMod n)) (List.range n)

/-- Every element of `Multiplicative (ZMod n)` occurs in `TauCeti.cyclicElements n` when `n` is
nonzero. -/
theorem mem_cyclicElements (n : ℕ) [NeZero n] (g : Multiplicative (ZMod n)) :
    g ∈ cyclicElements n := by
  rw [cyclicElements]
  have hg : Multiplicative.ofAdd (g.toAdd.val : ZMod n) = g :=
    congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val g.toAdd)
  rw [← hg]
  exact List.mem_map_of_mem
    (f := fun i : ℕ => Multiplicative.ofAdd (i : ZMod n))
    (List.mem_range.mpr (ZMod.val_lt g.toAdd))

end TauCeti
