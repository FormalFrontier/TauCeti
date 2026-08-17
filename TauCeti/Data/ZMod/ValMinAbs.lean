/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.ValMinAbs

/-!
# The residue window: small integers are recovered from their residues

If `2 * |z| < n` then `z` lies strictly inside the window `(-n/2, n/2]` that `ZMod.valMinAbs`
picks representatives from, so `ZMod.valMinAbs` returns `z` itself from the residue of `z` modulo
`n` -- and hence two such integers with the same residue are equal.

This is the arithmetic behind the size bound in a modular reconstruction: bound the integer you
are looking for by half the modulus and its residue determines it.

## Main results

* `TauCeti.ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt`: `((z : ZMod n)).valMinAbs = z`.
* `TauCeti.ZMod.eq_of_intCast_eq_of_two_mul_natAbs_lt`: two such integers agreeing modulo `n` are
  equal.
-/

public section

namespace TauCeti

namespace ZMod

/-- **An integer of absolute value less than half the modulus is returned by `ZMod.valMinAbs`.**
Such a `z` is the representative of its own residue class that `ZMod.valMinAbs` chooses. -/
theorem valMinAbs_intCast_of_two_mul_natAbs_lt {n : ℕ} {z : ℤ} (h : 2 * z.natAbs < n) :
    ((z : ZMod n)).valMinAbs = z := by
  have : NeZero n := ⟨by omega⟩
  refine (ZMod.valMinAbs_spec _ _).2 ⟨rfl, ?_, ?_⟩ <;> omega

/-- **An integer of absolute value less than half the modulus is determined by its residue.** -/
theorem eq_of_intCast_eq_of_two_mul_natAbs_lt {n : ℕ} {z w : ℤ} (hz : 2 * z.natAbs < n)
    (hw : 2 * w.natAbs < n) (h : (z : ZMod n) = w) : z = w := by
  rw [← valMinAbs_intCast_of_two_mul_natAbs_lt hz, ← valMinAbs_intCast_of_two_mul_natAbs_lt hw, h]

end ZMod

end TauCeti
