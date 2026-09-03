/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Applying `ZMod.finEquiv`

Mathlib defines `ZMod.finEquiv : Fin n ≃+* ZMod n` for `[NeZero n]` and states nothing about
applying it. This file states the two evaluation rules as `@[simp]` lemmas, so that an argument
indexed by `Fin n` rewrites into `ZMod n` arithmetic instead of being unfolded at each use.

## Main results

* `ZMod.finEquiv_apply`: `ZMod.finEquiv n j` is the natural cast of `j.val`.
* `ZMod.finEquiv_symm_apply_val`: it is `(ZMod.finEquiv n).symm` that produces the canonical `Fin n`
  representative of an element of `ZMod n`, and that representative's coerced natural value is
  the element's `val`.
-/

public section

namespace ZMod

open Fin.CommRing in
/-- **Applying `ZMod.finEquiv` is the natural cast.** `ZMod.finEquiv n j` is the image of `j.val`
under `Nat.cast`.

Mathlib defines `finEquiv` and states no evaluation rule for it in either direction, so this is
the lemma a `Fin n`-indexed statement rewrites through to reach `ZMod n`. -/
@[simp]
lemma finEquiv_apply {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n) j = ((j : ℕ) : ZMod n) := by
  -- Through stated lemmas rather than defeq: `Fin.cast_val_eq_self` puts `j` in natural-cast
  -- form, then `map_natCast` moves the cast across the ring hom. So the proof does not depend on
  -- `finEquiv` being defined by cases on `n`. `Fin.instCommRing` is scoped
  -- (`Mathlib/Data/ZMod/Defs.lean`), hence the `open Fin.CommRing in` above.
  conv_lhs => rw [← Fin.cast_val_eq_self j]
  exact map_natCast (ZMod.finEquiv n) j.val

/-- **The canonical `Fin n` representative of `z : ZMod n` has natural value `z.val`.** The
representative is produced by `(ZMod.finEquiv n).symm`, not by `finEquiv` itself, which maps the
other way. This is the companion of `finEquiv_apply`, and the form needed to index by `Fin n` an
element obtained by solving in `ZMod n`. -/
@[simp]
lemma finEquiv_symm_apply_val {n : ℕ} [NeZero n] (z : ZMod n) :
    (((ZMod.finEquiv n).symm z : Fin n) : ℕ) = z.val := by
  -- Through the stated rules rather than the `ZMod (k+1) = Fin (k+1)` reduction: rewrite `z` as
  -- `finEquiv` of its representative, then evaluate with `finEquiv_apply`.
  conv_rhs => rw [← (ZMod.finEquiv n).apply_symm_apply z, finEquiv_apply]
  exact (ZMod.val_natCast_of_lt ((ZMod.finEquiv n).symm z).isLt).symm

end ZMod
