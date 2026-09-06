/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The sign group as a line over `ZMod 2`

Mathlib makes the two-element group `ℤˣ = {±1}`, written additively, a module over `ZMod 2`
(`Mathlib.Data.ZMod.IntUnitsPower`). This file records that it is a line: its `ZMod 2`-dimension
is `1`. This is what lets a family of `±1`-valued characters indexed by a finite set `ι` be read
as a linear map into a `ZMod 2`-space of dimension `#ι`.

## Main result

* `TauCeti.finrank_zmod_two_additive_intUnits`: `Module.finrank (ZMod 2) (Additive ℤˣ) = 1`.
-/

public section

namespace TauCeti

/-- The sign group `Additive ℤˣ` is one-dimensional over `ZMod 2`. -/
@[simp] theorem finrank_zmod_two_additive_intUnits :
    Module.finrank (ZMod 2) (Additive ℤˣ) = 1 := by
  refine (finrank_eq_one_iff_of_nonzero' (K := ZMod 2) (Additive.ofMul (-1 : ℤˣ))
    (by rw [Ne, ofMul_eq_zero]; decide)).mpr fun w => ?_
  rcases Int.units_eq_one_or (Additive.toMul w) with h | h
  · exact ⟨0, by rw [zero_smul, ← ofMul_toMul w, h, ofMul_one]⟩
  · exact ⟨1, by rw [one_smul, ← ofMul_toMul w, h]⟩

end TauCeti
