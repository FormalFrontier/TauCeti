/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Characters of the rotation subgroup of a dihedral group

The rotation subgroup `TauCeti.dihedralRotations n` of `DihedralGroup n` is cyclic, its coordinate
`TauCeti.dihedralRotationsMulEquiv` identifying it with `Multiplicative (ZMod n)`. A character of
it is therefore named by a single `n`-th root of unity `ζ`: this file reads Mathlib's
`AddChar.zmodChar` through that coordinate to get `TauCeti.dihedralRotationChar`, the character
sending the rotation `r i` to `ζ ^ i`, and shows that a *primitive* root of unity gives a faithful
character.

This is separated from `TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic` because
`AddChar.zmodChar` lives in the number-theoretic part of Mathlib, which the rotation subgroup
itself does not need.

## Main definitions

* `TauCeti.dihedralRotationChar`: the character of the rotation subgroup sending `r i` to `ζ ^ i`,
  for `ζ` an `n`-th root of unity.

## Main results

* `TauCeti.dihedralRotationChar_injective`: the character attached to a *primitive* `n`-th root of
  unity is faithful.
-/

public section

namespace TauCeti

variable {n : ℕ} {M : Type*} [CommMonoid M] {ζ : M} [NeZero n]

/-- **The character of the rotation subgroup attached to an `n`-th root of unity** `ζ`: the
rotation `r i` is sent to `ζ ^ i`, the exponent being the canonical representative of `i` in
`ZMod n`. It is Mathlib's `AddChar.zmodChar` read through the cyclic coordinate
`TauCeti.dihedralRotationsMulEquiv`. -/
def dihedralRotationChar (hζ : ζ ^ n = 1) : dihedralRotations n →* M :=
  (AddChar.toMonoidHomEquiv (AddChar.zmodChar n hζ)).comp (dihedralRotationsMulEquiv n).toMonoidHom

@[simp]
theorem dihedralRotationChar_apply (hζ : ζ ^ n = 1) (x : dihedralRotations n) :
    dihedralRotationChar hζ x = ζ ^ (Multiplicative.toAdd (dihedralRotationsMulEquiv n x)).val := by
  simp [dihedralRotationChar, AddChar.zmodChar_apply]

/-- The character sends the rotation `r i` to `ζ ^ i`. -/
theorem dihedralRotationChar_r (hζ : ζ ^ n = 1) (i : ZMod n) :
    dihedralRotationChar hζ ⟨DihedralGroup.r i, r_mem_dihedralRotations i⟩ = ζ ^ i.val := by
  rw [dihedralRotationChar_apply, dihedralRotationsMulEquiv_r, toAdd_ofAdd]

/-- **The character attached to a *primitive* `n`-th root of unity is faithful**: the additive
character `AddChar.zmodChar` it is read off is then primitive, so it takes the value `1` only at
the identity rotation. -/
theorem dihedralRotationChar_injective (h : IsPrimitiveRoot ζ n) :
    Function.Injective (dihedralRotationChar h.pow_eq_one) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
  rw [dihedralRotationChar_apply] at hx
  have hzero := ((AddChar.zmodChar_primitive_of_primitive_root n h).zmod_char_eq_one_iff n
    (Multiplicative.toAdd (dihedralRotationsMulEquiv n x))).mp (by rwa [AddChar.zmodChar_apply])
  exact (dihedralRotationsMulEquiv n).map_eq_one_iff.mp (toAdd_eq_zero.mp hzero)

end TauCeti
