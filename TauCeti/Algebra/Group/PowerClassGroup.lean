/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The group of `n`th power classes `G ⧸ Gⁿ`

For a commutative group `G` the subgroup `Gⁿ` of `n`th powers is the range of `powMonoidHom n`,
and this file names the quotient `G ⧸ Gⁿ` together with the class of an element. The quotient is
written **additively**, on `Additive G`, because its consumers are additive: the Kummer map lands
in a cohomology group, and at `n = 2` the quotient is the `𝔽₂`-vector space
`TauCeti.SquareClassGroup`, whose subgroup is Mathlib's `Subgroup.square` — the same subgroup by
`TauCeti.square_eq_powMonoidHom_two_range`.

## Main definitions

* `TauCeti.PowerClassGroup`: the quotient `G ⧸ Gⁿ`, written additively.
* `TauCeti.powerClass`: the `n`th power class of an element, with
  `TauCeti.powerClass_eq_zero_iff` characterising the trivial class as the `n`th powers.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] (n : ℕ)

/-- **The group of `n`th power classes** `G ⧸ Gⁿ`, written additively on `Additive G`. The
subgroup divided out is the range of `powMonoidHom n`, that is `{g ^ n | g : G}`. -/
abbrev PowerClassGroup : Type _ :=
  Additive G ⧸ (powMonoidHom n : G →* G).range.toAddSubgroup

variable {G}

/-- The `n`th power class of an element of `G`. -/
def powerClass (g : G) : PowerClassGroup G n :=
  QuotientAddGroup.mk (Additive.ofMul g)

/-- The power class is the quotient class of the element, spelled with `QuotientAddGroup.mk`.
`TauCeti.powerClass` is a plain definition, so this is what a downstream module rewrites with. -/
theorem powerClass_eq_mk (g : G) :
    powerClass n g = QuotientAddGroup.mk (Additive.ofMul g) := (rfl)

theorem powerClass_surjective : Function.Surjective (powerClass (G := G) n) := fun x =>
  QuotientAddGroup.induction_on x fun g => ⟨g.toMul, rfl⟩

@[simp]
theorem powerClass_mul (g h : G) : powerClass n (g * h) = powerClass n g + powerClass n h := (rfl)

@[simp]
theorem powerClass_one : powerClass n (1 : G) = 0 := (rfl)

/-- The class of a ratio is the difference of the classes. -/
@[simp]
theorem powerClass_div (g h : G) :
    powerClass n (g / h) = powerClass n g - powerClass n h := (rfl)

/-- **A power class is trivial exactly when its representative is an `n`th power.** -/
@[simp]
theorem powerClass_eq_zero_iff {g : G} : powerClass n g = 0 ↔ ∃ h : G, h ^ n = g := by
  rw [powerClass, QuotientAddGroup.eq_zero_iff, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]; exact Iff.rfl

/-- Two elements have the same power class exactly when their ratio is an `n`th power. -/
theorem powerClass_eq_iff {g h : G} :
    powerClass n g = powerClass n h ↔ ∃ v : G, v ^ n = g / h := by
  rw [← sub_eq_zero, ← powerClass_div, powerClass_eq_zero_iff]

end TauCeti
