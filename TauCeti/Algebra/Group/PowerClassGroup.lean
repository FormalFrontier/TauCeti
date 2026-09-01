/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.ModN
public import TauCeti.Algebra.Group.PowMonoidHom

/-!
# The group of `n`th power classes `G ⧸ Gⁿ`

For a commutative group `G` the subgroup `Gⁿ` of `n`th powers is the range of `powMonoidHom n`,
and this file names the quotient `G ⧸ Gⁿ` together with the class of an element. It reuses
Mathlib's additive quotient `ModN (Additive G) n`; in particular its specialization at `n = 2` is
definitionally `TauCeti.ElementaryTwoQuotient G`. The Kummer map consumes the additive form, while
the equality `TauCeti.modNSubgroup_eq_powerSubgroup` identifies its quotient subgroup with `Gⁿ`.

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
  ModN (Additive G) n

variable {G}

/-- The subgroup defining Mathlib's `ModN (Additive G) n` is the additive form of the subgroup of
`n`th powers in `G`. -/
theorem modNSubgroup_eq_powerSubgroup :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ))).toAddSubgroup =
      (powMonoidHom n : G →* G).range.toAddSubgroup := by
  ext a
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.lsmul_apply,
    Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.toMul, ?_⟩
    simpa only [powMonoidHom_apply, natCast_zsmul, toMul_nsmul] using
      congrArg Additive.toMul hb
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    simpa only [powMonoidHom_apply, natCast_zsmul, toMul_nsmul, toMul_ofMul] using hb

/-- The `n`th power class of an element of `G`. -/
def powerClass (g : G) : PowerClassGroup G n :=
  ModN.mkQ n (Additive.ofMul g)

/-- The power class is the quotient class of the element in Mathlib's `ModN` model. -/
theorem powerClass_eq_mk (g : G) :
    powerClass n g = Submodule.Quotient.mk (Additive.ofMul g) := by
  rw [powerClass, ModN.mkQ]
  rfl

theorem powerClass_surjective : Function.Surjective (powerClass (G := G) n) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨a.toMul, rfl⟩

@[simp]
theorem powerClass_mul (g h : G) : powerClass n (g * h) = powerClass n g + powerClass n h := by
  simp only [powerClass, ofMul_mul, map_add]

@[simp]
theorem powerClass_one : powerClass n (1 : G) = 0 := by
  simp only [powerClass, ofMul_one, map_zero]

/-- The class of a ratio is the difference of the classes. -/
@[simp]
theorem powerClass_div (g h : G) :
    powerClass n (g / h) = powerClass n g - powerClass n h := by
  simp only [powerClass, ofMul_div, map_sub]

/-- **A power class is trivial exactly when its representative is an `n`th power.** -/
@[simp]
theorem powerClass_eq_zero_iff {g : G} : powerClass n g = 0 ↔ ∃ h : G, h ^ n = g := by
  rw [powerClass_eq_mk, Submodule.Quotient.mk_eq_zero]
  change Additive.ofMul g ∈
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ))).toAddSubgroup ↔ _
  rw [modNSubgroup_eq_powerSubgroup, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]; exact Iff.rfl

/-- Two elements have the same power class exactly when their ratio is an `n`th power. -/
theorem powerClass_eq_iff {g h : G} :
    powerClass n g = powerClass n h ↔ ∃ v : G, v ^ n = g / h := by
  rw [← sub_eq_zero, ← powerClass_div, powerClass_eq_zero_iff]

end TauCeti
