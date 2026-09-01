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
definitionally `TauCeti.ElementaryTwoQuotient G`. The Kummer map uses the multiplicative quotient,
while `TauCeti.powerClassEquivQuotient` identifies it with the additive `ModN` model.

This implements target 3 of Layer 9 in the human-authored
`TauCetiRoadmap/ProfiniteCohomology/README.md` and `Suggested.lean`.

## Main definitions

* `TauCeti.PowerClassGroup`: the quotient `G ⧸ Gⁿ`, written additively.
* `TauCeti.powerSubgroup`, `TauCeti.powerClassQuotient`: the multiplicative subgroup and quotient
  specified by the roadmap.
* `TauCeti.powerClass`, `TauCeti.powerClassHom`: the `n`th power class of an element, with
  `TauCeti.powerClass_eq_zero_iff` characterising the trivial class as the `n`th powers.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] (n : ℕ)

/-- **The subgroup of `n`th powers** `Gⁿ ≤ G`. -/
def powerSubgroup : Subgroup G :=
  (powMonoidHom n : G →* G).range

/-- **The multiplicative quotient by `n`th powers** `G ⧸ Gⁿ`. -/
abbrev powerClassQuotient : Type _ :=
  G ⧸ powerSubgroup G n

/-- **The group of `n`th power classes** `G ⧸ Gⁿ`, written additively on `Additive G`. The
subgroup divided out is the range of `powMonoidHom n`, that is `{g ^ n | g : G}`. -/
abbrev PowerClassGroup : Type _ :=
  ModN (Additive G) n

instance (priority := 90) [Finite G] : Finite (PowerClassGroup G n) :=
  Finite.of_surjective (ModN.mkQ n) (Submodule.Quotient.mk_surjective _)

variable {G}

/-- The subgroup defining Mathlib's `ModN (Additive G) n` is the additive form of the subgroup of
`n`th powers in `G`. -/
theorem modNSubgroup_eq_powerSubgroup :
    (LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ))).toAddSubgroup =
      (powerSubgroup G n).toAddSubgroup := by
  ext a
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_range, LinearMap.lsmul_apply,
    Additive.mem_toAddSubgroup]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.toMul, ?_⟩
    simpa only [powMonoidHom_apply, natCast_zsmul, toMul_nsmul] using
      congrArg Additive.toMul hb
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    apply Additive.toMul.injective
    simpa only [powMonoidHom_apply, natCast_zsmul, toMul_nsmul, toMul_ofMul] using hb

/-- Mathlib's additive `ModN` model is canonically equivalent to the additive form of the
multiplicative quotient `G ⧸ Gⁿ`. -/
def powerClassEquivQuotient :
    PowerClassGroup G n ≃+ Additive (powerClassQuotient G n) :=
  QuotientAddGroup.quotientAddEquivOfEq (modNSubgroup_eq_powerSubgroup (G := G) (n := n))

/-- The multiplicative quotient homomorphism `G → G ⧸ Gⁿ`. -/
def powerClassHom : G →* powerClassQuotient G n :=
  QuotientGroup.mk' (powerSubgroup G n)

/-- The multiplicative power-class homomorphism sends `g` to its quotient class. -/
@[simp]
theorem powerClassHom_apply (g : G) : powerClassHom n g = QuotientGroup.mk g := by
  exact QuotientGroup.mk'_apply (powerSubgroup G n) g

/-- An element belongs to `Gⁿ` exactly when it is an `n`th power. -/
@[simp]
theorem mem_powerSubgroup_iff {g : G} : g ∈ powerSubgroup G n ↔ ∃ h : G, h ^ n = g := by
  rw [powerSubgroup, MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]

/-- Lift a homomorphism that kills `Gⁿ` to the quotient `G ⧸ Gⁿ`. -/
def powerClassQuotientLift {H : Type*} [Group H] (f : G →* H)
    (hf : powerSubgroup G n ≤ f.ker) : powerClassQuotient G n →* H :=
  QuotientGroup.lift (powerSubgroup G n) f hf

/-- A lift from the power-class quotient agrees with the original homomorphism on
representatives. -/
@[simp]
theorem powerClassQuotientLift_mk {H : Type*} [Group H] (f : G →* H)
    (hf : powerSubgroup G n ≤ f.ker) (g : G) :
    powerClassQuotientLift n f hf (powerClassHom n g) = f g := by
  exact QuotientGroup.lift_mk' (powerSubgroup G n) hf g

/-- The additive quotient homomorphism `Additive G →+ PowerClassGroup G n`. -/
def powerClassAdd : Additive G →+ PowerClassGroup G n :=
  ModN.mkQ n

/-- The `n`th power class of an element of `G`. -/
def powerClass (g : G) : PowerClassGroup G n :=
  powerClassAdd n (Additive.ofMul g)

/-- The canonical equivalence sends the additive `ModN` class of `g` to its multiplicative
quotient class. -/
@[simp]
theorem powerClassEquivQuotient_powerClass (g : G) :
    powerClassEquivQuotient (G := G) (n := n) (powerClass n g) =
      Additive.ofMul (powerClassHom n g) := by
  exact QuotientAddGroup.quotientAddEquivOfEq_mk
    (modNSubgroup_eq_powerSubgroup (G := G) (n := n)) (Additive.ofMul g)

/-- The power class is the quotient class of the element in Mathlib's `ModN` model. -/
theorem powerClass_eq_mk (g : G) :
    powerClass n g = Submodule.Quotient.mk (Additive.ofMul g) := by
  exact Submodule.mkQ_apply _ _

/-- Every class in `PowerClassGroup G n` has a representative in `G`. -/
theorem powerClass_surjective : Function.Surjective (powerClass (G := G) n) := by
  intro x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨a.toMul, by simpa using powerClass_eq_mk n a.toMul⟩

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

/-- The class of an inverse is the negative of the class. -/
@[simp]
theorem powerClass_inv (g : G) : powerClass n g⁻¹ = -powerClass n g := by
  simp only [powerClass, ofMul_inv, map_neg]

/-- The class of a power is the corresponding multiple of the class. -/
@[simp]
theorem powerClass_pow (g : G) (m : ℕ) : powerClass n (g ^ m) = m • powerClass n g := by
  simp only [powerClass, ofMul_pow, map_nsmul]

/-- The class of a finite product is the sum of the classes. -/
theorem powerClass_prod {ι : Type*} (s : Finset ι) (g : ι → G) :
    powerClass n (∏ i ∈ s, g i) = ∑ i ∈ s, powerClass n (g i) := by
  simp only [powerClass, ofMul_prod, map_sum]

/-- Membership in the submodule defining `ModN (Additive G) n` is membership in `Gⁿ`, expressed
on multiplicative representatives. -/
theorem mem_modNSubgroup_iff {g : G} :
    Additive.ofMul g ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ)) ↔
      ∃ h : G, h ^ n = g := by
  rw [show Additive.ofMul g ∈ LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ)) ↔
      Additive.ofMul g ∈
        (LinearMap.range (LinearMap.lsmul ℤ (Additive G) (n : ℤ))).toAddSubgroup from Iff.rfl]
  rw [modNSubgroup_eq_powerSubgroup, Additive.mem_toAddSubgroup, powerSubgroup,
    MonoidHom.mem_range]
  exact exists_congr fun h => by rw [powMonoidHom_apply]; exact Iff.rfl

/-- **A power class is trivial exactly when its representative is an `n`th power.** -/
@[simp]
theorem powerClass_eq_zero_iff {g : G} : powerClass n g = 0 ↔ ∃ h : G, h ^ n = g := by
  rw [powerClass_eq_mk, Submodule.Quotient.mk_eq_zero]
  exact mem_modNSubgroup_iff (n := n)

/-- Two elements have the same power class exactly when their ratio is an `n`th power. -/
theorem powerClass_eq_iff {g h : G} :
    powerClass n g = powerClass n h ↔ ∃ v : G, v ^ n = g / h := by
  rw [← sub_eq_zero, ← powerClass_div, powerClass_eq_zero_iff]

end TauCeti
