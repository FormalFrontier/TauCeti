/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# One-dimensional representations from linear characters

A multiplicative character `χ : G →* kˣ` acts on the one-dimensional `k`-module `k` by scalar
multiplication. This file packages that action as `Representation.ofLinearCharacter χ` and records
the character, functoriality, and injectivity statements that let later constructions reason from
`χ` rather than unfold the representation.

The construction is the common core of the linear characters of the Borel subgroup and of
`GL₂`; keeping it here avoids separate scalar-action implementations for each group.

## Main definitions

* `Representation.ofLinearCharacter`: the one-dimensional representation associated to a
  unit-valued multiplicative character.

## Main results

* `Representation.ofLinearCharacter_apply`: the action is multiplication by the character value.
* `Representation.ofLinearCharacter_comp`: restriction of the representation is precomposition of
  the character.
* `Representation.ofLinearCharacter_injective`: the representation remembers its character.
* `Representation.char_ofLinearCharacter`: the trace character is the original character, coerced
  into the coefficient field.
-/

public section

universe u v

namespace Representation

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation associated to a multiplicative character.** An element
`g : G` acts on the line `k` by multiplication by the unit `χ g`. -/
def ofLinearCharacter [CommSemiring k] [Monoid G] (χ : G →* kˣ) : Representation k G k where
  toFun g := LinearMap.lsmul k k (χ g : k)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp only [map_mul, Units.val_mul, LinearMap.lsmul_apply, smul_eq_mul,
      Module.End.mul_apply]
    rw [mul_assoc]

/-- The representation associated to `χ` acts by multiplication by `χ`. -/
@[simp]
theorem ofLinearCharacter_apply [CommSemiring k] [Monoid G] (χ : G →* kˣ) (g : G) (x : k) :
    ofLinearCharacter χ g x = (χ g : k) * x :=
  (rfl)

/-- **Restricting a one-dimensional representation is precomposition of its character.** -/
@[simp]
theorem ofLinearCharacter_comp [CommSemiring k] [Monoid G] {H : Type*} [Monoid H]
    (χ : G →* kˣ) (f : H →* G) :
    (ofLinearCharacter χ).comp f = ofLinearCharacter (χ.comp f) := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro x
  rfl

/-- **The one-dimensional representation remembers its multiplicative character.** -/
theorem ofLinearCharacter_injective [CommSemiring k] [Monoid G] :
    Function.Injective (ofLinearCharacter : (G →* kˣ) → Representation k G k) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  apply Units.ext
  have := congrArg (fun ρ : Representation k G k => ρ g 1) h
  simpa using this

/-- **The trace character of a one-dimensional representation is its multiplicative character.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter χ).character g = (χ g : k) := by
  rw [character]
  have h : ofLinearCharacter χ g = LinearMap.id.smulRight (χ g : k) := by
    apply LinearMap.ext
    intro x
    simp [mul_comm]
  rw [h, LinearMap.trace_smulRight, LinearMap.id_apply]

end Representation
