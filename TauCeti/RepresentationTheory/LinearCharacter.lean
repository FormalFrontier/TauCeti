/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# One-dimensional representations from linear characters

A **linear character** of a monoid `G` over a commutative semiring `k` is a multiplicative
character `χ : G →* kˣ`. It acts on the one-dimensional `k`-module `k` by scalar multiplication.
This file packages that action as `Representation.ofLinearCharacter χ`, bundles it as an object
`FDRep.ofLinearCharacter χ` of `FDRep k G`, and records the facts every consumer of a linear
character needs: its character is `χ`, it is a line, it is simple, it restricts along a
homomorphism by pulling `χ` back, and two of them are isomorphic exactly when the two characters
are equal.

The construction is the common core of the linear characters of the Borel subgroup and of
`GL₂`; keeping it here avoids separate scalar-action implementations for each group. It is also
the smallest nonzero representation there is, and it is what the induction machinery is fed in the
classical worked examples: `Ind_H^G` of a linear character of a subgroup is a *monomial*
representation, and its irreducibility is what the Mackey criterion decides.

## Main definitions

* `Representation.ofLinearCharacter`: the one-dimensional representation associated to a
  unit-valued multiplicative character.
* `FDRep.ofLinearCharacter`: the same representation as an object of `FDRep k G`.

## Main results

* `Representation.ofLinearCharacter_apply`: the action is multiplication by the character value.
* `Representation.ofLinearCharacter_comp`: restriction of the representation is precomposition of
  the character.
* `Representation.ofLinearCharacter_injective`: the representation remembers its character.
* `Representation.ofLinearCharacter_one`: the trivial character carries the trivial
  representation.
* `Representation.char_ofLinearCharacter` and `FDRep.char_ofLinearCharacter`: the trace character
  is the original character, coerced into the coefficient field.
* `Representation.isIrreducible_ofLinearCharacter`: a line has no room for a proper nonzero
  subrepresentation.
* `FDRep.finrank_ofLinearCharacter`: it is a line.
* `FDRep.simple_ofLinearCharacter`: it is a simple object of `FDRep k G`, being a line.
* `FDRep.actionRes_obj_ofLinearCharacter`: restricting along `f : S →* G` gives the
  one-dimensional representation of the pulled-back character `χ ∘ f`.
* `FDRep.nonempty_iso_ofLinearCharacter_iff`: two of these are isomorphic exactly when the two
  linear characters are equal.

## Implementation notes

`FDRep.ofLinearCharacter` is `@[expose]` because it has to be: the carrier of an object of
`FDRep k G` is part of that object's data, so with the body hidden the two sides of
`FDRep.ofLinearCharacter_ρ` live in different types and its statement does not elaborate at all.
Consumers are still expected to go through the lemmas rather than the body. That the carrier is
the line `k` **on the nose** is recorded once and for all by
`FDRep.actionRes_obj_ofLinearCharacter`, an honest equality of objects rather than an isomorphism;
conjugation, restriction and comparison of these objects are then computed inside `G →* kˣ`
through it and `FDRep.nonempty_iso_ofLinearCharacter_iff`.
-/

public section

open CategoryTheory

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

/-- **The trivial linear character carries the trivial representation.** This is the sanity check
that fixes the convention: `χ = 1` acts by the scalar `1`. -/
@[simp]
theorem ofLinearCharacter_one [CommSemiring k] [Monoid G] :
    ofLinearCharacter (1 : G →* kˣ) = Representation.trivial k G k :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by simp

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

/-- A one-dimensional representation is irreducible, having no room for a proper nonzero
subrepresentation. -/
instance isIrreducible_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    (ofLinearCharacter (k := k) χ).IsIrreducible :=
  TauCeti.Representation.isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

end Representation

namespace FDRep

variable {k : Type u} {G : Type v}

/-- **The one-dimensional representation carrying a linear character, as an object of
`FDRep k G`.** This is the shape induction consumes. -/
@[expose]
noncomputable def ofLinearCharacter [CommRing k] [Monoid G] (χ : G →* kˣ) : FDRep k G :=
  FDRep.of (Representation.ofLinearCharacter χ)

@[simp]
theorem ofLinearCharacter_ρ [CommRing k] [Monoid G] (χ : G →* kˣ) :
    (ofLinearCharacter (k := k) χ).ρ = Representation.ofLinearCharacter χ :=
  (rfl)

/-- **Restricting a linear character along a homomorphism pulls the character back.** Both sides
are the line `k` with `s` acting by the scalar `χ (f s)`, so this is an equality of objects, not
merely an isomorphism; it is what lets conjugation and restriction of a one-dimensional
representation be computed inside `G →* kˣ`. -/
@[simp]
theorem actionRes_obj_ofLinearCharacter [CommRing k] [Monoid G] {S : Type*} [Monoid S]
    (f : S →* G) (χ : G →* kˣ) :
    (Action.res (FGModuleCat k) f).obj (ofLinearCharacter χ) = ofLinearCharacter (χ.comp f) :=
  (rfl)

/-- A linear character is carried by a line. -/
@[simp]
theorem finrank_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Module.finrank k (ofLinearCharacter (k := k) χ) = 1 :=
  Module.finrank_self k

/-- **The character of `FDRep.ofLinearCharacter` is the linear character it was built from.** -/
@[simp]
theorem char_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) (g : G) :
    (ofLinearCharacter (k := k) χ).character g = (χ g : k) :=
  Representation.char_ofLinearCharacter χ g

/-- **The one-dimensional representation of a linear character is a simple object**, being a
line. -/
instance simple_ofLinearCharacter [Field k] [Monoid G] (χ : G →* kˣ) :
    Simple (ofLinearCharacter (k := k) χ) :=
  have : Representation.IsIrreducible (ofLinearCharacter (k := k) χ).ρ :=
    Representation.isIrreducible_ofLinearCharacter χ
  FDRep.simple_of_isIrreducible _

/-- **Two one-dimensional representations are isomorphic exactly when their linear characters
agree.** One direction is that an isomorphism preserves characters, and the character of
`FDRep.ofLinearCharacter χ` is `χ`; the other is that equal characters give literally the same
object. -/
@[simp]
theorem nonempty_iso_ofLinearCharacter_iff [Field k] [Monoid G] (χ ψ : G →* kˣ) :
    Nonempty (ofLinearCharacter (k := k) χ ≅ ofLinearCharacter ψ) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => MonoidHom.ext fun g => Units.ext ?_, fun h => ⟨h ▸ Iso.refl _⟩⟩
  have h := congrArg (fun c => c g) (FDRep.char_iso e)
  simpa using h

end FDRep
