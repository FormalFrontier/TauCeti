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
# The one-dimensional representation carrying a linear character

A **linear character** of a monoid `G` over a commutative semiring `k` is a homomorphism
`χ : G →* kˣ`.  It carries a representation on the line `k` itself, with `g` acting by
multiplication by `χ g`.  This file builds that representation, first as a
`Representation k G k` and then as an object of `FDRep k G`, and records the facts every consumer
of a linear character needs: its character is `χ`, it is a line, it is a simple object, it
restricts along a homomorphism by pulling `χ` back, and two of them are isomorphic exactly when
the two characters are equal.

This is the smallest nonzero representation there is, and it is what the induction machinery is
fed in the classical worked examples: `Ind_H^G` of a linear character of a subgroup is a
*monomial* representation, and its irreducibility is what the Mackey criterion decides.

## Main definitions

* `TauCeti.Representation.ofLinearChar`: the representation of `G` on `k` in which `g` acts by
  multiplication by `χ g`.
* `TauCeti.FDRep.ofLinearChar`: the same representation as an object of `FDRep k G`.

## Main statements

* `TauCeti.Representation.character_ofLinearChar` and `TauCeti.FDRep.character_ofLinearChar`: the
  character of the one-dimensional representation is the linear character it was built from.
* `TauCeti.FDRep.finrank_ofLinearChar`: it is a line.
* `TauCeti.FDRep.simple_ofLinearChar`: it is a simple object of `FDRep k G`, being a line.
* `TauCeti.FDRep.actionRes_obj_ofLinearChar`: restricting along `f : S →* G` gives the
  one-dimensional representation of the pulled-back character `χ ∘ f`.
* `TauCeti.FDRep.nonempty_iso_ofLinearChar_iff`: two of these are isomorphic exactly when the two
  linear characters are equal.

## Implementation notes

`TauCeti.Representation.ofLinearChar` keeps its body private: `ofLinearChar_apply` characterizes
every use of it.  `TauCeti.FDRep.ofLinearChar` is `@[expose]` because it has to be: the carrier of
an object of `FDRep k G` is part of that object's data, so with the body hidden the two sides of
`TauCeti.FDRep.ofLinearChar_ρ` live in different types and its statement does not elaborate at all.
Consumers are still expected to go through the lemmas rather than the body.  That the carrier is
the line `k` **on the nose** is recorded once and for all by
`TauCeti.FDRep.actionRes_obj_ofLinearChar`, an honest equality of objects rather than an
isomorphism; conjugation, restriction and comparison of these objects are then computed inside
`G →* kˣ` through it and `TauCeti.FDRep.nonempty_iso_ofLinearChar_iff`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

namespace Representation

section CommSemiring

variable {k : Type u} {G : Type v} [CommSemiring k] [Monoid G]

/-- **The one-dimensional representation carrying a linear character** `χ : G →* kˣ`: the
representation of `G` on the line `k` in which `g` acts by multiplication by `χ g`. -/
def ofLinearChar (χ : G →* kˣ) : Representation k G k where
  toFun g := LinearMap.lsmul k k (χ g : k)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp only [map_mul, Units.val_mul, LinearMap.lsmul_apply, smul_eq_mul, Module.End.mul_apply]
    ring

@[simp]
theorem ofLinearChar_apply (χ : G →* kˣ) (g : G) (x : k) :
    ofLinearChar χ g x = (χ g : k) * x :=
  (rfl)

/-- **The trivial linear character carries the trivial representation.**  This is the sanity check
that fixes the convention: `χ = 1` acts by the scalar `1`. -/
theorem ofLinearChar_one : ofLinearChar (1 : G →* kˣ) = Representation.trivial k G k :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by simp

end CommSemiring

section Field

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- **The character of a one-dimensional representation is the scalar it acts by**: the trace of
multiplication by `c` on the line `k` is `c`. -/
@[simp]
theorem character_ofLinearChar (χ : G →* kˣ) (g : G) :
    (ofLinearChar χ).character g = (χ g : k) := by
  rw [Representation.character]
  have h : ofLinearChar χ g = LinearMap.id.smulRight (χ g : k) :=
    LinearMap.ext fun x => by simp [mul_comm]
  rw [h, LinearMap.trace_smulRight, LinearMap.id_apply]

/-- A one-dimensional representation is irreducible, having no room for a proper nonzero
subrepresentation. -/
instance isIrreducible_ofLinearChar (χ : G →* kˣ) :
    (ofLinearChar (k := k) χ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

end Field

end Representation

namespace FDRep

section CommRing

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

/-- **The one-dimensional representation carrying a linear character, as an object of
`FDRep k G`.**  This is the shape induction consumes. -/
@[expose]
noncomputable def ofLinearChar (χ : G →* kˣ) : FDRep k G :=
  FDRep.of (Representation.ofLinearChar χ)

@[simp]
theorem ofLinearChar_ρ (χ : G →* kˣ) :
    (ofLinearChar (k := k) χ).ρ = Representation.ofLinearChar χ :=
  (rfl)

/-- **Restricting a linear character along a homomorphism pulls the character back.**  Both sides
are the line `k` with `s` acting by the scalar `χ (f s)`, so this is an equality of objects, not
merely an isomorphism; it is what lets conjugation and restriction of a one-dimensional
representation be computed inside `G →* kˣ`. -/
theorem actionRes_obj_ofLinearChar {S : Type*} [Monoid S] (f : S →* G) (χ : G →* kˣ) :
    (Action.res (FGModuleCat k) f).obj (ofLinearChar χ) = ofLinearChar (χ.comp f) :=
  (rfl)

end CommRing

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

/-- A linear character is carried by a line. -/
@[simp]
theorem finrank_ofLinearChar (χ : G →* kˣ) :
    Module.finrank k (ofLinearChar (k := k) χ) = 1 :=
  Module.finrank_self k

/-- **The character of `TauCeti.FDRep.ofLinearChar` is the linear character it was built from.** -/
@[simp]
theorem character_ofLinearChar (χ : G →* kˣ) (g : G) :
    (ofLinearChar (k := k) χ).character g = (χ g : k) :=
  Representation.character_ofLinearChar χ g

/-- **The one-dimensional representation of a linear character is a simple object**, being a
line. -/
instance simple_ofLinearChar (χ : G →* kˣ) : Simple (ofLinearChar (k := k) χ) :=
  have : Representation.IsIrreducible (ofLinearChar (k := k) χ).ρ :=
    Representation.isIrreducible_ofLinearChar χ
  FDRep.simple_of_isIrreducible _

/-- **Two one-dimensional representations are isomorphic exactly when their linear characters
agree.**  One direction is that an isomorphism preserves characters, and the character of
`TauCeti.FDRep.ofLinearChar χ` is `χ`; the other is that equal characters give literally the same
object. -/
theorem nonempty_iso_ofLinearChar_iff (χ ψ : G →* kˣ) :
    Nonempty (ofLinearChar (k := k) χ ≅ ofLinearChar ψ) ↔ χ = ψ := by
  refine ⟨fun ⟨e⟩ => MonoidHom.ext fun g => Units.ext ?_, fun h => ⟨h ▸ Iso.refl _⟩⟩
  have h := congrArg (fun c => c g) (FDRep.char_iso e)
  simpa using h

end FDRep

end TauCeti
