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
# One-dimensional representations, and the linear characters that name them

A **linear character** of a monoid `G` over a commutative ring `k` is a homomorphism
`ψ : G →* kˣ`. It carries a representation on `k` itself, with `g` acting by multiplication by
`ψ g`; conversely every representation on a line is of that shape. This file builds that
representation, computes its character — which is `ψ` again, read in `k` — and records that over a
field it is irreducible, hence a simple object of `FDRep k G`.

These are the smallest representations there are, and they are how the smallest constituents of a
character table are written down: the trivial representation, the sign of a permutation, a
faithful character of a cyclic group. Mathlib has `Representation.trivial` but no construction
from a general `ψ`, so the one below fills that gap.

Note that `ψ` is valued in the **units** `kˣ`, not in `k`: a homomorphism to the multiplicative
monoid of `k` would allow `ψ g = 0`, and the resulting `ρ g` would then not be invertible.

## Main definitions

* `TauCeti.Representation.ofLinearChar`: the one-dimensional representation of a linear character.

## Main statements

* `TauCeti.Representation.character_ofLinearChar`: its character is the linear character itself.
* `TauCeti.Representation.isIrreducible_ofLinearChar`, `TauCeti.Representation.simple_ofLinearChar`:
  it is irreducible, being a line, hence a simple object of `FDRep k G`.
* `TauCeti.Representation.eq_of_nonempty_iso_ofLinearChar`: two linear characters whose
  representations are isomorphic are equal, so a linear character is recovered from the
  isomorphism class of the object it names.

## References

Linear characters are the degree-one rows of a character table; see
[the character-theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

open CategoryTheory

namespace TauCeti

namespace Representation

section Def

variable {k : Type*} [CommRing k] {G : Type*} [Monoid G]

/-- **The one-dimensional representation of a linear character** `ψ : G →* kˣ`: the representation
of `G` on `k` in which `g` acts by multiplication by `ψ g`. -/
def ofLinearChar (ψ : G →* kˣ) : _root_.Representation k G k where
  toFun g := (ψ g : k) • LinearMap.id
  map_one' := LinearMap.ext fun x => by simp
  map_mul' g h := LinearMap.ext fun x => by
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, smul_eq_mul]
    ring

@[simp]
theorem ofLinearChar_apply (ψ : G →* kˣ) (g : G) (x : k) :
    ofLinearChar ψ g x = (ψ g : k) * x := by
  change ((ψ g : k) • LinearMap.id) x = _
  simp

/-- Precomposing the representation of a linear character with a homomorphism is the
representation of the precomposed linear character. -/
theorem ofLinearChar_comp {G' : Type*} [Monoid G'] (ψ : G →* kˣ) (f : G' →* G) :
    (ofLinearChar ψ).comp f = ofLinearChar (ψ.comp f) :=
  (rfl)

end Def

section Field

variable {k : Type*} [Field k] {G : Type*} [Monoid G]

/-- **The character of a linear character is itself**, read in `k`: the trace of multiplication
by `ψ g` on the line `k`. -/
@[simp]
theorem character_ofLinearChar (ψ : G →* kˣ) (g : G) :
    (FDRep.of (ofLinearChar ψ)).character g = ψ g := by
  change LinearMap.trace k k (ofLinearChar ψ g) = _
  rw [show ofLinearChar ψ g = (ψ g : k) • LinearMap.id from rfl,
    map_smul, LinearMap.trace_id, Module.finrank_self]
  simp

/-- **A linear character is irreducible**: it is carried by a line. -/
instance isIrreducible_ofLinearChar (ψ : G →* kˣ) : (ofLinearChar ψ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- The finite-dimensional object carrying a linear character is a simple object of
`FDRep k G`. -/
instance simple_ofLinearChar (ψ : G →* kˣ) : Simple (FDRep.of (ofLinearChar ψ)) := by
  rw [FDRep.simple_iff_isIrreducible]
  exact isIrreducible_ofLinearChar ψ

/-- **Isomorphic linear characters are equal.** An isomorphism of the two one-dimensional
representations identifies their characters, and the character of `ofLinearChar ψ` is `ψ`. -/
theorem eq_of_nonempty_iso_ofLinearChar {ψ φ : G →* kˣ}
    (h : Nonempty (FDRep.of (ofLinearChar ψ) ≅ FDRep.of (ofLinearChar φ))) : ψ = φ := by
  obtain ⟨e⟩ := h
  have hchar := FDRep.char_iso e
  ext g
  simpa using congrFun hchar g

end Field

end Representation

end TauCeti
