/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.Tensor.Square

/-!
# Continuity of the two square characters

The symmetric square and the exterior square of a representation have characters
`χ_{Sym²}` and `χ_{Λ²}`; away from characteristic two they are determined by the character of the
representation through `χ_{Sym²}(g) = ½(χ(g)² + χ(g²))` and `χ_{Λ²}(g) = ½(χ(g)² - χ(g²))`
(`Representation.char_symmetricSquare` and `Representation.char_exteriorSquare` of
`TauCeti/RepresentationTheory/Tensor/Square.lean`). For a representation with continuous
operator-valued action those closed formulas exhibit both square characters as continuous functions
of `g`, which is what this file records.

Neither statement needs the symmetric or exterior square to be assembled as a *continuous*
representation: the closed formulas are used as they stand, so only the continuity of `χ` and of
`g ↦ χ(g * g)` (`ContRepresentation.continuous_character_mul_self`) enters.

## Main statements

* `ContRepresentation.continuous_character_symmetricPower_two` and
  `ContRepresentation.continuous_character_exteriorPower_two`: the two square characters of a
  continuous representation are continuous.

## Implementation notes

Nothing here needs a group, a measure, or compactness, so the statements are made over a
topological monoid; the consumer is
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Basic.lean`, where continuity supplies the
integrability of the two square characters against Haar measure.

The scalars are a complete nontrivially normed field `𝕜` with `2 ≠ 0` — exactly what the trace
functional behind `TauCeti.ContRepresentation.character` and the closed formulas ask for; the
consumer instantiates them at `ℂ`. `𝕜` is in `Type` rather than `Type*` because the symmetric- and
exterior-power representations of `TauCeti/RepresentationTheory/SymmetricPower.lean` and
`TauCeti/RepresentationTheory/ExteriorPower.lean`, whose characters are spoken of here, are built
over a base ring in `Type`, so a field in an arbitrary universe would not even let the statements
be formed. The hypothesis `2 ≠ 0` is explicit rather than a `CharZero`-style instance because that
is the shape `Representation.char_symmetricSquare` and `Representation.char_exteriorSquare` carry.

Both declarations sit in the **root** `ContRepresentation` namespace, so that
`π.continuous_character_symmetricPower_two hπ` elaborates: `ContRepresentation` is Mathlib's type,
and `scripts/lint-dot-notation.py` asks that new declarations about it not recreate its namespace
inside `TauCeti`. That is why the ambient `TauCeti` name this file consumes,
`TauCeti.ContRepresentation.character`, is brought in by `open`.
-/

public section

open TauCeti.ContRepresentation

namespace ContRepresentation

variable {𝕜 : Type} {G V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

include hπ in
/-- The symmetric-square character is continuous, being `½(χ(g)² + χ(g²))`. -/
theorem continuous_character_symmetricPower_two (h2 : (2 : 𝕜) ≠ 0) :
    Continuous fun g : G ↦ (π.toRepresentation.symmetricPower 2).character g := by
  have h : (fun g : G ↦ (π.toRepresentation.symmetricPower 2).character g)
      = fun g : G ↦ (character π hπ g ^ 2 + character π hπ (g * g)) / 2 := by
    funext g
    simpa only [coe_character] using
      Representation.char_symmetricSquare π.toRepresentation g h2
  rw [h]
  exact (((character π hπ).continuous.pow 2).add
    (continuous_character_mul_self π hπ)).div_const 2

include hπ in
/-- The exterior-square character is continuous, being `½(χ(g)² - χ(g²))`. -/
theorem continuous_character_exteriorPower_two (h2 : (2 : 𝕜) ≠ 0) :
    Continuous fun g : G ↦ (π.toRepresentation.exteriorPower 2).character g := by
  have h : (fun g : G ↦ (π.toRepresentation.exteriorPower 2).character g)
      = fun g : G ↦ (character π hπ g ^ 2 - character π hπ (g * g)) / 2 := by
    funext g
    simpa only [coe_character] using
      Representation.char_exteriorSquare π.toRepresentation g h2
  rw [h]
  exact (((character π hπ).continuous.pow 2).sub
    (continuous_character_mul_self π hπ)).div_const 2

end ContRepresentation
