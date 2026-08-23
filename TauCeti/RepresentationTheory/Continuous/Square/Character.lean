/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.Character
public import TauCeti.RepresentationTheory.Continuous.Square.Basic
public import TauCeti.RepresentationTheory.Tensor.Square

/-!
# The characters of the two squares of a continuous representation

The symmetric square and the exterior square of a representation have characters
`χ_{Sym²}` and `χ_{Λ²}`; away from characteristic two they are determined by the character of the
representation through `χ_{Sym²}(g) = ½(χ(g)² + χ(g²))` and `χ_{Λ²}(g) = ½(χ(g)² - χ(g²))`
(`Representation.char_symmetricSquare` and `Representation.char_exteriorSquare` of
`TauCeti/RepresentationTheory/Tensor/Square.lean`). For a representation with continuous
operator-valued action those closed formulas exhibit both square characters as continuous functions
of `g`, which is what the first section records.

Neither continuity statement needs the symmetric or exterior square to be assembled as a
*continuous* representation: the closed formulas are used as they stand, so only the continuity of
`χ` and of `g ↦ χ(g * g)` (`ContRepresentation.continuous_character_mul_self`) enters.

The second section reads the *difference* of the two square characters on the squares that
`TauCeti/RepresentationTheory/Continuous/Square/Basic.lean` does assemble as continuous
representations, the eigenspaces of the flip inside `V ⊗[𝕜] V`: there
`χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)`, which is the linear-algebra identity
`TauCeti.trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict` applied to `π g`.
Subtracting the two closed formulas above gives the same identity on the powers, so the two
sections agree wherever both apply.

## Main statements

* `ContRepresentation.continuous_character_symmetricPower_two` and
  `ContRepresentation.continuous_character_exteriorPower_two`: the two square characters of a
  continuous representation are continuous.
* `ContRepresentation.character_symmetricSquare_sub_character_exteriorSquare`: the characters of
  the symmetric and the exterior square differ by the character at the square,
  `χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)`.

## Implementation notes

Nothing here needs a group, a measure, or compactness, so the statements are made over a
topological monoid; the consumers are
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Basic.lean`, where continuity supplies the
integrability of the two square characters against Haar measure, and
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/InvariantTensors.lean`, where the pointwise
identity is integrated against it.

The two sections ask different things of the scalars. For the continuity statements they are a
complete nontrivially normed field `𝕜` with `2 ≠ 0` — exactly what the trace functional behind
`TauCeti.ContRepresentation.character` and the closed formulas ask for; the consumer instantiates
them at `ℂ`. There `𝕜` is in `Type` rather than `Type*` because the symmetric- and exterior-power
representations of `TauCeti/RepresentationTheory/SymmetricPower.lean` and
`TauCeti/RepresentationTheory/ExteriorPower.lean`, whose characters are spoken of, are built over a
base ring in `Type`, so a field in an arbitrary universe would not even let the statements be
formed. The hypothesis `2 ≠ 0` is explicit rather than a `CharZero`-style instance because that is
the shape `Representation.char_symmetricSquare` and `Representation.char_exteriorSquare` carry. The
pointwise identity instead needs the two squares of
`TauCeti/RepresentationTheory/Continuous/Square/Basic.lean`, whose carriers are submodules of an
inner product space, so its scalars are `RCLike 𝕜`, in any universe, and `2` is invertible there by
instance.

All declarations sit in the **root** `ContRepresentation` namespace, so that
`π.continuous_character_symmetricPower_two hπ` elaborates: `ContRepresentation` is Mathlib's type,
and `scripts/lint-dot-notation.py` asks that new declarations about it not recreate its namespace
inside `TauCeti`. That is why the ambient `TauCeti` names this file consumes are brought in by
`open`.
-/

public section

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section Powers

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

end Powers

section TensorSquare

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [TopologicalSpace G]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)

/-- **The two square characters differ by the character at the square**,
`χ_{Sym²π}(g) - χ_{Λ²π}(g) = χ_π(g²)`.

This is `TauCeti.trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict` applied to
the operator `π g`, whose square is `π (g * g)`. -/
theorem character_symmetricSquare_sub_character_exteriorSquare (g : G) :
    character (𝕜 := 𝕜) (V := symmetricTensors 𝕜 V) (symmetricSquare π)
          (continuous_symmetricSquare π hπ) g
        - character (𝕜 := 𝕜) (V := antisymmetricTensors 𝕜 V) (exteriorSquare π)
          (continuous_exteriorSquare π hπ) g
      = character π hπ (g * g) := by
  rw [character_apply, character_apply, character_apply, symmetricSquare_apply π g,
    exteriorSquare_apply π g,
    trace_symmetricTensorsRestrict_sub_trace_antisymmetricTensorsRestrict (π g : V →ₗ[𝕜] V)]
  congr 1
  rw [map_mul, ContinuousLinearMap.toLinearMap_mul, Module.End.mul_eq_comp]

end TensorSquare

end ContRepresentation
