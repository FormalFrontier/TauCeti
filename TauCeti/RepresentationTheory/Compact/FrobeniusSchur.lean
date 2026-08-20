/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Averaging
public import TauCeti.RepresentationTheory.Continuous.SquareCharacter
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Frobenius-Schur indicator of a compact group

For a finite-dimensional continuous representation `π` of a compact group `G`, the
**Frobenius-Schur indicator** is the Haar average of the character over squares,

`ν₂(π) = ∫_G χ_π(g²) dμ`,

with `μ` the normalized Haar measure of `TauCeti/RepresentationTheory/Compact/Haar.lean`. It is the
compact-group form of the finite average `|G|⁻¹ ∑_g χ(g²)` built in
`TauCeti/RepresentationTheory/CharacterTable/FrobeniusSchur/Basic.lean`; the integral replaces the
average and nothing else changes in the statement.

What the indicator computes is the signed difference of the two square characters. Over any field
`χ_{Sym²}(g) - χ_{Λ²}(g) = χ(g²)` (`Representation.char_symmetricSquare_sub_char_exteriorSquare`),
so integrating that identity gives

`ν₂(π) = ∫_G χ_{Sym²π} - ∫_G χ_{Λ²π}`,

and the companion identity `χ(g)² = χ_{Sym²}(g) + χ_{Λ²}(g)` gives the two integrals separately in
terms of `ν₂(π)` and `∫_G χ_π²`. Those two integrals are the (complexified) dimensions of the
invariants of the two squares once the projection onto invariants built from the Layer 0 averaging
operator is available; here only the character-level identities are proved, which is what makes them
independent of that development.

The two square characters are not, a priori, characters of *continuous* representations: the
symmetric and exterior square of a continuous representation carry a continuous action, but that
is not what is used. The closed formulas `χ_{Sym²}(g) = ½(χ(g)² + χ(g²))` and
`χ_{Λ²}(g) = ½(χ(g)² - χ(g²))`, valid because `2 ≠ 0`, exhibit both as continuous functions of `g`
directly, and that is all integration needs; that continuity is
`TauCeti/RepresentationTheory/Continuous/SquareCharacter.lean`, which needs neither a group nor a
measure, and only the integrability it yields is proved here.

For a **unitary** representation the indicator is real
(`ContRepresentation.conj_frobeniusSchurIndicator`): conjugating the character inverts its
argument, `(g²)⁻¹ = (g⁻¹)²`, and Haar measure on a compact group is inversion invariant. Its
modulus is at most `dim V`. That it takes only the values `1`, `0`, `-1` on an irreducible is the
reality trichotomy, which needs the invariant-form dictionary and is not proved here.

## Main definitions

* `ContRepresentation.frobeniusSchurIndicator`: `ν₂(π) = ∫_G χ_π(g²) dμ`.

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_of_equiv`: the indicator depends only on the
  equivalence class of the representation.
* `ContRepresentation.frobeniusSchurIndicator_eq_sub_integral`: **the indicator is the
  difference of the two square-character integrals**, `ν₂(π) = ∫ χ_{Sym²π} - ∫ χ_{Λ²π}`.
* `ContRepresentation.integral_character_sq`: the two square-character integrals add up to
  `∫ χ_π²`, so together with the previous statement they determine both:
  `ContRepresentation.integral_character_symmetricPower_two` and
  `ContRepresentation.integral_character_exteriorPower_two` are the resulting closed forms
  `½(∫ χ_π² ± ν₂(π))`.
* `ContRepresentation.conj_frobeniusSchurIndicator` and
  `ContRepresentation.im_frobeniusSchurIndicator`: the indicator of a unitary
  representation is real.
* `ContRepresentation.norm_frobeniusSchurIndicator_le`: it has modulus at most `dim V`.
* `ContRepresentation.frobeniusSchurIndicator_trivial`: the indicator of the trivial
  representation is its dimension, in particular `1` on the line.

## Implementation notes

The continuity hypothesis `hπ : Continuous π` is the one `TauCeti.ContRepresentation.character`
already carries: `ContRepresentation` bundles continuous action *operators* without asking that the
map to them be continuous. Since it is a `Prop` argument, two indicators built from different
continuity proofs are equal by proof irrelevance.

Everything below is declared in the **root** `ContRepresentation` namespace rather than in
`TauCeti.ContRepresentation`, so that `π.frobeniusSchurIndicator hπ` elaborates:
`ContRepresentation` is Mathlib's type, and a namespace for it nested inside `TauCeti` does not
support dot notation.
That is why the ambient `TauCeti` names this file consumes — `TauCeti.haarProb`,
`TauCeti.integrable_continuousMap`, `TauCeti.ContRepresentation.character` — are brought in by
`open` instead of by being in scope.

The scalars are `ℂ`, as the compact-groups roadmap pins them. That is not only convention here: the
symmetric- and exterior-power representations of
`TauCeti/RepresentationTheory/SymmetricPower.lean` and
`TauCeti/RepresentationTheory/ExteriorPower.lean`, whose characters the square identities below
speak of, are built over a base ring in `Type`, so a general `RCLike` field in an arbitrary universe
would not even let the statements be formed.

This is Layer 6b of the compact-groups roadmap, pinned in its
[`Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/Suggested.lean),
the compact-group half of the Frobenius-Schur reality invariant. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and Bröcker-tom Dieck,
*Representations of Compact Lie Groups*, Chapter II.
-/

public section

open MeasureTheory

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A continuous scalar function on a compact group is integrable against normalized Haar
measure. This is `TauCeti.integrable_continuousMap` with the continuous map assembled from a bare
continuity proof, which is the shape every integral below needs. -/
private theorem integrable_of_continuous {f : G → ℂ} (hf : Continuous f) :
    Integrable f (haarProb G) :=
  integrable_continuousMap G (⟨f, hf⟩ : C(G, ℂ))

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

/-- The character read along the squaring map is integrable against normalized Haar measure, so
the Frobenius-Schur indicator below is a genuine average and not the Bochner integral's junk
value. -/
theorem integrable_character_mul_self :
    Integrable (fun g : G ↦ character π hπ (g * g)) (haarProb G) :=
  integrable_of_continuous (continuous_character_mul_self π hπ)

/-- **The Frobenius-Schur indicator** of a finite-dimensional continuous representation of a
compact group: the Haar average `ν₂(π) = ∫_G χ_π(g²) dμ` of the character over squares. -/
noncomputable def frobeniusSchurIndicator : ℂ :=
  ∫ g, character π hπ (g * g) ∂(haarProb G)

/-- The defining integral of the Frobenius-Schur indicator. -/
theorem frobeniusSchurIndicator_def :
    frobeniusSchurIndicator π hπ = ∫ g, character π hπ (g * g) ∂(haarProb G) :=
  (rfl)

/-- **Equivalent representations have the same Frobenius-Schur indicator**, since they have the
same character (`Representation.char_iso`). The two continuity witnesses are unrelated: the
indicator reads only the underlying representation, so nothing links them. -/
theorem frobeniusSchurIndicator_eq_of_equiv {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (σ : ContRepresentation ℂ G W) (hσ : Continuous σ)
    (φ : Representation.Equiv π.toRepresentation σ.toRepresentation) :
    frobeniusSchurIndicator π hπ = frobeniusSchurIndicator σ hσ := by
  simp only [frobeniusSchurIndicator_def, coe_character, Representation.char_iso φ]

/-- The Frobenius-Schur indicator of the trivial representation is its dimension: every character
value is `dim V`, and Haar measure is normalized. On the line this is `ν₂ = 1`. -/
@[simp]
theorem frobeniusSchurIndicator_trivial :
    frobeniusSchurIndicator (ContRepresentation.trivial ℂ G V) continuous_const =
      (Module.finrank ℂ V : ℂ) := by
  -- `frobeniusSchurIndicator_def` gets its arguments explicitly: `continuous_const` has the
  -- required type only after unfolding `trivial`, which the matching of `rw` does not do.
  rw [frobeniusSchurIndicator_def (ContRepresentation.trivial ℂ G V) continuous_const]
  simp

/-! ### The two square characters

Over any field the difference of the symmetric-square and exterior-square characters is the
character at the square, and their sum is the square of the character. Integrating both identities
expresses the two square-character integrals through `ν₂(π)` and `∫ χ_π²`. -/

include hπ in
/-- The symmetric-square character is integrable against normalized Haar measure. -/
theorem integrable_character_symmetricPower_two :
    Integrable (fun g : G ↦ (π.toRepresentation.symmetricPower 2).character g) (haarProb G) :=
  integrable_of_continuous (continuous_character_symmetricPower_two π hπ two_ne_zero)

include hπ in
/-- The exterior-square character is integrable against normalized Haar measure. -/
theorem integrable_character_exteriorPower_two :
    Integrable (fun g : G ↦ (π.toRepresentation.exteriorPower 2).character g) (haarProb G) :=
  integrable_of_continuous (continuous_character_exteriorPower_two π hπ two_ne_zero)

/-- **The Frobenius-Schur indicator is the signed difference of the two square-character
integrals**, `ν₂(π) = ∫ χ_{Sym²π} - ∫ χ_{Λ²π}`.

This is the Haar average of `Representation.char_symmetricSquare_sub_char_exteriorSquare`, which
holds over every field, characteristic two included. Once the averaging projection identifies
`∫ χ_ρ` with the dimension of the invariants of `ρ`, the right-hand side becomes the signed count
`dim (Sym²V)ᴳ - dim (Λ²V)ᴳ` of the finite-group statement. -/
theorem frobeniusSchurIndicator_eq_sub_integral :
    frobeniusSchurIndicator π hπ =
      (∫ g, (π.toRepresentation.symmetricPower 2).character g ∂(haarProb G))
        - ∫ g, (π.toRepresentation.exteriorPower 2).character g ∂(haarProb G) := by
  rw [frobeniusSchurIndicator_def,
    ← integral_sub (integrable_character_symmetricPower_two π hπ)
      (integrable_character_exteriorPower_two π hπ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simpa only [coe_character] using
    (Representation.char_symmetricSquare_sub_char_exteriorSquare π.toRepresentation g).symm

/-- **The two square-character integrals add up to the integral of the squared character**,
`∫ χ_π² = ∫ χ_{Sym²π} + ∫ χ_{Λ²π}`. Together with
`ContRepresentation.frobeniusSchurIndicator_eq_sub_integral` this determines both. -/
theorem integral_character_sq :
    (∫ g, character π hπ g ^ 2 ∂(haarProb G)) =
      (∫ g, (π.toRepresentation.symmetricPower 2).character g ∂(haarProb G))
        + ∫ g, (π.toRepresentation.exteriorPower 2).character g ∂(haarProb G) := by
  rw [← integral_add (integrable_character_symmetricPower_two π hπ)
    (integrable_character_exteriorPower_two π hπ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  simpa only [coe_character] using Representation.char_tensorSquare π.toRepresentation g

/-- The symmetric-square character integrates to `½(∫ χ_π² + ν₂(π))`. -/
theorem integral_character_symmetricPower_two :
    (∫ g, (π.toRepresentation.symmetricPower 2).character g ∂(haarProb G))
      = ((∫ g, character π hπ g ^ 2 ∂(haarProb G)) + frobeniusSchurIndicator π hπ) / 2 := by
  rw [integral_character_sq π hπ, frobeniusSchurIndicator_eq_sub_integral π hπ]
  field_simp
  ring

/-- The exterior-square character integrates to `½(∫ χ_π² - ν₂(π))`. -/
theorem integral_character_exteriorPower_two :
    (∫ g, (π.toRepresentation.exteriorPower 2).character g ∂(haarProb G))
      = ((∫ g, character π hπ g ^ 2 ∂(haarProb G)) - frobeniusSchurIndicator π hπ) / 2 := by
  rw [integral_character_sq π hπ, frobeniusSchurIndicator_eq_sub_integral π hπ]
  field_simp
  ring

end CompactGroup

section Unitary

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

/-- **The Frobenius-Schur indicator of a unitary representation is real.**

Conjugating the character inverts its argument
(`TauCeti.ContRepresentation.character_apply_inv`), and `(g * g)⁻¹ = g⁻¹ * g⁻¹`, so the conjugate
indicator is the Haar average of `g ↦ χ(g⁻¹ * g⁻¹)`. Haar measure on a compact group is inversion
invariant, which returns that average to the original one. -/
@[simp]
theorem conj_frobeniusSchurIndicator (hunitary : IsUnitary π) :
    (starRingEnd ℂ) (frobeniusSchurIndicator π hπ) = frobeniusSchurIndicator π hπ := by
  rw [frobeniusSchurIndicator_def, ← integral_conj]
  have h : ∀ g : G, (starRingEnd ℂ) (character π hπ (g * g))
      = character π hπ (g⁻¹ * g⁻¹) := fun g ↦ by
    rw [← mul_inv_rev, character_apply_inv π hπ hunitary]
  rw [integral_congr_ae (Filter.Eventually.of_forall h)]
  exact integral_inv_eq_self (fun g : G ↦ character π hπ (g * g)) (haarProb G)

/-- The Frobenius-Schur indicator of a unitary representation has vanishing imaginary part: it is
a real number, the form in which the reality trichotomy `ν₂ ∈ {1, 0, -1}` is stated. -/
@[simp]
theorem im_frobeniusSchurIndicator (hunitary : IsUnitary π) :
    (frobeniusSchurIndicator π hπ).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_frobeniusSchurIndicator π hπ hunitary)

/-- The Frobenius-Schur indicator of a unitary representation has modulus at most the dimension:
every character value of a unitary representation does, and Haar measure is normalized. -/
theorem norm_frobeniusSchurIndicator_le (hunitary : IsUnitary π) :
    ‖frobeniusSchurIndicator π hπ‖ ≤ Module.finrank ℂ V := by
  rw [frobeniusSchurIndicator_def]
  simpa using norm_integral_le_of_norm_le_const (μ := haarProb G)
    (Filter.Eventually.of_forall fun g ↦ norm_character_apply_le π hπ hunitary (g * g))

end Unitary

end ContRepresentation
