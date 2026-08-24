/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.FrobeniusSchur.Basic
public import TauCeti.RepresentationTheory.Compact.Invariants

/-!
# The Frobenius-Schur indicator counts invariant tensors

For a finite-dimensional continuous representation `π` of a compact group `G`, the Frobenius-Schur
indicator `ν₂(π) = ∫_G χ_π(g²) dμ` of
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Basic.lean` is the **signed count of invariant
tensors**,

`ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`,

the compact-group form of the finite-group identity
`TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`.

The two squares are realized *inside* the tensor square `V ⊗[ℂ] V`, as the two eigenspaces of the
flip `x ⊗ y ↦ y ⊗ x` (`TauCeti.symmetricTensors` and `TauCeti.antisymmetricTensors`). That is not
a matter of taste: Haar averaging counts the invariants of a *continuous* representation, so the
carrier has to be a topological vector space, and the tensor square of a complex inner product
space is one, whereas `Sym[ℂ]^2 V` and `⋀[ℂ]^2 V` — a quotient and a subobject of a
`PiTensorProduct` — carry no topology. In characteristic zero the eigenspaces are the symmetric and
exterior squares, so nothing is lost.

With the squares realized that way the proof is short. The tensor square of `π` is
`TauCeti.ContRepresentation.tprod π π`, the flip commutes with it, so each eigenspace is a
subrepresentation, and their characters differ by `χ_π(g²)`: this is
`ContRepresentation.character_symmetricSquare_sub_character_exteriorSquare`, whose linear-algebra
content is that composing `f ⊗ f` with the flip has trace `tr (f ∘ f)`. Integrating that pointwise
identity and reading each character integral as a dimension of invariants
(`ContRepresentation.integral_character_eq_finrank_invariants`) is the theorem.

Neither the two squares nor their character identity needs any of the analysis, so neither is built
here: the squares are defined and shown continuous, and their characters are compared, for a
continuous representation of a monoid on an inner product space over `RCLike 𝕜` in
`TauCeti/RepresentationTheory/Continuous/Square/Basic.lean` and
`TauCeti/RepresentationTheory/Continuous/Square/Character.lean`. Only the indicator statements
below ask for a compact group and `𝕜 = ℂ`.

## Main statements

* `ContRepresentation.frobeniusSchurIndicator_eq_sub_finrank_invariants`: **the Frobenius-Schur
  indicator is the signed count of invariant tensors**,
  `ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.
* `ContRepresentation.frobeniusSchurIndicator_eq_intCast`: it is therefore an integer, the first
  half of the reality trichotomy.

## Implementation notes

The carrier of `TauCeti.ContRepresentation.character` is pinned by name at every use below, as
`character (𝕜 := ℂ) (V := symmetricTensors ℂ V) ...`. It has to be: the carrier is an implicit
argument that the elaborator would have to read off the coercion `⇑(symmetricSquare π)`, and a
submodule of `V ⊗[ℂ] V` receives its topology both as a subtype and through the norm its
`NormedAddCommGroup` instance carries, so that unification stalls between the two instance paths.
Pinning the carrier costs a few characters and makes every statement below elaborate on the first
try.

## References

This is the reading of `ν₂(π)` as a difference of invariant counts that Layer 6b of the
compact-groups roadmap asks for — the section "Layer 6b: the Frobenius-Schur reality trichotomy for
compact groups" of its
[`Suggested.lean`](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/Suggested.lean),
which pins `frobeniusSchurIndicator` (already built, in
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/Basic.lean`) and the trichotomy targets on top
of it — and that `TauCeti/RepresentationTheory/Compact/Invariants.lean` was built to supply; the
trichotomy `ν₂ ∈ {1, 0, -1}` is the next step and is not proved here. The mathematical development
follows Daniel Bump, *Lie Groups*, second edition, Chapter 2, and T. Bröcker and T. tom Dieck,
*Representations of Compact Lie Groups*, Springer GTM 98 (1985), Chapter II.
-/

public section

open MeasureTheory

open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

section CompactGroup

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (π : ContRepresentation ℂ G V) (hπ : Continuous π)

include hπ

/-- **The Frobenius-Schur indicator is the signed count of invariant tensors**,
`ν₂(π) = dim (Sym²V)ᴳ - dim (Λ²V)ᴳ`.

Integrate `ContRepresentation.character_symmetricSquare_sub_character_exteriorSquare` and read
each of the two character integrals as the dimension of the invariants of its representation
(`ContRepresentation.integral_character_eq_finrank_invariants`). This is the compact-group form of
the finite-group `TauCeti.Representation.frobeniusSchurIndicator_eq_sub_finrank_invariants`, with
the Haar integral in place of the average over the group. -/
theorem frobeniusSchurIndicator_eq_sub_finrank_invariants :
    frobeniusSchurIndicator π hπ
      = (Module.finrank ℂ (symmetricSquare π).invariants : ℂ)
        - (Module.finrank ℂ (exteriorSquare π).invariants : ℂ) := by
  have hs := integral_character_eq_finrank_invariants (𝕜 := ℂ) (V := symmetricTensors ℂ V)
    (symmetricSquare π) (continuous_symmetricSquare π hπ)
  have ha := integral_character_eq_finrank_invariants (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
    (exteriorSquare π) (continuous_exteriorSquare π hπ)
  have hIs : Integrable (fun g : G ↦ character (𝕜 := ℂ) (V := symmetricTensors ℂ V)
      (symmetricSquare π) (continuous_symmetricSquare π hπ) g) (haarProb G) := by
    exact integrable_continuousMap G (character (𝕜 := ℂ) (V := symmetricTensors ℂ V)
      (symmetricSquare π) (continuous_symmetricSquare π hπ))
  have hIa : Integrable (fun g : G ↦ character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
      (exteriorSquare π) (continuous_exteriorSquare π hπ) g) (haarProb G) := by
    exact integrable_continuousMap G (character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V)
      (exteriorSquare π) (continuous_exteriorSquare π hπ))
  calc frobeniusSchurIndicator π hπ
      = ∫ g, (character (𝕜 := ℂ) (V := symmetricTensors ℂ V) (symmetricSquare π)
            (continuous_symmetricSquare π hπ) g
          - character (𝕜 := ℂ) (V := antisymmetricTensors ℂ V) (exteriorSquare π)
            (continuous_exteriorSquare π hπ) g) ∂(haarProb G) := by
        rw [frobeniusSchurIndicator_def]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g ↦
          (character_symmetricSquare_sub_character_exteriorSquare π hπ g).symm)
    _ = (Module.finrank ℂ (symmetricSquare π).invariants : ℂ)
          - (Module.finrank ℂ (exteriorSquare π).invariants : ℂ) := by
        rw [integral_sub hIs hIa, hs, ha]

/-- **The Frobenius-Schur indicator of a compact group is an integer**, being the difference of two
dimensions. This is the first half of the reality trichotomy `ν₂ ∈ {1, 0, -1}`, and the
compact-group form of the finite-group
`TauCeti.Representation.frobeniusSchurIndicator_eq_intCast`; that the integer is one of `1`, `0`,
`-1` for an irreducible needs Schur's lemma and is not proved here. -/
theorem frobeniusSchurIndicator_eq_intCast :
    frobeniusSchurIndicator π hπ
      = ((Module.finrank ℂ (symmetricSquare π).invariants
          - Module.finrank ℂ (exteriorSquare π).invariants : ℤ) : ℂ) := by
  rw [frobeniusSchurIndicator_eq_sub_finrank_invariants π hπ]
  push_cast
  ring

end CompactGroup

end ContRepresentation
