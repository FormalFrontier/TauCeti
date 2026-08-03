/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Group.Conjugation
public import TauCeti.RepresentationTheory.Compact.Character

/-!
# Characters are class functions in `L²(G)`

The character of a finite-dimensional continuous representation of a compact group is a class
function: it is constant on conjugacy classes.  Passing to `L²(G)` this becomes a statement about
an almost-everywhere equivalence class, and the correct home for it is the closed subspace
`TauCeti.centralLp` of classes fixed by every conjugation.

This file proves that a continuous class function lands in that subspace, and specializes to
characters.  Together with the orthogonality relations of
`TauCeti/RepresentationTheory/Compact/Character.lean` this says the irreducible characters form an
orthonormal system *inside* `centralLp`; that they are a Hilbert basis of it -- the compact-group
form of "the irreducible characters are a basis of the class functions" -- needs the Peter-Weyl
theorem and is not proved here.

## Main statements

* `TauCeti.toLp_mem_centralLp`: a continuous class function on a compact group defines an element
  of `centralLp`.
* `TauCeti.ContRepresentation.characterLp_mem_centralLp`: the character of a finite-dimensional
  continuous representation is a class function in `L²(G)`.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 6, "Characters span the class functions", whose first half -- the closed subspace
  `centralLp` and the membership `characterLp_mem_centralLp` -- is what this file supplies.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

section ClassFunction

variable {𝕜 G E : Type*} [NormedRing 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SecondCountableTopologyEither G E]

/-- **A continuous class function is a class function in `Lp`.**  A continuous function on a
compact group is its own representative, so this is
`TauCeti.mem_centralLp_of_ae_eq_of_conj_invariant` applied to `ContinuousMap.coeFn_toLp`. -/
theorem toLp_mem_centralLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : C(G, E))
    (hF : ∀ g h : G, F (h * g * h⁻¹) = F g) :
    ContinuousMap.toLp p (haarProb G) 𝕜 F ∈ centralLp 𝕜 E p (haarProb G) :=
  mem_centralLp_of_ae_eq_of_conj_invariant 𝕜
    (ContinuousMap.coeFn_toLp (E := E) (𝕜 := 𝕜) (p := p) (haarProb G) F) hF

end ClassFunction

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **A character is a class function in `L²(G)`.**  This is
`TauCeti.ContRepresentation.character_conj` promoted from a pointwise identity to a statement about
the almost-everywhere class of the character. -/
theorem characterLp_mem_centralLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    characterLp π hπ ∈ centralLp 𝕜 𝕜 2 (haarProb G) := by
  rw [characterLp_def]
  exact toLp_mem_centralLp (𝕜 := 𝕜) 2 (character π hπ) fun g h ↦ character_conj π hπ g h

end ContRepresentation

end TauCeti
