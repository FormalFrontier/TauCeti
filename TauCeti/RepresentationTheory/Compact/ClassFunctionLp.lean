/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.Conjugation
public import TauCeti.RepresentationTheory.Compact.Character.Basic

/-!
# Characters are class functions in `L²(G)`

The character of a finite-dimensional continuous representation of a compact group is a class
function: it is constant on conjugacy classes.  Passing to `L²(G)` this becomes a statement about
an almost-everywhere equivalence class, and the correct home for it is the closed subspace
`TauCeti.classFunctionLp` of classes fixed by every conjugation.

This file proves that a continuous class function lands in that subspace, and specializes to
characters.  Together with the orthogonality relations of
`TauCeti/RepresentationTheory/Compact/Character/Basic.lean` this says the irreducible characters
form an orthonormal system *inside* `classFunctionLp`; that they are a Hilbert basis of it -- the
compact-group form of "the irreducible characters are a basis of the class functions" -- needs the
Peter-Weyl theorem and is proved in
`TauCeti/RepresentationTheory/Compact/Character/Basis.lean`.

## Main statements

* `TauCeti.toLp_mem_classFunctionLp`: a continuous class function on a compact group defines an
  element of `classFunctionLp`.
* `TauCeti.ContRepresentation.characterLp_mem_classFunctionLp`: the character of a
  finite-dimensional continuous representation is a class function in `L²(G)`.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
* [Compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  Layer 6, "Characters span the class functions", whose first half -- the closed subspace
  `classFunctionLp` (the roadmap's `centralLp`) and the membership
  `characterLp_mem_classFunctionLp` -- is what this file supplies.
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
compact group that is constant on conjugacy classes has a class in `Lp` fixed by every
conjugation. -/
theorem toLp_mem_classFunctionLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : C(G, E))
    (hF : ∀ g h : G, F (h * g * h⁻¹) = F g) :
    ContinuousMap.toLp p (haarProb G) 𝕜 F ∈ classFunctionLp 𝕜 E p (haarProb G) :=
  mem_classFunctionLp_of_ae_eq_of_conj_invariant 𝕜
    (ContinuousMap.coeFn_toLp (E := E) (𝕜 := 𝕜) (p := p) (haarProb G) F) hF

end ClassFunction

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **A character is a class function in `L²(G)`.**  The class of the character of a
finite-dimensional continuous representation of a compact group is fixed by every conjugation,
the almost-everywhere form of its pointwise invariance on conjugacy classes. -/
theorem characterLp_mem_classFunctionLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    characterLp π hπ ∈ classFunctionLp 𝕜 𝕜 2 (haarProb G) := by
  rw [characterLp_def]
  exact toLp_mem_classFunctionLp (𝕜 := 𝕜) 2 (character π hπ) fun g h ↦ character_conj π hπ g h

end ContRepresentation

end TauCeti
