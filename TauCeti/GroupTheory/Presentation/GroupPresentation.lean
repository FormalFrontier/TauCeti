/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.GroupTheory.Presentation.Relator

/-!
# Auditable finite group presentations

This file packages a finite group presentation together with the metadata needed to audit a
transcription from a published source. Generator names determine the arity of the relators, so a
presentation cannot separately record an incompatible generator count. The expected generator and
relator counts remain as checkable transcription metadata.

The stored relators are human-readable `TauCeti.Relator` expressions. They are compiled to
Mathlib's signed words and then interpreted by `FreeGroup.mk`; the resulting finite relation set
defines `TauCeti.GroupPresentation.Group` using Mathlib's `PresentedGroup`.

## Main definitions

* `TauCeti.GroupPresentation`: cited presentation data and its transcription metadata.
* `TauCeti.GroupPresentation.relators`: the compiled signed words.
* `TauCeti.GroupPresentation.relatorSet`: the relations as free-group elements.
* `TauCeti.GroupPresentation.Group`: the group defined by the presentation.
* `TauCeti.GroupPresentation.matchesMetadata`: the executable generator and relator count check.

## References

This file implements the finite-presentation metadata format in milestone S0 of
`TauCetiRoadmap/CFSGStatement/README.md`. Its record fields and dependent-arity design are adapted
from the target signatures in the human-owned roadmap's `CFSGStatement/Suggested.lean`.
-/

public section

namespace TauCeti

/-- A finite group presentation together with auditable source and transcription metadata.

The source must be a full presentation of the abstract group, not a semi-presentation for
recognizing generators in a group already constructed elsewhere. `generatorNames` alone determines
the relator arity; `expectedGeneratorCount` is retained only as metadata checked by
`matchesMetadata`.

There is deliberately no checksum field: without a pinned normalization and algorithm, a checksum
would not be a reproducible check on the transcribed expressions. -/
structure GroupPresentation where
  /-- Generator names, in the order used by the relator indices. -/
  generatorNames : List String
  /-- Bibliographic citation or database name for the full presentation. -/
  source : String
  /-- Page, theorem number, or stable database identifier locating the presentation. -/
  sourceLocator : String
  /-- The source's generator and commutator conventions. -/
  generatorConvention : String
  /-- Notes explaining any normalization or conversion made during transcription. -/
  transcriptionNotes : String
  /-- The number of generators stated by the source. -/
  expectedGeneratorCount : ℕ
  /-- The number of relators stated by the source. -/
  expectedRelatorCount : ℕ
  /-- Relators transcribed in the generator order recorded by `generatorNames`. -/
  transcribed : List (Relator (Fin generatorNames.length))

namespace GroupPresentation

/-- The number of generators in a presentation, determined by its generator-name list. -/
abbrev generatorCount (P : GroupPresentation) : ℕ := P.generatorNames.length

/-- The relator expressions compiled to left-to-right signed words. -/
def relators (P : GroupPresentation) : List (PresentationWord (Fin P.generatorCount)) :=
  P.transcribed.map Relator.toWord

/-- Compilation preserves the number of relators. -/
@[simp]
theorem length_relators (P : GroupPresentation) : P.relators.length = P.transcribed.length := by
  simp [relators]

/-- The compiled relations, interpreted as elements of the free group. -/
def relatorSet (P : GroupPresentation) : Set (FreeGroup (Fin P.generatorCount)) :=
  {r | r ∈ P.relators.map FreeGroup.mk}

/-- Membership in the relation set is membership in the list of interpreted compiled words. -/
@[simp]
theorem mem_relatorSet_iff (P : GroupPresentation) (r : FreeGroup (Fin P.generatorCount)) :
    r ∈ P.relatorSet ↔ r ∈ P.relators.map FreeGroup.mk :=
  Iff.rfl

/-- The relation set of a `GroupPresentation` is finite. -/
theorem relatorSet_finite (P : GroupPresentation) : P.relatorSet.Finite := by
  simpa only [relatorSet] using (P.relators.map FreeGroup.mk).finite_toSet

/-- The group defined by the generators and compiled relations of a presentation. -/
abbrev Group (P : GroupPresentation) : Type :=
  PresentedGroup P.relatorSet

/-- The recorded generator and relator counts agree with the transcribed data.

This checks transcription metadata only; it makes no claim that the source presents a named group
or that the transcription agrees with the source. -/
def matchesMetadata (P : GroupPresentation) : Prop :=
  P.generatorCount = P.expectedGeneratorCount ∧
    P.transcribed.length = P.expectedRelatorCount

/-- The metadata check is exactly the pair of generator- and relator-count equalities. -/
@[simp]
theorem matchesMetadata_iff (P : GroupPresentation) : P.matchesMetadata ↔
    P.generatorCount = P.expectedGeneratorCount ∧
      P.transcribed.length = P.expectedRelatorCount :=
  Iff.rfl

end GroupPresentation

end TauCeti
