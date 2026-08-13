/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.BabyMonster
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.One
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Three
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Conway.Two
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyFour
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyThree
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyTwo
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HaradaNorton
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.HigmanSims
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Four
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.One
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Three
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Two
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Lyons
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.McLaughlin
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Monster
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Thompson

/-!
# The sporadic groups of the classification list

Each of the twenty-six sporadic names carries a transcribed finite presentation, one per file under
`TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/`. This file assembles those rows into the single
dispatch `TauCeti.SporadicName.presentation` and defines the carrier
`TauCeti.SporadicName.Group` that the classification statement will use on its sporadic branch.

The dispatch is the interface between the transcription lane and the assembly of the classification
list. A consumer names a sporadic group by its `TauCeti.SporadicName` and never mentions an
individual row, while a reviewer auditing a transcription still reads the row's own file, where the
source, generator convention, transcription notes, and relator expressions live. The branch lemmas
below are what connect the two: each is the statement that the dispatch selects the row of the
matching name, which is exactly the assignment a reviewer of this file checks.

Nothing here asserts anything about the presented groups. In particular no branch is claimed to be
finite, simple, nontrivial, or isomorphic to any other construction of the group whose name it
carries; those are downstream developments. Correspondingly, `presentation_matchesMetadata` records
the generator and relator counts stated by each source against the transcribed data, which is a
check on a transcription and not on the group it presents.

## Main definitions

* `TauCeti.SporadicName.presentation`: the cited finite presentation transcribed for each of the
  twenty-six sporadic names.
* `TauCeti.SporadicName.Group`: the group presented by that data, the carrier of the sporadic
  branch of the classification list.

## Main results

* `TauCeti.SporadicName.presentation_matchesMetadata`: every one of the twenty-six rows passes the
  generator and relator count check of its source.

## References

This closes the dispatch of milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md`, whose
milestone A0 consumes `TauCeti.SporadicName.Group` as the sporadic branch of `CFSGIndex.Group`. The
signatures of `presentation`, `presentation_matchesMetadata`, and `Group` follow the human-owned
formal skeleton in `TauCetiRoadmap/CFSGStatement/Suggested.lean`. The presentations themselves are
transcribed in the per-name files imported above, each citing its own source.
-/

public section

namespace TauCeti

namespace SporadicName

/-- The cited finite presentation transcribed for a sporadic group name.

Every branch selects the row transcribed for that name in its own file, so no branch is a
placeholder, a semi-presentation, or a group obtained from an existence theorem. The generator
convention, the source, and the transcription notes of the selected row travel with it, since they
are fields of the returned `TauCeti.GroupPresentation`.

This is exposed because the classification list is assembled by cases on an index, so the
presentation attached to a name has to reduce for the resulting carrier to be recognised as the
presented group of a named row. -/
@[expose] def presentation : SporadicName → GroupPresentation
  | .M11 => Sporadic.m11Presentation
  | .M12 => Sporadic.m12Presentation
  | .M22 => Sporadic.m22Presentation
  | .M23 => Sporadic.m23Presentation
  | .M24 => Sporadic.m24Presentation
  | .J1 => Sporadic.j1Presentation
  | .J2 => Sporadic.j2Presentation
  | .J3 => Sporadic.j3Presentation
  | .J4 => Sporadic.j4Presentation
  | .HS => Sporadic.hsPresentation
  | .McL => Sporadic.mclPresentation
  | .He => Sporadic.hePresentation
  | .Ru => Sporadic.ruPresentation
  | .Suz => Sporadic.suzPresentation
  | .ONan => Sporadic.onanPresentation
  | .Co1 => Sporadic.co1Presentation
  | .Co2 => Sporadic.co2Presentation
  | .Co3 => Sporadic.co3Presentation
  | .Fi22 => Sporadic.fi22Presentation
  | .Fi23 => Sporadic.fi23Presentation
  | .Fi24Prime => Sporadic.fi24PrimePresentation
  | .HN => Sporadic.hnPresentation
  | .Ly => Sporadic.lyPresentation
  | .Th => Sporadic.Thompson.presentation
  | .B => Sporadic.BabyMonster.presentation
  | .M => Sporadic.Monster.presentation

/-! ### The twenty-six branches

One lemma per name, recording which transcribed row the dispatch selects. Reading this list against
the constructors of `TauCeti.SporadicName` is the review of the assignment; reading a row against
its published source is the review carried out in that row's own file. -/

@[simp] theorem presentation_M11 : M11.presentation = Sporadic.m11Presentation := by
  simp only [presentation]

@[simp] theorem presentation_M12 : M12.presentation = Sporadic.m12Presentation := by
  simp only [presentation]

@[simp] theorem presentation_M22 : M22.presentation = Sporadic.m22Presentation := by
  simp only [presentation]

@[simp] theorem presentation_M23 : M23.presentation = Sporadic.m23Presentation := by
  simp only [presentation]

@[simp] theorem presentation_M24 : M24.presentation = Sporadic.m24Presentation := by
  simp only [presentation]

@[simp] theorem presentation_J1 : J1.presentation = Sporadic.j1Presentation := by
  simp only [presentation]

@[simp] theorem presentation_J2 : J2.presentation = Sporadic.j2Presentation := by
  simp only [presentation]

@[simp] theorem presentation_J3 : J3.presentation = Sporadic.j3Presentation := by
  simp only [presentation]

@[simp] theorem presentation_J4 : J4.presentation = Sporadic.j4Presentation := by
  simp only [presentation]

@[simp] theorem presentation_HS : HS.presentation = Sporadic.hsPresentation := by
  simp only [presentation]

@[simp] theorem presentation_McL : McL.presentation = Sporadic.mclPresentation := by
  simp only [presentation]

@[simp] theorem presentation_He : He.presentation = Sporadic.hePresentation := by
  simp only [presentation]

@[simp] theorem presentation_Ru : Ru.presentation = Sporadic.ruPresentation := by
  simp only [presentation]

@[simp] theorem presentation_Suz : Suz.presentation = Sporadic.suzPresentation := by
  simp only [presentation]

@[simp] theorem presentation_ONan : ONan.presentation = Sporadic.onanPresentation := by
  simp only [presentation]

@[simp] theorem presentation_Co1 : Co1.presentation = Sporadic.co1Presentation := by
  simp only [presentation]

@[simp] theorem presentation_Co2 : Co2.presentation = Sporadic.co2Presentation := by
  simp only [presentation]

@[simp] theorem presentation_Co3 : Co3.presentation = Sporadic.co3Presentation := by
  simp only [presentation]

@[simp] theorem presentation_Fi22 : Fi22.presentation = Sporadic.fi22Presentation := by
  simp only [presentation]

@[simp] theorem presentation_Fi23 : Fi23.presentation = Sporadic.fi23Presentation := by
  simp only [presentation]

@[simp] theorem presentation_Fi24Prime :
    Fi24Prime.presentation = Sporadic.fi24PrimePresentation := by
  simp only [presentation]

@[simp] theorem presentation_HN : HN.presentation = Sporadic.hnPresentation := by
  simp only [presentation]

@[simp] theorem presentation_Ly : Ly.presentation = Sporadic.lyPresentation := by
  simp only [presentation]

@[simp] theorem presentation_Th : Th.presentation = Sporadic.Thompson.presentation := by
  simp only [presentation]

@[simp] theorem presentation_B : B.presentation = Sporadic.BabyMonster.presentation := by
  simp only [presentation]

@[simp] theorem presentation_M : M.presentation = Sporadic.Monster.presentation := by
  simp only [presentation]

/-! ### The count check and the carrier -/

/-- The generator and relator counts stated by the source of every sporadic row agree with the
transcribed data.

This is transcription metadata for all twenty-six names at once, assembled from the row-by-row
checks. It makes no claim that a source presents the group whose name the row carries, nor that the
transcription agrees with that source: those rest on the source citation and the independent
read-through required of each row. -/
theorem presentation_matchesMetadata (s : SporadicName) : s.presentation.matchesMetadata := by
  cases s <;> simp only [presentation]
  exacts [Sporadic.m11Presentation_matchesMetadata, Sporadic.m12Presentation_matchesMetadata,
    Sporadic.m22Presentation_matchesMetadata, Sporadic.matchesMetadata_m23Presentation,
    Sporadic.matchesMetadata_m24Presentation, Sporadic.j1Presentation_matchesMetadata,
    Sporadic.j2Presentation_matchesMetadata, Sporadic.j3Presentation_matchesMetadata,
    Sporadic.matchesMetadata_j4Presentation, Sporadic.matchesMetadata_hsPresentation,
    Sporadic.matchesMetadata_mclPresentation, Sporadic.hePresentation_matchesMetadata,
    Sporadic.ruPresentation_matchesMetadata, Sporadic.suzPresentation_matchesMetadata,
    Sporadic.onanPresentation_matchesMetadata, Sporadic.co1Presentation_matchesMetadata,
    Sporadic.matchesMetadata_co2Presentation, Sporadic.matchesMetadata_co3Presentation,
    Sporadic.matchesMetadata_fi22Presentation, Sporadic.fi23Presentation_matchesMetadata,
    Sporadic.fi24PrimePresentation_matchesMetadata, Sporadic.matchesMetadata_hnPresentation,
    Sporadic.matchesMetadata_lyPresentation, Sporadic.Thompson.matchesMetadata_presentation,
    Sporadic.BabyMonster.matchesMetadata_presentation,
    Sporadic.Monster.presentation_matchesMetadata]

/-- The sporadic group named by `s`, defined by the generators and compiled relations of its
transcribed presentation.

This is the carrier the classification list uses on its sporadic branch. It is a
`Mathlib.GroupTheory.PresentedGroup`, so its group structure is Mathlib's and no instance is added
here; equally, nothing is asserted about it beyond being that presented group. -/
abbrev Group (s : SporadicName) : Type := s.presentation.Group

/-! The group structure on the carrier is inherited from Mathlib's presented group. -/

example (s : SporadicName) : _root_.Group s.Group := inferInstance

end SporadicName

end TauCeti
