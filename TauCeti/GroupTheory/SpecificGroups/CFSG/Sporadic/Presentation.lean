/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
# Presentations of the sporadic groups

This file assembles the twenty-six independently transcribed sporadic-group presentations into the
total function `TauCeti.SporadicName.presentation`. Each branch is the explicit, cited
`TauCeti.GroupPresentation` defined in its group-specific module. The theorem
`TauCeti.presentation_matchesMetadata` combines the individual generator- and
relator-count checks, while `TauCeti.SporadicName.Group` is the concrete group defined by the
selected presentation.

This is milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md`. The dispatcher and its interface
follow the target signatures in the human-authored roadmap's `CFSGStatement/Suggested.lean`; the
mathematical and bibliographic sources for each presentation are recorded in the corresponding
imported module.

## Main definitions

* `TauCeti.SporadicName.presentation`: the complete presentation attached to a sporadic name.
* `TauCeti.SporadicName.Group`: the group defined by that presentation.

## Main results

* `TauCeti.presentation_matchesMetadata`: every selected presentation has the stated
  number of generators and relators.
-/

public section

namespace TauCeti

/-- The explicit, cited finite presentation attached to each sporadic-group name. -/
@[simp]
def SporadicName.presentation : SporadicName → GroupPresentation
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

/-- Every sporadic presentation has the generator and relator counts stated in its metadata.

This is deliberately not `@[simp]`: `GroupPresentation.matchesMetadata_iff` is itself a `simp`
lemma, so the left-hand side `s.presentation.matchesMetadata` simplifies to the pair of count
equations and is not in simp normal form, which the `simpNF` linter rejects. Apply the theorem
directly, or pass it to `simp` as an argument. -/
theorem presentation_matchesMetadata (s : SporadicName) :
    s.presentation.matchesMetadata := by
  cases s with
  | M11 => exact Sporadic.m11Presentation_matchesMetadata
  | M12 => exact Sporadic.m12Presentation_matchesMetadata
  | M22 => exact Sporadic.m22Presentation_matchesMetadata
  | M23 => exact Sporadic.matchesMetadata_m23Presentation
  | M24 => exact Sporadic.matchesMetadata_m24Presentation
  | J1 => exact Sporadic.j1Presentation_matchesMetadata
  | J2 => exact Sporadic.j2Presentation_matchesMetadata
  | J3 => exact Sporadic.j3Presentation_matchesMetadata
  | J4 => exact Sporadic.matchesMetadata_j4Presentation
  | HS => exact Sporadic.matchesMetadata_hsPresentation
  | McL => exact Sporadic.matchesMetadata_mclPresentation
  | He => exact Sporadic.hePresentation_matchesMetadata
  | Ru => exact Sporadic.ruPresentation_matchesMetadata
  | Suz => exact Sporadic.suzPresentation_matchesMetadata
  | ONan => exact Sporadic.onanPresentation_matchesMetadata
  | Co1 => exact Sporadic.co1Presentation_matchesMetadata
  | Co2 => exact Sporadic.matchesMetadata_co2Presentation
  | Co3 => exact Sporadic.matchesMetadata_co3Presentation
  | Fi22 => exact Sporadic.matchesMetadata_fi22Presentation
  | Fi23 => exact Sporadic.fi23Presentation_matchesMetadata
  | Fi24Prime => exact Sporadic.fi24PrimePresentation_matchesMetadata
  | HN => exact Sporadic.matchesMetadata_hnPresentation
  | Ly => exact Sporadic.matchesMetadata_lyPresentation
  | Th => exact Sporadic.Thompson.matchesMetadata_presentation
  | B => exact Sporadic.BabyMonster.matchesMetadata_presentation
  | M => exact Sporadic.Monster.presentation_matchesMetadata

/-- The sporadic group concretely defined by its selected finite presentation. -/
abbrev SporadicName.Group (s : SporadicName) : Type := s.presentation.Group

end TauCeti
