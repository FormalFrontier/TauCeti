/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the first Conway group

This file carries the `Co₁` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records presentation `GPLTable.Co1.1` from Roderik
Lindenbergh's Group Presentations Library as a `TauCeti.GroupPresentation`, together with the exact
source, generator convention, transcription notes, expected counts, and decidable checks on the
transcription.

The presentation uses the Coxeter graph encoded by

```text
b4h3a3b5c3d3f4c3e4a, b4g4f, e6f6h.
```

All eight generators are involutions and every omitted edge has label two. Thus the graph
contributes eight square relations, thirteen labeled-edge relations, and fifteen omitted-edge
relations. The source then appends

```text
a = (cf)²,  e = (bg)²,  b = (ef)³,  d = (bh)²,  d = (eah)³,
(adfh)³,  (baefg)³,  (cef)⁷,  (adefcefgh)³⁹.
```

An equality `x = y` in the source is the relator `x⁻¹y`. The complete presentation therefore has
45 relators, whose compiled words have 611 signed letters. The theorems below check both figures
from the transcribed expressions.

The library identifies this record as a presentation of `Co₁` originating in Praeger--Soicher,
whose construction uses low-rank representations and graphs for sporadic groups. The stored data
is a full presentation of the abstract group, not a semi-presentation for recognizing generators
in an already constructed group. This file asserts no order, finiteness, simplicity, or
identification result. A separate source-to-Lean read-through remains part of the S1 review artifact
required by the roadmap.

## Main definition

* `TauCeti.Sporadic.co1Presentation`: the GPL finite presentation of the first Conway group `Co₁`.

## References

* R. Lindenbergh, *Group Presentations Library*, version 1.0, record `GPLTable.Co1.1`,
  <https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g>.
* C. E. Praeger and L. H. Soicher, *Low Rank Representations and Graphs for Sporadic Groups*,
  Cambridge University Press, 1997, Chapter 4, doi:10.1017/CBO9780511526039.005.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 8) := .gen 0

private abbrev b : Relator (Fin 8) := .gen 1

private abbrev c : Relator (Fin 8) := .gen 2

private abbrev d : Relator (Fin 8) := .gen 3

private abbrev e : Relator (Fin 8) := .gen 4

private abbrev f : Relator (Fin 8) := .gen 5

private abbrev g : Relator (Fin 8) := .gen 6

private abbrev h : Relator (Fin 8) := .gen 7

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The eight involution relations and thirteen labeled-edge relations decoded from the three
Coxeter paths of `GPLTable.Co1.1`. -/
private def co1NodeAndEdgeRelators : List (Relator (Fin 8)) :=
  [ .pow a 2,
    .pow b 2,
    .pow c 2,
    .pow d 2,
    .pow e 2,
    .pow f 2,
    .pow g 2,
    .pow h 2,
    .pow (a ⬝ b) 3,
    .pow (a ⬝ e) 4,
    .pow (a ⬝ h) 3,
    .pow (b ⬝ c) 5,
    .pow (b ⬝ g) 4,
    .pow (b ⬝ h) 4,
    .pow (c ⬝ d) 3,
    .pow (c ⬝ e) 3,
    .pow (c ⬝ f) 4,
    .pow (d ⬝ f) 3,
    .pow (e ⬝ f) 6,
    .pow (f ⬝ g) 4,
    .pow (f ⬝ h) 6 ]

/-- The fifteen omitted-edge relations decoded from the three Coxeter paths of
`GPLTable.Co1.1`. Each omitted edge has label two. -/
private def co1NonedgeRelators : List (Relator (Fin 8)) :=
  [ .pow (a ⬝ c) 2,
    .pow (a ⬝ d) 2,
    .pow (a ⬝ f) 2,
    .pow (a ⬝ g) 2,
    .pow (b ⬝ d) 2,
    .pow (b ⬝ e) 2,
    .pow (b ⬝ f) 2,
    .pow (c ⬝ g) 2,
    .pow (c ⬝ h) 2,
    .pow (d ⬝ e) 2,
    .pow (d ⬝ g) 2,
    .pow (d ⬝ h) 2,
    .pow (e ⬝ g) 2,
    .pow (e ⬝ h) 2,
    .pow (g ⬝ h) 2 ]

/-- The nine words following the Coxeter paths in `GPLTable.Co1.1`. An equality `x = y` is stored
as the relator `x⁻¹y`, following the GPL decoder. -/
private def co1AdditionalRelators : List (Relator (Fin 8)) :=
  [ .inv a ⬝ .pow (c ⬝ f) 2,
    .inv e ⬝ .pow (b ⬝ g) 2,
    .inv b ⬝ .pow (e ⬝ f) 3,
    .inv d ⬝ .pow (b ⬝ h) 2,
    .inv d ⬝ .pow (e ⬝ a ⬝ h) 3,
    .pow (a ⬝ d ⬝ f ⬝ h) 3,
    .pow (b ⬝ a ⬝ e ⬝ f ⬝ g) 3,
    .pow (c ⬝ e ⬝ f) 7,
    .pow (a ⬝ d ⬝ e ⬝ f ⬝ c ⬝ e ⬝ f ⬝ g ⬝ h) 39 ]

/-- The Group Presentations Library finite presentation `GPLTable.Co1.1` of the first Conway
group `Co₁` on generators `a`, `b`, `c`, `d`, `e`, `f`, `g`, and `h`.

The source describes this as a full presentation of the abstract group and identifies its origin
as Praeger--Soicher. No structural property of the presented group is asserted here: this
definition records only the cited generators and relations. -/
def co1Presentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "e", "f", "g", "h"]
  source := "R. Lindenbergh, Group Presentations Library, version 1.0; presentation attributed \
    there to C. E. Praeger and L. H. Soicher, Low Rank Representations and Graphs for Sporadic \
    Groups, Cambridge University Press, 1997"
  sourceLocator := "GPLTable.Co1.1 in \
    https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g; Praeger--Soicher, Chapter 4, \
    doi:10.1017/CBO9780511526039.005"
  generatorConvention := "The source generators are indexed alphabetically in Lean: indices 0 \
    through 7 are a,b,c,d,e,f,g,h. This is a relabeling of the GPL decoder's first-occurrence map \
    b,h,a,c,d,f,e,g and preserves every named relation. A Coxeter path declares each node to be \
    an involution, a labeled edge x-m-y declares (x*y)^m = 1, and an omitted edge declares \
    (x*y)^2 = 1. An equality x = y compiles to x^-1*y, and products are read left to right."
  transcriptionNotes := "Expand the paths b4h3a3b5c3d3f4c3e4a, b4g4f, and e6f6h to eight square \
    relations, thirteen labeled-edge relations, and fifteen omitted-edge relations. Append the \
    nine words in presdef[3], interpreting each equality as left-hand inverse times right-hand \
    side, and reindex the named generators alphabetically. The expected relator count and total \
    length are derived from this exact expansion. A separate source-to-Lean read-through remains \
    an S1 review obligation."
  expectedGeneratorCount := 8
  expectedRelatorCount := 45
  transcribed := co1NodeAndEdgeRelators ++ co1NonedgeRelators ++ co1AdditionalRelators

/-- The generator and relator counts recorded for `Co₁` agree with the transcribed data. -/
theorem co1Presentation_matchesMetadata : co1Presentation.matchesMetadata := by
  decide

/-- The compiled relators of the `Co₁` presentation contain `611` signed letters in total. -/
theorem co1Presentation_totalLength : co1Presentation.totalLength = 611 := by
  rw [GroupPresentation.totalLength_def, GroupPresentation.relators_def]
  simp only [co1Presentation, co1NodeAndEdgeRelators, co1NonedgeRelators, co1AdditionalRelators,
    List.map_append, List.sum_append, Relator.length_toWord, Relator.length_gen, Relator.length_inv,
    Relator.length_mul, Relator.length_pow, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  norm_num

/-- The involution and labeled-edge relators compile to cyclically reduced words. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1NodeAndEdgeRelators :
    ∀ r ∈ co1NodeAndEdgeRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  simp [co1NodeAndEdgeRelators, FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- The omitted-edge relators compile to cyclically reduced words. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1NonedgeRelators :
    ∀ r ∈ co1NonedgeRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  simp [co1NonedgeRelators, FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- The relators taken from `presdef[3]` compile to cyclically reduced words.

The last of them is a thirty-ninth power, whose expansion has three hundred and fifty-one letters;
it is handled by `TauCeti.Relator.isCyclicallyReduced_toWord_pow`, which reduces the check to its
nine-letter base. Expanding it instead exhausts the elaborator. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1AdditionalRelators :
    ∀ r ∈ co1AdditionalRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  intro r hr
  simp only [co1AdditionalRelators, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  on_goal 9 =>
    exact Relator.isCyclicallyReduced_toWord_pow
      (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]) 39
  all_goals simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced, FreeGroup.invRev]

/-- Every transcribed `Co₁` relator expression compiles to a cyclically reduced word. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1Transcribed :
    ∀ r ∈ co1Presentation.transcribed, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · rcases List.mem_append.mp h with h | h
    · exact isCyclicallyReduced_toWord_of_mem_co1NodeAndEdgeRelators r h
    · exact isCyclicallyReduced_toWord_of_mem_co1NonedgeRelators r h
  · exact isCyclicallyReduced_toWord_of_mem_co1AdditionalRelators r h

/-- Every compiled `Co₁` relator is cyclically reduced, so the letter count recorded by
`TauCeti.Sporadic.co1Presentation_totalLength` is comparable with a published presentation length,
which is measured after free and cyclic reduction of each relator. -/
theorem co1Presentation_relatorsCyclicallyReduced :
    co1Presentation.relatorsCyclicallyReduced := by
  rw [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def]
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  exact isCyclicallyReduced_toWord_of_mem_co1Transcribed r hr

end TauCeti.Sporadic
