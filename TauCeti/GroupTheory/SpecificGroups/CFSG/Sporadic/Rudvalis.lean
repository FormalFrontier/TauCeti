/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Rudvalis group

This file carries the `Ru` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records Leonard Soicher's `tcenum` presentation of
the Rudvalis group as a `TauCeti.GroupPresentation`, together with its exact source, generator
convention, transcription notes, expected counts, and decidable checks on the transcription.

The complete presentation is

```text
⟨u, v, t | v², t², u⁴, (uv)⁷, (u²v)³, [t,vuv], [t,u⁻¹vu],
           (ut)¹⁰, (uvut)¹³,
           (u[t,u⁻¹][u⁻²tu²,[u⁻¹,t]])³,
           (u(uv)⁻¹t(uv)(tu²)⁴(uv)⁻¹tuv)²,
           (uvtv[(uv)⁻¹tuv,u]²)² ⟩,
```

where `[r,s] = r⁻¹s⁻¹rs`. Bradley, Curtis, and Malik deduce an ordinary presentation
from their symmetric construction of `Ru`; Soicher's `tcenum` artifact supplies the exact list
above and cites that paper as its reference.

The `tcenum` format has five sections. Its first two sections list all generators `uvt` and mark
only `u` as not known to be an involution, which contributes the implicit relators `v²` and `t²`.
The third section lists generators of the subgroup used for coset enumeration and contributes no
relator. The fourth section is empty, so it contributes no Coxeter relations. The ten words in the
fifth section are the remaining relators. The source's parser expands a commutator as
`r⁻¹s⁻¹rs`, so source commutators are represented using `Relator.comm (.inv r) (.inv s)`.
The proved `TauCeti.Relator.toWord_toFreeGroup` theorem is the audit boundary between these
structured expressions and the signed words used by `PresentedGroup`.

The source artifact also gives subgroup generators for enumeration over `²F₄(2)`. They are not
part of the abstract presentation and are therefore recorded in the metadata but not inserted as
relations. An independent line-by-line read-through against the pinned source file and its pinned
`tcfrontend.c` parser found an exact match after the parser's documented involution normalization.
The parser's alphabet is `1 = u`, `2 = v = v⁻¹`, `3 = t = t⁻¹`, and `4 = u⁻¹`; after putting its
implicit `v²` and `t²` relations first, its ten explicit outputs are the signed words in
`TauCeti.Sporadic.ruPresentation_relatorLetters`. This closes the source-to-Lean read-through for
the row. The separate `FiniteSimpleGroups` cross-check does not apply because that development does
not cover `Ru`. This file asserts no order, finiteness, simplicity, or identification result.

## The letter counts

Further decidable checks accompany the count check on the transcribed data. The lengths of the
compiled relator words, one at a time and in aggregate, record the transcription as written, so a
dropped or duplicated letter shows up at the relator that carries it. Exactly one of those words is
not reduced: in the twelfth relator, the tenth source word `(uvtv[(uv)⁻¹tuv,u]²)²`, each of the two
halves puts the `v` ending its prefix `uvtv` against the `v⁻¹` that opens `[(uv)⁻¹tuv,u]`, and those
two cancelling pairs are the four letters by which the compiled count `290` exceeds the reduced
count `286`. Free reduction leaves every relator cyclically reduced, which is what makes the reduced
figure the one comparable with a published presentation length, since such a length is measured
after free and cyclic reduction.

No length is recorded to compare it with: none of the five `tcenum` sections described above carries
a letter count, and Bray's presentation page for `Ru`, which in any case describes a different
two-generator presentation, prints `Length ??`. The figures below therefore state the transcribed
data for a reviewer to compare with the source, rather than checking it against a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.ruPresentation`: Soicher's finite presentation of the Rudvalis group `Ru`.
* `TauCeti.Sporadic.ruPresentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.ruPresentation_relatorLetters`: the twelve compiled words checked against the
  pinned parser output in the independent source-to-Lean read-through.
* `TauCeti.Sporadic.ruPresentation_map_length_relators` and
  `TauCeti.Sporadic.ruPresentation_totalLength`: the letter counts of the compiled words.
* `TauCeti.Sporadic.ruPresentation_map_length_reduce_relators` and
  `TauCeti.Sporadic.ruPresentation_reducedTotalLength`: the same counts after free reduction.
* `TauCeti.Sporadic.isCyclicallyReduced_reduce_of_mem_ruPresentation_relators`: the reduced words
  are cyclically reduced.

## References

* J. D. Bradley, R. T. Curtis, and M. Aslam Malik, *Symmetric generation of the Rudvalis group*,
  Journal of the London Mathematical Society **82** (2010), 643--662,
  <https://doi.org/10.1112/jlms/jdq039>.
* L. H. Soicher, `tcenum`, presentation file `presentations/Ru`, commit
  `fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1`,
  <https://github.com/lhsoicher/tcenum/blob/fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1/presentations/Ru>.
* J. N. Bray, presentation page for the Rudvalis group,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Ru.html>, which records `Length ??` and so
  publishes no letter count.
-/

public section

namespace TauCeti.Sporadic

private abbrev u : Relator (Fin 3) := .gen 0

private abbrev v : Relator (Fin 3) := .gen 1

private abbrev t : Relator (Fin 3) := .gen 2

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The source's commutator `[r,s] = r⁻¹s⁻¹rs`, represented in Mathlib's convention. -/
private abbrev sourceComm (r s : Relator (Fin 3)) : Relator (Fin 3) :=
  .comm (.inv r) (.inv s)

/-- The relator `(u[t,u⁻¹][u⁻²tu²,[u⁻¹,t]])³` in the source file. -/
private abbrev eighthWord : Relator (Fin 3) :=
  .pow (u ⬝ sourceComm t (.inv u) ⬝
    sourceComm (.pow (.inv u) 2 ⬝ t ⬝ .pow u 2) (sourceComm (.inv u) t)) 3

/-- The relator `(u(uv)⁻¹t(uv)(tu²)⁴(uv)⁻¹tuv)²` in the source file. -/
private abbrev ninthWord : Relator (Fin 3) :=
  .pow (u ⬝ .inv (u ⬝ v) ⬝ t ⬝ (u ⬝ v) ⬝ .pow (t ⬝ .pow u 2) 4 ⬝
    .inv (u ⬝ v) ⬝ t ⬝ u ⬝ v) 2

/-- The relator `(uvtv[(uv)⁻¹tuv,u]²)²` in the source file. -/
private abbrev tenthWord : Relator (Fin 3) :=
  .pow (u ⬝ v ⬝ t ⬝ v ⬝ .pow (sourceComm (.inv (u ⬝ v) ⬝ t ⬝ u ⬝ v) u) 2) 2

/-- Leonard Soicher's `tcenum` finite presentation of the Rudvalis sporadic group `Ru` on
generators `u`, `v`, and `t`.

Bradley, Curtis, and Malik prove the underlying presentation; the pinned `tcenum` artifact gives
the exact machine-readable relator list. No structural property of the presented group is asserted
here: this definition records only the cited generators and relators. -/
def ruPresentation : GroupPresentation where
  generatorNames := ["u", "v", "t"]
  source := "J. D. Bradley, R. T. Curtis, and M. Aslam Malik, Symmetric generation of the \
    Rudvalis group, J. London Math. Soc. 82 (2010), 643-662; L. H. Soicher, tcenum"
  sourceLocator := "doi:10.1112/jlms/jdq039; tcenum presentation file presentations/Ru at commit \
    fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1, https://github.com/lhsoicher/tcenum/blob/\
    fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1/presentations/Ru"
  generatorConvention := "Generators have source order u,v,t, so indices 0, 1, and 2 have those \
    names. The tcenum involution-default section lists only u, so v and t are involutions. \
    Products are read left to right, a postfix minus denotes inversion, natural numbers denote \
    powers, and [r,s] denotes r^-1*s^-1*r*s."
  transcriptionNotes := "Prepend the implicit relators v^2 and t^2 to the ten words in the \
    source's fifth section. The third-section words t, u, and ((uvu)^-1*t*u*v*u*v*t*v*\
    [t,u]^2*v*t*v)^2 only generate the subgroup used for enumeration over twisted F4(2), so they \
    are metadata rather than relations. The fourth section is empty and hence supplies no \
    Coxeter relations. An independent line-by-line read-through against the pinned source and its \
    tcfrontend.c parser found exact equality after its documented involution normalization: in \
    the parser output alphabet 1 is u, 2 is both v and v^-1, 3 is both t and t^-1, and 4 is u^-1. \
    FiniteSimpleGroups does not cover Ru, so its separate permutation-group cross-check does not \
    apply."
  expectedGeneratorCount := 3
  expectedRelatorCount := 12
  transcribed :=
    [ .pow v 2,
      .pow t 2,
      .pow u 4,
      .pow (u ⬝ v) 7,
      .pow (.pow u 2 ⬝ v) 3,
      sourceComm t (v ⬝ u ⬝ v),
      sourceComm t (.inv u ⬝ v ⬝ u),
      .pow (u ⬝ t) 10,
      .pow (u ⬝ v ⬝ u ⬝ t) 13,
      eighthWord,
      ninthWord,
      tenthWord ]

/-- The generator names recorded for `Ru`. -/
@[simp]
theorem ruPresentation_generatorNames : ruPresentation.generatorNames = ["u", "v", "t"] := by
  simp [ruPresentation]

/-- The sources recorded for the `Ru` presentation. -/
theorem ruPresentation_source :
    ruPresentation.source = "J. D. Bradley, R. T. Curtis, and M. Aslam Malik, Symmetric \
      generation of the Rudvalis group, J. London Math. Soc. 82 (2010), 643-662; L. H. \
      Soicher, tcenum" := by
  simp [ruPresentation]

/-- The exact paper and pinned machine-readable artifact locating the `Ru` presentation. -/
theorem ruPresentation_sourceLocator :
    ruPresentation.sourceLocator = "doi:10.1112/jlms/jdq039; tcenum presentation file \
      presentations/Ru at commit fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1, \
      https://github.com/lhsoicher/tcenum/blob/\
      fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1/presentations/Ru" := by
  simp [ruPresentation]

/-- The generator order and word syntax used by the `Ru` presentation artifact. -/
theorem ruPresentation_generatorConvention :
    ruPresentation.generatorConvention = "Generators have source order u,v,t, so indices 0, 1, \
      and 2 have those names. The tcenum involution-default section lists only u, so v and t are \
      involutions. Products are read left to right, a postfix minus denotes inversion, natural \
      numbers denote powers, and [r,s] denotes r^-1*s^-1*r*s." := by
  simp [ruPresentation]

/-- The conversion of the five `tcenum` sections into the twelve abstract relators. -/
theorem ruPresentation_transcriptionNotes :
    ruPresentation.transcriptionNotes = "Prepend the implicit relators v^2 and t^2 to the ten \
      words in the source's fifth section. The third-section words t, u, and \
      ((uvu)^-1*t*u*v*u*v*t*v*[t,u]^2*v*t*v)^2 only generate the subgroup used for enumeration \
      over twisted F4(2), so they are metadata rather than relations. The fourth section is empty \
      and hence supplies no Coxeter relations. An independent line-by-line read-through against \
      the pinned source and its tcfrontend.c parser found exact equality after its documented \
      involution normalization: in the parser output alphabet 1 is u, 2 is both v and v^-1, 3 is \
      both t and t^-1, and 4 is u^-1. FiniteSimpleGroups does not cover Ru, so its separate \
      permutation-group cross-check does not apply." := by
  simp [ruPresentation]

/-- The generator count recorded in the `Ru` presentation artifact. -/
@[simp]
theorem ruPresentation_expectedGeneratorCount : ruPresentation.expectedGeneratorCount = 3 := by
  simp [ruPresentation]

/-- The relator count obtained from two implicit involution relations and ten explicit words. -/
@[simp]
theorem ruPresentation_expectedRelatorCount : ruPresentation.expectedRelatorCount = 12 := by
  simp [ruPresentation]

/-- The twelve relator expressions transcribed for `Ru`, with the generator indices written out.

The row's body is sealed, so this equation characterizes the presentation for downstream audits.
Indices `0`, `1`, and `2` denote `u`, `v`, and `t`; the first two entries are the implicit
involution relations and the remaining ten are the words in the source's fifth section. -/
theorem ruPresentation_transcribed :
    ruPresentation.transcribed =
      [ .pow (.gen ⟨1, by decide⟩) 2,
        .pow (.gen ⟨2, by decide⟩) 2,
        .pow (.gen ⟨0, by decide⟩) 4,
        .pow (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) 7,
        .pow (.pow (.gen ⟨0, by decide⟩) 2 ⬝ .gen ⟨1, by decide⟩) 3,
        .comm (.inv (.gen ⟨2, by decide⟩))
          (.inv (.gen ⟨1, by decide⟩ ⬝ .gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩)),
        .comm (.inv (.gen ⟨2, by decide⟩))
          (.inv (.inv (.gen ⟨0, by decide⟩) ⬝ .gen ⟨1, by decide⟩ ⬝
            .gen ⟨0, by decide⟩)),
        .pow (.gen ⟨0, by decide⟩ ⬝ .gen ⟨2, by decide⟩) 10,
        .pow (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩ ⬝
          .gen ⟨0, by decide⟩ ⬝ .gen ⟨2, by decide⟩) 13,
        .pow
          (.gen ⟨0, by decide⟩ ⬝
            .comm (.inv (.gen ⟨2, by decide⟩)) (.inv (.inv (.gen ⟨0, by decide⟩))) ⬝
            .comm
              (.inv (.pow (.inv (.gen ⟨0, by decide⟩)) 2 ⬝
                .gen ⟨2, by decide⟩ ⬝ .pow (.gen ⟨0, by decide⟩) 2))
              (.inv (.comm (.inv (.inv (.gen ⟨0, by decide⟩)))
                (.inv (.gen ⟨2, by decide⟩))))) 3,
        .pow
          (.gen ⟨0, by decide⟩ ⬝
            .inv (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) ⬝
            .gen ⟨2, by decide⟩ ⬝
            (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) ⬝
            .pow (.gen ⟨2, by decide⟩ ⬝ .pow (.gen ⟨0, by decide⟩) 2) 4 ⬝
            .inv (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) ⬝
            .gen ⟨2, by decide⟩ ⬝ .gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) 2,
        .pow
          (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩ ⬝
            .gen ⟨2, by decide⟩ ⬝ .gen ⟨1, by decide⟩ ⬝
            .pow
              (.comm
                (.inv (.inv (.gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩) ⬝
                  .gen ⟨2, by decide⟩ ⬝ .gen ⟨0, by decide⟩ ⬝ .gen ⟨1, by decide⟩))
                (.inv (.gen ⟨0, by decide⟩))) 2) 2 ] := by
  simp [ruPresentation, eighthWord, ninthWord, tenthWord, sourceComm]

/-- The generator and relator counts recorded for `Ru` agree with the transcribed data. -/
theorem ruPresentation_matchesMetadata : ruPresentation.matchesMetadata := by
  decide

/-! ### The letter counts of the compiled words -/

/-- The twelve compiled relator words for `Ru`, spelled out in the order recorded by the Lean row.
A letter `(i, true)` is generator `i` and `(i, false)` is its inverse, so indices `0`, `1`, and `2`
are `u`, `v`, and `t`.

This is the independent source-to-Lean read-through artifact. Running the pinned source's
`tcfrontend.c` on `presentations/Ru` emits the final ten words below with `1 = u`,
`2 = v = v⁻¹`, `3 = t = t⁻¹`, and `4 = u⁻¹`; its involution table supplies the leading `v²` and
`t²` words. The lists below preserve the formal inverse signs that the parser deliberately
collapses for `v` and `t`; applying that documented normalization reproduces its output exactly. -/
theorem ruPresentation_relatorLetters :
    ruPresentation.relatorLetters =
      [[(1, true), (1, true)],
        [(2, true), (2, true)],
        [(0, true), (0, true), (0, true), (0, true)],
        [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true),
          (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
        [(0, true), (0, true), (1, true), (0, true), (0, true), (1, true), (0, true),
          (0, true), (1, true)],
        [(2, false), (1, false), (0, false), (1, false), (2, true), (1, true), (0, true),
          (1, true)],
        [(2, false), (0, false), (1, false), (0, true), (2, true), (0, false), (1, true),
          (0, true)],
        [(0, true), (2, true), (0, true), (2, true), (0, true), (2, true), (0, true),
          (2, true), (0, true), (2, true), (0, true), (2, true), (0, true), (2, true),
          (0, true), (2, true), (0, true), (2, true), (0, true), (2, true)],
        [(0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true),
          (2, true), (0, true), (1, true), (0, true), (2, true), (0, true), (1, true),
          (0, true), (2, true), (0, true), (1, true), (0, true), (2, true), (0, true),
          (1, true), (0, true), (2, true), (0, true), (1, true), (0, true), (2, true),
          (0, true), (1, true), (0, true), (2, true), (0, true), (1, true), (0, true),
          (2, true), (0, true), (1, true), (0, true), (2, true), (0, true), (1, true),
          (0, true), (2, true), (0, true), (1, true), (0, true), (2, true), (0, true),
          (1, true), (0, true), (2, true)],
        [(0, true), (2, false), (0, true), (2, true), (0, false), (0, false), (0, false),
          (2, false), (0, true), (0, true), (2, false), (0, true), (2, true), (0, false),
          (0, false), (0, false), (2, true), (0, true), (0, true), (0, true), (2, false),
          (0, false), (2, true), (0, true), (2, false), (0, true), (2, true), (0, false),
          (0, false), (0, false), (2, false), (0, true), (0, true), (2, false), (0, true),
          (2, true), (0, false), (0, false), (0, false), (2, true), (0, true), (0, true),
          (0, true), (2, false), (0, false), (2, true), (0, true), (2, false), (0, true),
          (2, true), (0, false), (0, false), (0, false), (2, false), (0, true), (0, true),
          (2, false), (0, true), (2, true), (0, false), (0, false), (0, false), (2, true),
          (0, true), (0, true), (0, true), (2, false), (0, false), (2, true)],
        [(0, true), (1, false), (0, false), (2, true), (0, true), (1, true), (2, true),
          (0, true), (0, true), (2, true), (0, true), (0, true), (2, true), (0, true),
          (0, true), (2, true), (0, true), (0, true), (1, false), (0, false), (2, true),
          (0, true), (1, true), (0, true), (1, false), (0, false), (2, true), (0, true),
          (1, true), (2, true), (0, true), (0, true), (2, true), (0, true), (0, true),
          (2, true), (0, true), (0, true), (2, true), (0, true), (0, true), (1, false),
          (0, false), (2, true), (0, true), (1, true)],
        [(0, true), (1, true), (2, true), (1, true), (1, false), (0, false), (2, false),
          (0, true), (1, true), (0, false), (1, false), (0, false), (2, true), (0, true),
          (1, true), (0, true), (1, false), (0, false), (2, false), (0, true), (1, true),
          (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true),
          (0, true), (1, true), (2, true), (1, true), (1, false), (0, false), (2, false),
          (0, true), (1, true), (0, false), (1, false), (0, false), (2, true), (0, true),
          (1, true), (0, true), (1, false), (0, false), (2, false), (0, true), (1, true),
          (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true)]] := by
  simp only [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    ruPresentation_transcribed, List.map_cons, List.map_nil, Relator.toWord_gen,
    Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_comm,
    FreeGroup.invRev]
  decide

/-- The lengths of the twelve compiled relator words for `Ru`, in the source's order.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.ruPresentation_totalLength`. -/
theorem ruPresentation_map_length_relators :
    ruPresentation.relators.map List.length = [2, 2, 4, 14, 9, 8, 8, 20, 52, 69, 46, 56] := by
  rw [← GroupPresentation.map_length_relatorLetters, ruPresentation_relatorLetters]
  decide

/-- The compiled relator words for `Ru` have `290` letters in total. The twelfth of them is not
reduced, so `TauCeti.Sporadic.ruPresentation_reducedTotalLength` and not this figure is the one to
compare with a published presentation length. -/
theorem ruPresentation_totalLength : ruPresentation.totalLength = 290 := by
  rw [GroupPresentation.totalLength_def, ruPresentation_map_length_relators]
  decide

/-- The lengths of the twelve compiled relator words for `Ru` after free reduction. Only the
twelfth entry differs from `TauCeti.Sporadic.ruPresentation_map_length_relators`, by the two
cancelling pairs its two halves each contribute. -/
theorem ruPresentation_map_length_reduce_relators :
    (ruPresentation.relators.map fun w => (FreeGroup.reduce w).length) =
      [2, 2, 4, 14, 9, 8, 8, 20, 52, 69, 46, 52] := by
  simp only [GroupPresentation.relators_def, ruPresentation_transcribed, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

/-- The freely reduced relator words for `Ru` have `286` letters in total. No length is recorded for
this presentation to compare it with, so this figure states the transcribed data for a reviewer to
check against the source rather than against a published number. -/
theorem ruPresentation_reducedTotalLength :
    (ruPresentation.relators.map fun w => (FreeGroup.reduce w).length).sum = 286 := by
  rw [ruPresentation_map_length_reduce_relators]
  decide

/-- Free reduction makes every compiled relator word for `Ru` cyclically reduced.

This is what makes the letter count of `TauCeti.Sporadic.ruPresentation_reducedTotalLength`
comparable with a published presentation length, which is measured after free and cyclic reduction
of each relator. -/
theorem isCyclicallyReduced_reduce_of_mem_ruPresentation_relators :
    ∀ w ∈ ruPresentation.relators, FreeGroup.IsCyclicallyReduced (FreeGroup.reduce w) := by
  simp only [GroupPresentation.relators_def, ruPresentation_transcribed, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

end TauCeti.Sporadic
