/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Harada--Norton group

This file carries the `HN` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the corrected five-generator presentation of
the Harada--Norton group given by Bray and Curtis as a `TauCeti.GroupPresentation`, together with
its source, generator convention, transcription notes, and expected counts.

The nineteen relators are

```text
a⁴, [a²,b], b⁷, (ab²)⁴, a⁻²(abab³)³, ((ab)³ab⁻³)²,
c²a², [a,c], [bab,c], (bab³c)³,
d², (ad)², [b,d], d^(cbcb⁻¹)(cd)³,
t⁵, t^a t², t^c t⁻², [t,b], (dt)³.
```

Here `[r,s] = r⁻¹s⁻¹rs` and `r^s = s⁻¹rs`, following the Magma source. Mathlib's
`commutatorElement` uses the opposite commutator convention, so a source commutator is represented
by `Relator.comm (.inv r) (.inv s)`. Conjugates are expanded directly in the structured
expressions. The proved `TauCeti.Relator.toWord_toFreeGroup` theorem is the audit boundary between
these expressions and the signed words consumed by `PresentedGroup`.

Section 4 of Bray--Curtis constructs `HN` as a quotient of a progenitor by coset enumeration over
the visible subgroup `2·HS:2`. Section 5 derives the five-generator presentation used here. The
authors' corrected Magma file `HNpb.m` gives the same nineteen relators exactly; in particular, it
uses `(ad)²`, correcting the preprint's `[a,d]` at that position. The source describes `c` and `d`
as generators adjoined while successively presenting `U₃(5):2` and `HS:2`, and `t` as the
order-five symmetric generator whose final relations produce `HN`.

The source-to-Lean transcription has been read against both the corrected printed display and the
machine-readable Magma file. An independent read-through remains part of the S1 review artifact.
This file asserts no order, finiteness, simplicity, or identification result.

## The letter counts

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out, and the provenance a manifest row
exists to record. Further decidable checks accompany them. The lengths of the compiled relator
words, one at a time and in aggregate, record the transcription as written, so a dropped or
duplicated letter shows up at the relator that carries it. Exactly one compiled word is not reduced:
the fifth relator `a⁻²(abab³)³` puts the second letter of `a⁻²` against the `a` opening `abab³`, and
that single cancelling pair is the two letters by which the compiled count `153` exceeds the reduced
count `151`. Free reduction leaves every relator cyclically reduced, which is what makes the reduced
figure the one comparable with a published presentation length, since such a length is measured
after free and cyclic reduction.

No such length is published for this presentation: `HNpb.m` is a Magma file of relator words with no
letter count, the paper's known-errors record adds none, and Bray's presentation page for `HN` is
one of the 1997 stubs that print `Length ??`. The figures below therefore state the transcribed
data for a reviewer to compare with the source, rather than checking it against a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.hnPresentation`: the Bray--Curtis finite presentation of `HN`.
* `TauCeti.Sporadic.transcribed_hnPresentation` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.map_length_relators_hnPresentation` and
  `TauCeti.Sporadic.totalLength_hnPresentation`: the letter counts of the compiled words.
* `TauCeti.Sporadic.map_length_reduce_relators_hnPresentation` and
  `TauCeti.Sporadic.reducedTotalLength_hnPresentation`: the same counts after free reduction.
* `TauCeti.Sporadic.isCyclicallyReduced_reduce_mem_hnPresentation_relators`: the reduced words are
  cyclically reduced.

## References

* J. N. Bray and R. T. Curtis, *Monomial modular representations and symmetric generation of the
  Harada--Norton group*, J. Algebra **268** (2003), no. 2, 723--743, Sections 4--5,
  <https://doi.org/10.1016/S0021-8693(03)00298-9>.
* The authors' corrected version and known-errors record,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HN.html>, and the corrected
  machine-readable presentation,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HNpb.m>.
* J. N. Bray, presentation page for the Harada--Norton group,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/HN.html>, which records `Length ??` and so
  publishes no letter count.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 5) := .gen 0

private abbrev b : Relator (Fin 5) := .gen 1

private abbrev c : Relator (Fin 5) := .gen 2

private abbrev d : Relator (Fin 5) := .gen 3

private abbrev t : Relator (Fin 5) := .gen 4

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The word `c b c b⁻¹` conjugating `d` in the fourteenth relator. -/
private abbrev dConjugator : Relator (Fin 5) :=
  c ⬝ b ⬝ c ⬝ .inv b

/-- The corrected Bray--Curtis finite presentation of the Harada--Norton group `HN` on five
generators.

The paper proves that this is a presentation of the abstract group, rather than a
semi-presentation used only to recognize generators inside an existing group. No structural
property of the presented group is asserted here: this definition records only the cited
generators and relators. -/
def hnPresentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "t"]
  source := "J. N. Bray and R. T. Curtis, Monomial modular representations and symmetric \
    generation of the Harada--Norton group, J. Algebra 268 (2003), 723--743"
  sourceLocator := "Sections 4--5, especially p. 735; corrected Magma file HNpb.m at \
    https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HNpb.m"
  generatorConvention := "The generators a, b, c, d and t of Bray--Curtis HNpb.m, in that order, \
    so indices 0 through 4 have those names. Products are read left to right, negative exponents \
    denote inverses, [r,s] denotes r^-1 s^-1 r s, and r^s denotes s^-1 r s."
  transcriptionNotes := "The nineteen words in the first presentation of the corrected HNpb.m \
    file are stored as nineteen relators equal to the identity. They agree in order and spelling \
    with the five-generator presentation displayed in Section 5 of the corrected paper. The \
    corrected source uses (a*d)^2 as its twelfth relator; the authors' known-errors record notes \
    that the preprint's [a,d] at this position was wrong. An independent source-to-Lean \
    read-through remains part of the S1 review artifact."
  expectedGeneratorCount := 5
  expectedRelatorCount := 19
  transcribed :=
    [ .pow a 4,
      Relator.comm (.inv (.pow a 2)) (.inv b),
      .pow b 7,
      .pow (a ⬝ .pow b 2) 4,
      .pow (.inv a) 2 ⬝ .pow (a ⬝ b ⬝ a ⬝ .pow b 3) 3,
      .pow (.pow (a ⬝ b) 3 ⬝ a ⬝ .pow (.inv b) 3) 2,
      .pow c 2 ⬝ .pow a 2,
      Relator.comm (.inv a) (.inv c),
      Relator.comm (.inv (b ⬝ a ⬝ b)) (.inv c),
      .pow (b ⬝ a ⬝ .pow b 3 ⬝ c) 3,
      .pow d 2,
      .pow (a ⬝ d) 2,
      Relator.comm (.inv b) (.inv d),
      .inv dConjugator ⬝ d ⬝ dConjugator ⬝ .pow (c ⬝ d) 3,
      .pow t 5,
      .inv a ⬝ t ⬝ a ⬝ .pow t 2,
      .inv c ⬝ t ⬝ c ⬝ .pow (.inv t) 2,
      Relator.comm (.inv t) (.inv b),
      .pow (d ⬝ t) 3 ]

/-- The generator names recorded for `HN`. The row's body is sealed, so this equation is what shows
a consumer that the transcription is on five generators, and it supplies the index bounds in
`TauCeti.Sporadic.transcribed_hnPresentation`. -/
@[simp]
theorem generatorNames_hnPresentation :
    hnPresentation.generatorNames = ["a", "b", "c", "d", "t"] := by
  simp [hnPresentation]

/-- The source recorded for `HN`. The row's body is sealed, so this equation publishes the citation
itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem source_hnPresentation :
    hnPresentation.source = "J. N. Bray and R. T. Curtis, Monomial modular representations and \
      symmetric generation of the Harada--Norton group, J. Algebra 268 (2003), 723--743" := by
  simp [hnPresentation]

/-- The locator recorded for `HN`, naming both the sections of the paper and the corrected Magma
file that carries the same nineteen relators. -/
@[simp]
theorem sourceLocator_hnPresentation :
    hnPresentation.sourceLocator = "Sections 4--5, especially p. 735; corrected Magma file HNpb.m \
      at https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HNpb.m" := by
  simp [hnPresentation]

/-- The generator convention recorded for `HN`, fixing which generator each relator index names and
which commutator and conjugation conventions the source uses. -/
@[simp]
theorem generatorConvention_hnPresentation :
    hnPresentation.generatorConvention = "The generators a, b, c, d and t of Bray--Curtis HNpb.m, \
      in that order, so indices 0 through 4 have those names. Products are read left to right, \
      negative exponents denote inverses, [r,s] denotes r^-1 s^-1 r s, and r^s denotes \
      s^-1 r s." := by
  simp [hnPresentation]

/-- The transcription notes recorded for `HN`, including the correction the authors' known-errors
record makes to the twelfth relator. -/
@[simp]
theorem transcriptionNotes_hnPresentation :
    hnPresentation.transcriptionNotes = "The nineteen words in the first presentation of the \
      corrected HNpb.m file are stored as nineteen relators equal to the identity. They agree in \
      order and spelling with the five-generator presentation displayed in Section 5 of the \
      corrected paper. The corrected source uses (a*d)^2 as its twelfth relator; the authors' \
      known-errors record notes that the preprint's [a,d] at this position was wrong. An \
      independent source-to-Lean read-through remains part of the S1 review artifact." := by
  simp [hnPresentation]

/-- The generator count `HN`'s source states. With
`TauCeti.Sporadic.generatorNames_hnPresentation` this makes
`TauCeti.Sporadic.matchesMetadata_hnPresentation` an equation between two visible numbers. -/
@[simp]
theorem expectedGeneratorCount_hnPresentation : hnPresentation.expectedGeneratorCount = 5 := by
  simp [hnPresentation]

/-- The relator count `HN`'s source states; see
`TauCeti.Sporadic.expectedGeneratorCount_hnPresentation`. -/
@[simp]
theorem expectedRelatorCount_hnPresentation : hnPresentation.expectedRelatorCount = 19 := by
  simp [hnPresentation]

/-- The relator expressions transcribed for `HN`, with their generator indices written out.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer auditing the transcription never has to unfold the
row. Indices `0` through `4` are the generators `a`, `b`, `c`, `d` and `t`, and their bounds come
from `TauCeti.Sporadic.generatorNames_hnPresentation`. -/
@[simp]
theorem transcribed_hnPresentation :
    hnPresentation.transcribed =
      [ -- a⁴
        .pow (.gen ⟨0, by simp⟩) 4,
        -- [a², b]
        Relator.comm (.inv (.pow (.gen ⟨0, by simp⟩) 2)) (.inv (.gen ⟨1, by simp⟩)),
        -- b⁷
        .pow (.gen ⟨1, by simp⟩) 7,
        -- (ab²)⁴
        .pow (.gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 2) 4,
        -- a⁻²(abab³)³
        .pow (.inv (.gen ⟨0, by simp⟩)) 2 ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .pow (.gen ⟨1, by simp⟩) 3) 3,
        -- ((ab)³ab⁻³)²
        .pow (.pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3 ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.inv (.gen ⟨1, by simp⟩)) 3) 2,
        -- c²a²
        .pow (.gen ⟨2, by simp⟩) 2 ⬝ .pow (.gen ⟨0, by simp⟩) 2,
        -- [a, c]
        Relator.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.gen ⟨2, by simp⟩)),
        -- [bab, c]
        Relator.comm
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩))
          (.inv (.gen ⟨2, by simp⟩)),
        -- (bab³c)³
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 3 ⬝
          .gen ⟨2, by simp⟩) 3,
        -- d²
        .pow (.gen ⟨3, by simp⟩) 2,
        -- (ad)²
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨3, by simp⟩) 2,
        -- [b, d]
        Relator.comm (.inv (.gen ⟨1, by simp⟩)) (.inv (.gen ⟨3, by simp⟩)),
        -- d^(cbcb⁻¹)(cd)³
        .inv (.gen ⟨2, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨2, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩)) ⬝ .gen ⟨3, by simp⟩ ⬝
          (.gen ⟨2, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨2, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩)) ⬝ .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨3, by simp⟩) 3,
        -- t⁵
        .pow (.gen ⟨4, by simp⟩) 5,
        -- t^a t²
        .inv (.gen ⟨0, by simp⟩) ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.gen ⟨4, by simp⟩) 2,
        -- t^c t⁻²
        .inv (.gen ⟨2, by simp⟩) ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨2, by simp⟩ ⬝
          .pow (.inv (.gen ⟨4, by simp⟩)) 2,
        -- [t, b]
        Relator.comm (.inv (.gen ⟨4, by simp⟩)) (.inv (.gen ⟨1, by simp⟩)),
        -- (dt)³
        .pow (.gen ⟨3, by simp⟩ ⬝ .gen ⟨4, by simp⟩) 3 ] := by
  simp [hnPresentation]

/-- The generator and relator counts recorded for `HN` agree with the transcribed data. -/
theorem matchesMetadata_hnPresentation : hnPresentation.matchesMetadata := by decide

/-! ### The letter counts of the compiled words -/

/-- The lengths of the nineteen compiled relator words for `HN`, in the source's order.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.totalLength_hnPresentation`. -/
theorem map_length_relators_hnPresentation :
    hnPresentation.relators.map List.length =
      [4, 6, 7, 12, 20, 20, 4, 4, 8, 18, 2, 4, 4, 15, 5, 5, 5, 4, 6] := by
  simp [GroupPresentation.relators_def, transcribed_hnPresentation]

/-- The compiled relator words for `HN` have `153` letters in total. The fifth of them is not
reduced, so `TauCeti.Sporadic.reducedTotalLength_hnPresentation` and not this figure is the one to
compare with a published presentation length. -/
theorem totalLength_hnPresentation : hnPresentation.totalLength = 153 := by
  rw [GroupPresentation.totalLength_def, map_length_relators_hnPresentation]
  decide

/-- The lengths of the nineteen compiled relator words for `HN` after free reduction. Only the fifth
entry differs from `TauCeti.Sporadic.map_length_relators_hnPresentation`, by the cancelling pair at
the junction of the two factors of `a⁻²(abab³)³`. -/
theorem map_length_reduce_relators_hnPresentation :
    (hnPresentation.relators.map fun w => (FreeGroup.reduce w).length) =
      [4, 6, 7, 12, 18, 20, 4, 4, 8, 18, 2, 4, 4, 15, 5, 5, 5, 4, 6] := by
  simp only [GroupPresentation.relators_def, transcribed_hnPresentation, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

/-- The freely reduced relator words for `HN` have `151` letters in total. No length is recorded for
this presentation to compare it with, so this figure states the transcribed data for a reviewer to
check against the source rather than against a published number. -/
theorem reducedTotalLength_hnPresentation :
    (hnPresentation.relators.map fun w => (FreeGroup.reduce w).length).sum = 151 := by
  rw [map_length_reduce_relators_hnPresentation]
  decide

/-- Free reduction makes every compiled relator word for `HN` cyclically reduced.

This is what makes the letter count of `TauCeti.Sporadic.reducedTotalLength_hnPresentation`
comparable with a published presentation length, which is measured after free and cyclic reduction
of each relator. -/
theorem isCyclicallyReduced_reduce_mem_hnPresentation_relators :
    ∀ w ∈ hnPresentation.relators, FreeGroup.IsCyclicallyReduced (FreeGroup.reduce w) := by
  simp only [GroupPresentation.relators_def, transcribed_hnPresentation, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_comm]
  decide

end TauCeti.Sporadic
