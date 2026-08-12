/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
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
relations. This file asserts no order, finiteness, simplicity, or identification result. A separate
source-to-Lean read-through remains part of the S1 review artifact required by the roadmap.

## Main definition

* `TauCeti.Sporadic.ruPresentation`: Soicher's finite presentation of the Rudvalis group `Ru`.

## References

* J. D. Bradley, R. T. Curtis, and M. Aslam Malik, *Symmetric generation of the Rudvalis group*,
  Journal of the London Mathematical Society **82** (2010), 643--662,
  <https://doi.org/10.1112/jlms/jdq039>.
* L. H. Soicher, `tcenum`, presentation file `presentations/Ru`, commit
  `fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1`,
  <https://github.com/lhsoicher/tcenum/blob/fb9dd89130fca8ad7dc4a92537c96ce7b30b62f1/presentations/Ru>.
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
    Coxeter relations. A separate source-to-Lean read-through remains an S1 review obligation."
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
      and hence supplies no Coxeter relations. A separate source-to-Lean read-through remains an \
      S1 review obligation." := by
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

end TauCeti.Sporadic
