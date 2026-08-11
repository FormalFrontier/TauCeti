/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
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

## Main definition

* `TauCeti.Sporadic.hnPresentation`: the Bray--Curtis finite presentation of `HN`.

## References

* J. N. Bray and R. T. Curtis, *Monomial modular representations and symmetric generation of the
  Harada--Norton group*, J. Algebra **268** (2003), no. 2, 723--743, Sections 4--5,
  <https://doi.org/10.1016/S0021-8693(03)00298-9>.
* The authors' corrected version and known-errors record,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HN.html>, and the corrected
  machine-readable presentation,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/Papers/HN/HNpb.m>.
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

/-- The source's commutator `[r, s] = r⁻¹ s⁻¹ r s`, represented in Mathlib's convention. -/
private abbrev sourceComm (r s : Relator (Fin 5)) : Relator (Fin 5) :=
  .comm (.inv r) (.inv s)

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
      sourceComm (.pow a 2) b,
      .pow b 7,
      .pow (a ⬝ .pow b 2) 4,
      .pow (.inv a) 2 ⬝ .pow (a ⬝ b ⬝ a ⬝ .pow b 3) 3,
      .pow (.pow (a ⬝ b) 3 ⬝ a ⬝ .pow (.inv b) 3) 2,
      .pow c 2 ⬝ .pow a 2,
      sourceComm a c,
      sourceComm (b ⬝ a ⬝ b) c,
      .pow (b ⬝ a ⬝ .pow b 3 ⬝ c) 3,
      .pow d 2,
      .pow (a ⬝ d) 2,
      sourceComm b d,
      .inv dConjugator ⬝ d ⬝ dConjugator ⬝ .pow (c ⬝ d) 3,
      .pow t 5,
      .inv a ⬝ t ⬝ a ⬝ .pow t 2,
      .inv c ⬝ t ⬝ c ⬝ .pow (.inv t) 2,
      sourceComm t b,
      .pow (d ⬝ t) 3 ]

/-- The generator and relator counts recorded for `HN` agree with the transcribed data. -/
theorem matchesMetadata_hnPresentation : hnPresentation.matchesMetadata := by decide

end TauCeti.Sporadic
