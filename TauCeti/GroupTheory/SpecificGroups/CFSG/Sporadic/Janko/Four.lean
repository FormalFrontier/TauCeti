/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the fourth Janko group

This file carries the `J₄` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records John Bray's ATLAS version 3 presentation on
the type II standard generators `x`, `y`, and `t` as a `TauCeti.GroupPresentation`, together with
its exact source, generator convention, transcription notes, expected counts, and count check.

The twelve relators are

```text
x², y³, (xy)²³, [x,y]¹², [x,yxy]⁵,
(xyxyxy⁻¹)³(xyxy⁻¹xy⁻¹)³,
(xy(xyxy⁻¹)³)⁴,
t², [t,x], [t,yxy(xy⁻¹)²(xy)³],
(y t^(yxy⁻¹xyxy⁻¹x))³,
((yxyxyxy)³ t t^((xy)³y(xy)⁶y))².
```

Here `r^s` means `s⁻¹rs`, as in the ATLAS Magma source. The source's commutator convention is
`[r,s] = r⁻¹s⁻¹rs`, opposite to Mathlib's `commutatorElement`, so a source commutator is stored as
`Relator.comm (.inv r) (.inv s)`. The structured expressions otherwise preserve the source's
products, powers, and conjugates. The proved `TauCeti.Relator.toWord_toFreeGroup` is the audit
boundary between these expressions and the signed words consumed by `PresentedGroup`.

Bolt, Bray, and Curtis prove a symmetric presentation of `J₄` and convert it into an ordinary
three-generator presentation. The ATLAS publishes the resulting relator list as `J4G2-P1`; its
Magma file also records the double-coset-enumeration route through the involution centralizer
`2^(1+12)·3·M₂₂·2`, of index `3980549947`.

As an independent transcription check, GAP 4.15.1 with AtlasRep 2.1.9 evaluates all twelve
compiled words below to the identity after applying the ATLAS restandardization program from the
112-dimensional characteristic-two representation's type I generators to type II generators.
This computation is provenance rather than a Lean theorem: the file asserts no order, finiteness,
simplicity, or identification result. The independent `FiniteSimpleGroups` development named by
the roadmap does not cover `J₄`, so no cross-check against that development is available.

## Independent source-to-Lean read-through

An independent read-through used the bytes of the ATLAS Magma source `J4G2-P1.M` whose SHA-256
digest is `0ed9ed620f24b22490d2cb32f202ecbeb422ff665b4614b9ad8c6a6d7b118135`. Its constructor
`G<x,y,t>` fixes exactly the three-generator order published by `j4Presentation_generatorNames`.

The first seven constructor entries are, one for one, the seven active `M₂₄`-presentation words
on `x,y` displayed above. The remaining five entries extend them in this source order:

```text
t²,
[t,x],
[t, yxy (xy⁻¹)² (xy)³],
(y t^(yxy⁻¹xyxy⁻¹x))³,
((yxyxyxy)³ t t^((xy)³y(xy)⁶y))².
```

They agree with entries eight through twelve of `j4Presentation_transcribed`. In the last two,
expanding each source conjugate `t^s` as `s⁻¹ts` gives precisely `sourceConj t firstConjugator`
and `sourceConj t secondConjugator`; the two conjugating words agree letter for letter with the
Magma file. None of the twelve constructor entries is commented out or marked redundant. This
checks every source relator, inverse, exponent, conjugating word, and source-order position
independently of the original transcription and closes this row's S1 source-to-Lean read-through.

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out, and the provenance a manifest row
exists to record. Together with `TauCeti.GroupPresentation.relators_def` and
`TauCeti.GroupPresentation.mem_relatorSet_iff` the first of those determines the compiled words and
the relations defining the presented group, so a consumer reasons about the row without unfolding
it.

Three decidable checks accompany those equations. The relator lengths and their total record the
compiled data one word at a time and in aggregate, and cyclic reducedness is what makes such a
letter count comparable with a published presentation length, since both are measured after free
and cyclic reduction of each relator. This row records no published length, so the total here
states the transcription for a reviewer to compare with the source, rather than checking it against
a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.j4Presentation`: John Bray's ATLAS finite presentation of `J₄`.
* `TauCeti.Sporadic.j4Presentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.j4Presentation_map_length_relators`,
  `TauCeti.Sporadic.j4Presentation_totalLength` and
  `TauCeti.Sporadic.j4Presentation_relatorsCyclicallyReduced`: the three checks on the compiled
  words.

## References

* S. W. Bolt, J. N. Bray, and R. T. Curtis, *Symmetric presentation of the Janko group J₄*,
  Journal of the London Mathematical Society **76** (2007), 683--701,
  <https://doi.org/10.1112/jlms/jdm086>.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, presentation `J4G2-P1`, contributed by John Bray,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J4G2-P1>, with the relator list and enumeration
  notes in <https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/mag/J4G2-P1.M>.
-/

public section

namespace TauCeti.Sporadic

private abbrev x : Relator (Fin 3) := .gen 0

private abbrev y : Relator (Fin 3) := .gen 1

private abbrev t : Relator (Fin 3) := .gen 2

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The source's commutator `[r,s] = r⁻¹s⁻¹rs`, represented in Mathlib's convention. -/
private abbrev sourceComm (r s : Relator (Fin 3)) : Relator (Fin 3) :=
  .comm (.inv r) (.inv s)

/-- The source's conjugate `r^s = s⁻¹rs`. -/
private abbrev sourceConj (r s : Relator (Fin 3)) : Relator (Fin 3) :=
  .inv s ⬝ r ⬝ s

/-- The sixth relator of the ATLAS presentation. -/
private abbrev sixthWord : Relator (Fin 3) :=
  .pow (x ⬝ y ⬝ x ⬝ y ⬝ x ⬝ .inv y) 3 ⬝
    .pow (x ⬝ y ⬝ x ⬝ .inv y ⬝ x ⬝ .inv y) 3

/-- The word conjugating `t` in the eleventh relator. -/
private abbrev firstConjugator : Relator (Fin 3) :=
  y ⬝ x ⬝ .inv y ⬝ x ⬝ y ⬝ x ⬝ .inv y ⬝ x

/-- The word conjugating `t` in the twelfth relator. -/
private abbrev secondConjugator : Relator (Fin 3) :=
  .pow (x ⬝ y) 3 ⬝ y ⬝ .pow (x ⬝ y) 6 ⬝ y

/-- John Bray's ATLAS version 3 finite presentation of the fourth Janko group `J₄` on its
type II standard generators `x`, `y`, and `t`.

The ATLAS lists this as a presentation of the abstract group, separately from the relations used
only to recognize standard generators inside an existing group. No structural property of the
presented group is asserted here: this definition records only the cited generators and relators.
-/
def j4Presentation : GroupPresentation where
  generatorNames := ["x", "y", "t"]
  source := "S. W. Bolt, J. N. Bray, and R. T. Curtis, Symmetric presentation of the Janko \
    group J4, J. London Math. Soc. 76 (2007), 683-701; R. A. Wilson, R. A. Parker, J. N. Bray \
    et al., ATLAS of Finite Group Representations, version 3"
  sourceLocator := "Bolt-Bray-Curtis, Section 5, doi:10.1112/jlms/jdm086; ATLAS presentation \
    J4G2-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J4G2-P1; relator list and \
    enumeration notes, https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/mag/J4G2-P1.M"
  generatorConvention := "The ATLAS type II standard generators x, y, and t of J4, in that \
    order, so indices 0, 1, and 2 are x, y, and t. Products are read left to right, negative \
    exponents denote inverses, [r,s] denotes r^-1 s^-1 r s, and r^s denotes s^-1 r s."
  transcriptionNotes := "The twelve words are stored in the order of the ATLAS Magma file; \
    none is marked redundant. Source conjugates are expanded as s^-1*r*s, while products and \
    natural powers remain structured. GAP 4.15.1 with AtlasRep 2.1.9 checks the twelve compiled \
    words on type II generators obtained by the ATLAS restandardization program from the \
    112-dimensional characteristic-two matrix representation of J4. The source's double-coset \
    route enumerates 3980549947 cosets of the involution centralizer."
  expectedGeneratorCount := 3
  expectedRelatorCount := 12
  transcribed :=
    [ .pow x 2,
      .pow y 3,
      .pow (x ⬝ y) 23,
      .pow (sourceComm x y) 12,
      .pow (sourceComm x (y ⬝ x ⬝ y)) 5,
      sixthWord,
      .pow (x ⬝ y ⬝ .pow (x ⬝ y ⬝ x ⬝ .inv y) 3) 4,
      .pow t 2,
      sourceComm t x,
      sourceComm t (y ⬝ x ⬝ y ⬝ .pow (x ⬝ .inv y) 2 ⬝ .pow (x ⬝ y) 3),
      .pow (y ⬝ sourceConj t firstConjugator) 3,
      .pow (.pow (y ⬝ x ⬝ y ⬝ x ⬝ y ⬝ x ⬝ y) 3 ⬝ t ⬝
        sourceConj t secondConjugator) 2 ]

/-- The generator names recorded for `J₄`. The row's body is sealed, so this is what lets a
consumer see that it is a three-generator presentation. -/
@[simp]
theorem j4Presentation_generatorNames : j4Presentation.generatorNames = ["x", "y", "t"] := by
  simp [j4Presentation]

/-- The source recorded for `J₄`. The row's body is sealed, so this equation is what publishes the
citation itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem j4Presentation_source :
    j4Presentation.source = "S. W. Bolt, J. N. Bray, and R. T. Curtis, Symmetric presentation of \
      the Janko group J4, J. London Math. Soc. 76 (2007), 683-701; R. A. Wilson, R. A. Parker, \
      J. N. Bray et al., ATLAS of Finite Group Representations, version 3" := by
  simp [j4Presentation]

/-- The locator recorded for `J₄`, pointing at the presentation inside its sources. -/
@[simp]
theorem j4Presentation_sourceLocator :
    j4Presentation.sourceLocator = "Bolt-Bray-Curtis, Section 5, doi:10.1112/jlms/jdm086; ATLAS \
      presentation J4G2-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/J4G2-P1; relator list \
      and enumeration notes, https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/mag/J4G2-P1.M" := by
  simp [j4Presentation]

/-- The generator convention recorded for `J₄`, fixing which generator each relator index names and
which commutator and conjugation conventions the source uses. -/
@[simp]
theorem j4Presentation_generatorConvention :
    j4Presentation.generatorConvention = "The ATLAS type II standard generators x, y, and t of \
      J4, in that order, so indices 0, 1, and 2 are x, y, and t. Products are read left to right, \
      negative exponents denote inverses, [r,s] denotes r^-1 s^-1 r s, and r^s denotes \
      s^-1 r s." := by
  simp [j4Presentation]

/-- The transcription notes recorded for `J₄`. -/
@[simp]
theorem j4Presentation_transcriptionNotes :
    j4Presentation.transcriptionNotes = "The twelve words are stored in the order of the ATLAS \
      Magma file; none is marked redundant. Source conjugates are expanded as s^-1*r*s, while \
      products and natural powers remain structured. GAP 4.15.1 with AtlasRep 2.1.9 checks the \
      twelve compiled words on type II generators obtained by the ATLAS restandardization program \
      from the 112-dimensional characteristic-two matrix representation of J4. The source's \
      double-coset route enumerates 3980549947 cosets of the involution centralizer." := by
  simp [j4Presentation]

/-- The generator count `J₄`'s source states. With
`TauCeti.Sporadic.j4Presentation_generatorNames` this is what makes
`TauCeti.Sporadic.j4Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem j4Presentation_expectedGeneratorCount : j4Presentation.expectedGeneratorCount = 3 := by
  simp [j4Presentation]

/-- The relator count `J₄`'s source states; see
`TauCeti.Sporadic.j4Presentation_expectedGeneratorCount`. -/
@[simp]
theorem j4Presentation_expectedRelatorCount : j4Presentation.expectedRelatorCount = 12 := by
  simp [j4Presentation]

/-- The relator expressions transcribed for `J₄`, with their generator indices written out and the
private abbreviations of this file expanded.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Indices `0`, `1` and
`2` are the generators `x`, `y` and `t`, and the bounds come from
`TauCeti.Sporadic.j4Presentation_generatorNames`. Each source conjugate `r^s` appears as the
bracketed `s⁻¹rs`, since the stored expression is a tree and not a flat word. -/
@[simp]
theorem j4Presentation_transcribed :
    j4Presentation.transcribed =
      [ -- x²
        .pow (.gen ⟨0, by simp⟩) 2,
        -- y³
        .pow (.gen ⟨1, by simp⟩) 3,
        -- (xy)²³
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 23,
        -- [x,y]¹², in the source's commutator convention
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.gen ⟨1, by simp⟩))) 12,
        -- [x,yxy]⁵
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩))) 5,
        -- (xyxyxy⁻¹)³(xyxy⁻¹xy⁻¹)³
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩)) 3 ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩)) 3,
        -- (xy(xyxy⁻¹)³)⁴
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩)) 3) 4,
        -- t²
        .pow (.gen ⟨2, by simp⟩) 2,
        -- [t,x]
        .comm (.inv (.gen ⟨2, by simp⟩)) (.inv (.gen ⟨0, by simp⟩)),
        -- [t,yxy(xy⁻¹)²(xy)³]
        .comm (.inv (.gen ⟨2, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
            .pow (.gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩)) 2 ⬝
            .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3)),
        -- (y t^(yxy⁻¹xyxy⁻¹x))³
        .pow (.gen ⟨1, by simp⟩ ⬝
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩) ⬝
              .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
              .inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩) ⬝
            .gen ⟨2, by simp⟩ ⬝
            (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩) ⬝
              .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
              .inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩))) 3,
        -- ((yxyxyxy)³ t t^((xy)³y(xy)⁶y))²
        .pow (.pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
            .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3 ⬝
          .gen ⟨2, by simp⟩ ⬝
          (.inv (.pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3 ⬝ .gen ⟨1, by simp⟩ ⬝
              .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 6 ⬝ .gen ⟨1, by simp⟩) ⬝
            .gen ⟨2, by simp⟩ ⬝
            (.pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3 ⬝ .gen ⟨1, by simp⟩ ⬝
              .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 6 ⬝ .gen ⟨1, by simp⟩))) 2 ] := by
  simp [j4Presentation]

/-- The generator and relator counts recorded for `J₄` agree with the transcribed data. -/
theorem j4Presentation_matchesMetadata : j4Presentation.matchesMetadata := by
  decide

/-- The lengths of the twelve compiled relator words for `J₄`, in the order of the ATLAS Magma
file.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.j4Presentation_totalLength`. -/
theorem j4Presentation_map_length_relators :
    j4Presentation.relators.map List.length =
      [2, 3, 46, 48, 40, 36, 56, 2, 4, 28, 54, 126] := by
  simp [GroupPresentation.relators_def, j4Presentation]

/-- The compiled relator words for `J₄` have `445` letters in total. The row records no published
length, so this figure states the transcribed data for a reviewer to compare with the source,
rather than checking it against a recorded number. -/
theorem j4Presentation_totalLength : j4Presentation.totalLength = 445 := by
  rw [GroupPresentation.totalLength_def, j4Presentation_map_length_relators]
  decide

/-- Every compiled relator word for `J₄` is cyclically reduced. This is what makes the letter count
of `TauCeti.Sporadic.j4Presentation_totalLength` comparable with a published presentation length,
which is measured after free and cyclic reduction of each relator. -/
theorem j4Presentation_relatorsCyclicallyReduced :
    j4Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    j4Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_comm, Relator.toWord_gen]
  decide

end TauCeti.Sporadic
