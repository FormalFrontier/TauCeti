/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Held group

This file carries the `He` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records John Bray's ATLAS version 3 presentation on
the standard generators `a` and `b` as a `TauCeti.GroupPresentation`, together with the source,
generator convention, transcription notes, and expected counts.

The presentation displayed by the ATLAS is

```text
⟨a, b | a² = b⁷ = (ab)¹⁷ = [a,b]⁶ = [a,b³]⁵
       = [a,babab⁻¹abab]
       = (ab)⁴ab²ab⁻³ababab⁻¹ab³ab⁻²ab² = 1⟩.
```

The ATLAS commutator convention is `[r,s] = r⁻¹s⁻¹rs`, opposite to Mathlib's
`commutatorElement`. Accordingly each displayed commutator is stored using
`Relator.comm (.inv r) (.inv s)`, as prescribed by `Relator`'s API. The structured expressions
otherwise preserve the displayed products and powers. The proved `Relator.toWord_toFreeGroup`
theorem is the audit boundary between these expressions and the signed words used by
`PresentedGroup`.

GAP 4.15.1 with AtlasRep 2.1.9 independently checks the seven transcribed relations on the
ATLAS 2058-point standard generators; those generators yield a simple group of order
`4030387200`. This computation is provenance for the transcription, not a Lean theorem. This file
asserts no order, finiteness, simplicity, or identification result.

## Independent source-to-Lean read-through

An independent read-through used the bytes of the ATLAS Magma source `HeG1-P1.M` whose SHA-256
digest is `6ab1294d2599ce209cb9ef53e433cdb40342244ac387c425d0682be6ab55e374`. Its constructor
`G<x,y>` and following assignments `a := x; b := y` fix the source generator order.

The rendered presentation page lists the seven active words in this order:

```text
a², b⁷, (ab)¹⁷, [a,b]⁶, [a,b³]⁵,
[a,babab⁻¹abab],
(ab)⁴ab²ab⁻³ababab⁻¹ab³ab⁻²ab².
```

These are exactly the seven entries of `hePresentation_transcribed`, after expanding the source
commutator `[r,s]` as `r⁻¹s⁻¹rs` and the two private long-word abbreviations. The Magma
constructor writes the same active words in `x,y`, but places the long commutator before
`[x,y³]⁵` and `[x,y]⁶`; the Lean row deliberately follows the rendered page's order. It also
comments out three other words, marking each redundant and two of them possibly useful, so none
belongs to the active relator list. This checks every source relator, inverse, exponent, both
source-order renderings, and the active/commented boundary independently of the original
transcription and closes this row's S1 source-to-Lean read-through.

## Independent comparison with the ATLAS permutation data

The independent comparison used the ATLAS representation `HeG1-p2058B0`, a primitive action on
2058 points whose two published MeatAxe tables are the standard generators `a` and `b`. The raw
generator files have respective SHA-256 digests
`d55a1451cd552d3caf571893754bf25ffa73c934107d820f9e0b7af1de29ccf5` and
`4790eac0de182c3b0ab5d4243ab28e31e3b768398d5e7a8a3c2f243fc95db66d`. These are independently
published representation data, not permutations obtained from the presentation transcribed here.

Decoding the two one-based image tables gives permutations of orders `2` and `7`, whose product
has order `17`. Direct evaluation of the seven compiled relators in this module makes every one
the identity. A Schreier--Sims calculation from the same decoded tables gives generated order
`4030387200`, agreeing with the ATLAS order check for this representation.

The check used Python 3.14.6 and SymPy 1.14.0. Concatenating the zero-based forward image tables for
`a` and then `b`, with each image stored as a two-byte little-endian integer, has SHA-256
`4a386b7656182c087d66c18ca3ee9f6c4cc61b416d23f1623b97996ce8499da5`. This is the independent
comparison artifact required by S1; no external code or permutation data is imported into Tau Ceti.

For separate corroboration, `finite-simple-groups-lean` at commit
`7f09e33a9ceef6b59ce03e34cd4f0558c763e325` defines `hea` and `heb` by coset enumeration from this
same seven-relator presentation and proves that their generated subgroup has order `4030387200`
and is simple. Because that action is derived from the same relators, it is not the independent
transcription comparison above and is not used as one; its order and simplicity proofs instead
give kernel-checked evidence about the quotient action obtained from the presentation.

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out, and the provenance a manifest row
exists to record. Together with `TauCeti.GroupPresentation.relators_def` and
`TauCeti.GroupPresentation.mem_relatorSet_iff` the first of those determines the compiled words and
the relations defining the presented group, so a consumer reasons about the row without unfolding
it.

Three decidable checks accompany those equations. The relator lengths and their total record the
compiled data one word at a time and in aggregate, and cyclic reducedness is what makes such a
letter count comparable with a published presentation length, since both are measured after free
and cyclic reduction of each relator. This row has no published length to check against: Bray's
presentation page for `He` is one of the 1997 stubs that record `Length ??`, and the ATLAS page and
its Magma source file give no figure either. The total below therefore states the transcribed data
for a reviewer to compare with the source, rather than checking it against a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.hePresentation`: John Bray's ATLAS finite presentation of `He`.
* `TauCeti.Sporadic.hePresentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.hePresentation_map_length_relators`,
  `TauCeti.Sporadic.hePresentation_totalLength` and
  `TauCeti.Sporadic.hePresentation_relatorsCyclicallyReduced`: the three checks on the compiled
  words.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, presentation `HeG1-P1`, contributed by John Bray,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1>.
* J. N. Bray, presentation page for the Held group,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/He.html>, which records `Length ??` and so
  publishes no letter count for this presentation.
* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, primitive permutation representation `HeG1-p2058B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/HeG1-p2058B0>.
* KitaKen1, *FiniteSimpleGroups*, `He` construction at commit
  `7f09e33a9ceef6b59ce03e34cd4f0558c763e325`,
  <https://github.com/KitaKen1/finite-simple-groups-lean>.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The word `babab⁻¹abab` in the long commutator of Bray's presentation. -/
private abbrev commutatorWord : Relator (Fin 2) :=
  b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ b ⬝ a ⬝ b

/-- The final relator in Bray's presentation, before setting it equal to the identity. -/
private abbrev finalWord : Relator (Fin 2) :=
  .pow (a ⬝ b) 4 ⬝ a ⬝ .pow b 2 ⬝ a ⬝ .pow (.inv b) 3 ⬝
    a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ .pow b 3 ⬝ a ⬝
    .pow (.inv b) 2 ⬝ a ⬝ .pow b 2

/-- John Bray's ATLAS version 3 finite presentation of the Held group `He` on its standard
generators `a` and `b`.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators in a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def hePresentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "HeG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1"
  generatorConvention := "The ATLAS standard generators a and b, in that order, so index 0 is a \
    and index 1 is b. Products are read left to right, negative exponents denote inverses, and \
    [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The seven displayed words are stored as seven relators equal to the \
    identity. ATLAS distinguishes HeG1-P1 from its semi-presentation. GAP 4.15.1 with AtlasRep \
    2.1.9 checks these relators on the independent ATLAS 2058-point generators, which generate a \
    simple group of order 4030387200."
  expectedGeneratorCount := 2
  expectedRelatorCount := 7
  transcribed :=
    [ .pow a 2,
      .pow b 7,
      .pow (a ⬝ b) 17,
      .pow (.comm (.inv a) (.inv b)) 6,
      .pow (.comm (.inv a) (.inv (.pow b 3))) 5,
      .comm (.inv a) (.inv commutatorWord),
      finalWord ]

/-- The generator names recorded for `He`. The row's body is sealed, so this is what lets a
consumer see that it is a two-generator presentation. -/
@[simp]
theorem hePresentation_generatorNames : hePresentation.generatorNames = ["a", "b"] := by
  simp [hePresentation]

/-- The source recorded for `He`. The row's body is sealed, so this equation publishes the citation
itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem hePresentation_source :
    hePresentation.source = "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
      Representations, version 3; presentation contributed by John Bray" := by
  simp [hePresentation]

/-- The locator recorded for `He`, pointing at the presentation inside its source. -/
@[simp]
theorem hePresentation_sourceLocator :
    hePresentation.sourceLocator =
      "HeG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1" := by
  simp [hePresentation]

/-- The generator convention recorded for `He`, fixing which generator each relator index names and
which commutator convention the source uses. -/
@[simp]
theorem hePresentation_generatorConvention :
    hePresentation.generatorConvention = "The ATLAS standard generators a and b, in that order, \
      so index 0 is a and index 1 is b. Products are read left to right, negative exponents denote \
      inverses, and [r,s] denotes r^-1 s^-1 r s." := by
  simp [hePresentation]

/-- The transcription notes recorded for `He`. -/
@[simp]
theorem hePresentation_transcriptionNotes :
    hePresentation.transcriptionNotes = "The seven displayed words are stored as seven relators \
      equal to the identity. ATLAS distinguishes HeG1-P1 from its semi-presentation. GAP 4.15.1 \
      with AtlasRep 2.1.9 checks these relators on the independent ATLAS 2058-point generators, \
      which generate a simple group of order 4030387200." := by
  simp [hePresentation]

/-- The generator count `He`'s source states. With
`TauCeti.Sporadic.hePresentation_generatorNames` this makes
`TauCeti.Sporadic.hePresentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem hePresentation_expectedGeneratorCount : hePresentation.expectedGeneratorCount = 2 := by
  simp [hePresentation]

/-- The relator count `He`'s source states; see
`TauCeti.Sporadic.hePresentation_expectedGeneratorCount`. -/
@[simp]
theorem hePresentation_expectedRelatorCount : hePresentation.expectedRelatorCount = 7 := by
  simp [hePresentation]

/-- The relator expressions transcribed for `He`, with their generator indices written out and the
private abbreviations of this file expanded.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Index `0` is the
generator `a` and index `1` is `b`, and the bounds come from
`TauCeti.Sporadic.hePresentation_generatorNames`. -/
@[simp]
theorem hePresentation_transcribed :
    hePresentation.transcribed =
      [ -- a²
        .pow (.gen ⟨0, by simp⟩) 2,
        -- b⁷
        .pow (.gen ⟨1, by simp⟩) 7,
        -- (ab)¹⁷
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 17,
        -- [a,b]⁶, in the source's commutator convention
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.gen ⟨1, by simp⟩))) 6,
        -- [a,b³]⁵
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.pow (.gen ⟨1, by simp⟩) 3))) 5,
        -- [a, babab⁻¹abab]
        .comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
            .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩)),
        -- (ab)⁴ab²ab⁻³ababab⁻¹ab³ab⁻²ab²
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 4 ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.gen ⟨1, by simp⟩) 2 ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.inv (.gen ⟨1, by simp⟩)) 3 ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩) ⬝
          .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 3 ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.inv (.gen ⟨1, by simp⟩)) 2 ⬝ .gen ⟨0, by simp⟩ ⬝
          .pow (.gen ⟨1, by simp⟩) 2 ] := by
  simp [hePresentation]

/-- The generator and relator counts recorded for `He` agree with the transcribed data. -/
theorem hePresentation_matchesMetadata : hePresentation.matchesMetadata := by decide

/-- The lengths of the seven compiled relator words for `He`, in the order of the source.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.hePresentation_totalLength`. -/
theorem hePresentation_map_length_relators :
    hePresentation.relators.map List.length = [2, 7, 34, 24, 40, 20, 31] := by
  simp [GroupPresentation.relators_def, hePresentation]

/-- The compiled relator words for `He` have `158` letters in total. The source records no
presentation length, so this figure states the transcribed data for a reviewer to compare with the
source, rather than checking it against a recorded number. -/
theorem hePresentation_totalLength : hePresentation.totalLength = 158 := by
  rw [GroupPresentation.totalLength_def, hePresentation_map_length_relators]
  decide

/-- Every compiled relator word for `He` is cyclically reduced. This is what makes the letter count
of `TauCeti.Sporadic.hePresentation_totalLength` comparable with a published presentation length,
which is measured after free and cyclic reduction of each relator. -/
theorem hePresentation_relatorsCyclicallyReduced :
    hePresentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    hePresentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_comm, Relator.toWord_gen]
  decide

end TauCeti.Sporadic
