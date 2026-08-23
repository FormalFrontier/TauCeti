/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Coxeter

/-!
# A transcribed presentation of the third Fischer group

This file carries the `Fi24Prime` row of the sporadic presentation data required by milestone S1
of `TauCetiRoadmap/CFSGStatement/README.md`. The cited source presents the 3-transposition group
`Fi₂₄'·2` and proves that its commutator subgroup is the simple group `Fi₂₄'`. It also gives
the index-two subgroup generators

```text
ab, ac, ad, ae, af, ag, ah, ai, aj, ak.
```

The presentation recorded here is the Reidemeister--Schreier presentation of that commutator
subgroup. An eleventh Schreier generator `al` is retained instead of using the source relation
`l = (abcdefh)⁹` to eliminate it; retaining it keeps every derived relator a direct rewrite of one
displayed source relator.

The source presentation has twelve involutory generators, indexed here as
`a,b,c,d,e,f,g,h,i,j,k,l`. Its Coxeter graph is

```text
l -- k -- a -- b -- c -- d -- e -- f -- g -- j
                         |
                         h -- i
```

and it has two further relations

```text
l = (a b c d e f h)^9,
(d c b a k l d e f g j d h i)^17 = 1.
```

Sending every source generator to the nontrivial element of `C₂` is the quotient onto
`Fi₂₄'·2 / Fi₂₄'`. With transversal `{1,a}`, the Schreier generator attached to `x` is
`ax`. Because all source generators are involutions, a source letter in an even position rewrites
as `(ax)⁻¹` and one in an odd position as `ax`; conjugating a relator by `a` exchanges the two
signs. Each off-diagonal Coxeter relator and each further relator therefore contributes those two
rewrites. The square relators are precisely the relations used to eliminate the other half of the
Schreier generators: after that elimination each rewrites to `u⁻¹u` or `uu⁻¹`, so none remains.

Thus the `66` off-diagonal Coxeter relators and two further relators yield `2 · (66 + 2) = 136`
relators on eleven generators. `TauCeti.Sporadic.fi24PrimePresentation_matchesMetadata` checks
this count, while `TauCeti.Sporadic.even_length_of_mem_fi24AutomorphismRelators` checks that every
source relator does lie in the index-two subgroup before the rewrite is applied.

Nothing here asserts that the presented group is nontrivial, finite, simple, of any particular
order, or isomorphic to another realization. Kim and Michler prove that the commutator subgroup of
the displayed source presentation is `Fi₂₄'`; Reidemeister--Schreier rewriting transfers that
presentation to the subgroup. A separate source-to-Lean read-through remains the S1 review
artifact required by the roadmap.

## Main definitions

* `TauCeti.Sporadic.fi24AutomorphismCoxeterMatrix`: the source's numbered Coxeter diagram.
* `TauCeti.Sporadic.fi24AutomorphismRelators`: all eighty source relators for `Fi₂₄'·2`.
* `TauCeti.Sporadic.fi24SchreierRewrite`: the Reidemeister--Schreier rewrite of a source relator.
* `TauCeti.Sporadic.fi24PrimePresentation`: the Reidemeister--Schreier presentation of `Fi₂₄'`.

Every definition here has its body sealed, and each is pinned by a public characteristic equation
named after it: the `_def` theorems below, the evaluation lemmas
`TauCeti.Sporadic.fi24AutomorphismCoxeterMatrix_apply`, `TauCeti.Sporadic.fi24TargetGenerator_val`
and `TauCeti.Sporadic.fi24SchreierFactors_nil`/`_cons`, and the field equations of the presentation
row ending in `TauCeti.Sporadic.fi24PrimePresentation_relatorLetters`, jointly determine every
transcribed relation without unfolding a single body.

## References

* H. K. Kim and G. O. Michler, *Construction of Fischer's sporadic group Fi₂₄' inside
  GL₈₆₇₁(13)*, Journal of Algebra **322** (2009), 193--233,
  <https://doi.org/10.1016/j.jalgebra.2009.05.003>, also <https://arxiv.org/abs/0906.1064>.
  Lemma 6.2 reproduces the full presentation, proves that its commutator subgroup is simple, and
  gives the ten subgroup generators above; Theorem 6.3 identifies that subgroup with `Fi₂₄'`.
* J. I. Hall and L. H. Soicher, *Presentations of some 3-transposition groups*, Communications in
  Algebra **23** (1995), 2517--2559, <https://doi.org/10.1080/00927879508825358>, the original
  source of the presentation reproduced by Kim and Michler.
* M. Hall, Jr., *The Theory of Groups*, Macmillan, 1959, Chapter 7, for the
  Reidemeister--Schreier rewriting process used to pass to the index-two subgroup.
-/

public section

namespace TauCeti.Sporadic

/-! ## The source presentation of `Fi₂₄'·2` -/

/-- The eleven edges in the source's Coxeter diagram, using the generator order
`a,b,c,d,e,f,g,h,i,j,k,l`. -/
def fi24AutomorphismEdges : List (Fin 12 × Fin 12) :=
  [(11, 10), (10, 0), (0, 1), (1, 2), (2, 3), (3, 4),
    (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)]

/-- The edges of the source diagram, spelled out. The body is sealed, so this equation is what
publishes the transcribed diagram: with `TauCeti.Sporadic.fi24AutomorphismCoxeterMatrix_apply` it
determines every entry of the source Coxeter matrix.

This is deliberately not `@[simp]`: the simp-normal fact about this list is
`TauCeti.Sporadic.length_fi24AutomorphismEdges`, while this equation is available for an explicit
audit of the transcribed edges. -/
theorem fi24AutomorphismEdges_def :
    fi24AutomorphismEdges =
      [(11, 10), (10, 0), (0, 1), (1, 2), (2, 3), (3, 4),
        (4, 5), (5, 6), (6, 9), (3, 7), (7, 8)] := by
  simp only [fi24AutomorphismEdges]

/-- The Coxeter matrix of Hall--Soicher's twelve-generator presentation of `Fi₂₄'·2`.
Adjacent nodes have entry three and all other distinct nodes have entry two. -/
def fi24AutomorphismCoxeterMatrix : CoxeterMatrix (Fin 12) where
  M := Matrix.of fun i j =>
    if i = j then 1
    else if (i, j) ∈ fi24AutomorphismEdges ∨ (j, i) ∈ fi24AutomorphismEdges then 3 else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rcases eq_or_ne i j with rfl | h
    · rfl
    · simp only [h, Ne.symm h, ↓reduceIte]
      exact if_congr or_comm rfl rfl
  diagonal i := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ↓reduceIte]
    split <;> omega

/-- Evaluation of the source Coxeter matrix directly from its edge list. -/
@[simp]
theorem fi24AutomorphismCoxeterMatrix_apply (i j : Fin 12) :
    fi24AutomorphismCoxeterMatrix i j =
      if i = j then 1
      else if (i, j) ∈ fi24AutomorphismEdges ∨ (j, i) ∈ fi24AutomorphismEdges then 3 else 2 := by
  simp only [fi24AutomorphismCoxeterMatrix, Matrix.of_apply]

/-- The source diagram has eleven edges. -/
@[simp]
theorem length_fi24AutomorphismEdges : fi24AutomorphismEdges.length = 11 := by decide

/-- The `66` unordered pairs of distinct source generators. -/
private def sourcePairs : List (Sym2 (Fin 12)) :=
  (List.finRange 12).sym2.filter fun z => z.inf ≠ z.sup

/-- The off-diagonal Coxeter relators in the order supplied by `List.sym2`. -/
def fi24SourcePairRelators : List (Relator (Fin 12)) :=
  sourcePairs.map fun z =>
    coxeterRelator fi24AutomorphismCoxeterMatrix z.inf z.sup

/-- The off-diagonal Coxeter relators, spelled out over Mathlib's unordered-pair list. The body is
sealed, so this equation is what publishes which pairs are taken and in which order.

Like `TauCeti.GroupPresentation.relators_def` this is deliberately not `@[simp]`: the simp normal
form of the list is the count `TauCeti.Sporadic.length_fi24SourcePairRelators`, not the enumeration
of all sixty-six pairs. -/
theorem fi24SourcePairRelators_def :
    fi24SourcePairRelators =
      ((List.finRange 12).sym2.filter fun z => z.inf ≠ z.sup).map fun z =>
        coxeterRelator fi24AutomorphismCoxeterMatrix z.inf z.sup := by
  simp only [fi24SourcePairRelators, sourcePairs]

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The seven-letter right-hand side of the source equation for `l`, before taking its ninth
power. -/
def fi24SourceEquationWord : Relator (Fin 12) :=
  .gen 0 ⬝ .gen 1 ⬝ .gen 2 ⬝ .gen 3 ⬝ .gen 4 ⬝ .gen 5 ⬝ .gen 7

/-- The letters of the source word `a b c d e f h`. The body is sealed, so this equation is what
lets an audit read the transcribed word off against the source.

This equation and the ones from here to `TauCeti.Sporadic.fi24AutomorphismRelators_def` are
deliberately not `@[simp]`. Unfolding a source word underneath its ninth or seventeenth power makes
`simp` rebuild the compiled word letter by letter and exceed the recursion limit; the simp-normal
facts about these definitions are the length lemmas below. -/
theorem fi24SourceEquationWord_def :
    fi24SourceEquationWord =
      .gen 0 ⬝ .gen 1 ⬝ .gen 2 ⬝ .gen 3 ⬝ .gen 4 ⬝ .gen 5 ⬝ .gen 7 := by
  simp only [fi24SourceEquationWord]

/-- The fourteen-letter word in the source's final relation. -/
def fi24SourceLongWord : Relator (Fin 12) :=
  .gen 3 ⬝ .gen 2 ⬝ .gen 1 ⬝ .gen 0 ⬝ .gen 10 ⬝ .gen 11 ⬝ .gen 3 ⬝ .gen 4 ⬝ .gen 5 ⬝ .gen 6 ⬝
    .gen 9 ⬝ .gen 3 ⬝ .gen 7 ⬝ .gen 8

/-- The letters of the source word `d c b a k l d e f g j d h i`. The body is sealed, so this
equation is what lets an audit read the transcribed word off against the source. -/
theorem fi24SourceLongWord_def :
    fi24SourceLongWord =
      .gen 3 ⬝ .gen 2 ⬝ .gen 1 ⬝ .gen 0 ⬝ .gen 10 ⬝ .gen 11 ⬝ .gen 3 ⬝ .gen 4 ⬝ .gen 5 ⬝ .gen 6 ⬝
        .gen 9 ⬝ .gen 3 ⬝ .gen 7 ⬝ .gen 8 := by
  simp only [fi24SourceLongWord]

/-- The source relation `l = (a b c d e f h)^9`, stored as a relator. -/
def fi24SourceEquationRelator : Relator (Fin 12) :=
  (Relator.gen 11).div (.pow fi24SourceEquationWord 9)

/-- The source equation for `l`, compiled as the relator `l · ((a b c d e f h)^9)⁻¹`. -/
theorem fi24SourceEquationRelator_def :
    fi24SourceEquationRelator = (Relator.gen 11).div (.pow fi24SourceEquationWord 9) := by
  simp only [fi24SourceEquationRelator]

/-- The source relation `(d c b a k l d e f g j d h i)^17 = 1`. -/
def fi24SourceLongRelator : Relator (Fin 12) := .pow fi24SourceLongWord 17

/-- The source's final relation, compiled as the seventeenth power of its fourteen-letter word. -/
theorem fi24SourceLongRelator_def :
    fi24SourceLongRelator = .pow fi24SourceLongWord 17 := by
  simp only [fi24SourceLongRelator]

/-- The two non-Coxeter relators in the source presentation: the displayed equation for `l`,
followed by the long relator. -/
def fi24AutomorphismAdditionalRelators : List (Relator (Fin 12)) :=
  [fi24SourceEquationRelator, fi24SourceLongRelator]

/-- The two additional source relators, in the order in which the source displays them. -/
theorem fi24AutomorphismAdditionalRelators_def :
    fi24AutomorphismAdditionalRelators = [fi24SourceEquationRelator, fi24SourceLongRelator] := by
  simp only [fi24AutomorphismAdditionalRelators]

/-- The complete eighty-relator Hall--Soicher presentation of `Fi₂₄'·2`: all Coxeter
relations of the diagram, followed by the two additional source relations. -/
def fi24AutomorphismRelators : List (Relator (Fin 12)) :=
  coxeterRelators fi24AutomorphismCoxeterMatrix ++ fi24AutomorphismAdditionalRelators

/-- The source relator list, spelled out as the diagram's Coxeter relators followed by the two
displayed relations. -/
theorem fi24AutomorphismRelators_def :
    fi24AutomorphismRelators =
      coxeterRelators fi24AutomorphismCoxeterMatrix ++ fi24AutomorphismAdditionalRelators := by
  simp only [fi24AutomorphismRelators]

/-- The source presentation has eighty relators: `78` Coxeter relators and two additional
relators. -/
@[simp]
theorem length_fi24AutomorphismRelators : fi24AutomorphismRelators.length = 80 := by
  simp [fi24AutomorphismRelators, fi24AutomorphismAdditionalRelators]
  norm_num [Nat.choose]

/-- The source word `a b c d e f h` has seven letters. -/
@[simp]
theorem length_fi24SourceEquationWord : fi24SourceEquationWord.length = 7 := by
  simp [fi24SourceEquationWord_def]

/-- The source word `d c b a k l d e f g j d h i` has fourteen letters. -/
@[simp]
theorem length_fi24SourceLongWord : fi24SourceLongWord.length = 14 := by
  simp [fi24SourceLongWord_def]

/-- The compiled source equation for `l` has `1 + 9 · 7 = 64` letters. -/
@[simp]
theorem length_fi24SourceEquationRelator : fi24SourceEquationRelator.length = 64 := by
  simp [fi24SourceEquationRelator_def, Relator.div]

/-- The compiled final source relation has `17 · 14 = 238` letters. -/
@[simp]
theorem length_fi24SourceLongRelator : fi24SourceLongRelator.length = 238 := by
  simp [fi24SourceLongRelator_def]

/-- Every source relator has even length, so sending all twelve involutory generators to the
nontrivial element of `C₂` kills every relation. This is the parity check needed before applying
the index-two Reidemeister--Schreier rewrite. -/
theorem even_length_of_mem_fi24AutomorphismRelators :
    ∀ r ∈ fi24AutomorphismRelators, Even r.toWord.length := by
  rintro r hr
  simp only [fi24AutomorphismRelators, List.mem_append] at hr
  rcases hr with hr | hr
  · obtain ⟨i, j, rfl⟩ := mem_coxeterRelators_iff.mp hr
    have hlen :
        (coxeterRelator fi24AutomorphismCoxeterMatrix s(i, j).inf s(i, j).sup).toWord.length =
          fi24AutomorphismCoxeterMatrix s(i, j).inf s(i, j).sup * 2 := by
      simp
    rw [hlen]
    exact even_iff_two_dvd.mpr ⟨_, Nat.mul_comm _ 2⟩
  · simp only [fi24AutomorphismAdditionalRelators, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl
    · rw [Relator.length_toWord, length_fi24SourceEquationRelator]
      exact even_iff_two_dvd.mpr (by norm_num)
    · rw [Relator.length_toWord, length_fi24SourceLongRelator]
      exact even_iff_two_dvd.mpr (by norm_num)

/-! ## Reidemeister--Schreier rewriting -/

/-- The target generator `ax` corresponding to a source generator `x ≠ a`.
The source index drops by one because `a` itself contributes no target generator. -/
def fi24TargetGenerator (i : Fin 12) (_h : i.val ≠ 0) : Fin 11 :=
  ⟨i.val - 1, by omega⟩

/-- The index shift performed by `TauCeti.Sporadic.fi24TargetGenerator`. Since a `Fin 11` is
determined by its value, this equation determines the map. -/
@[simp]
theorem fi24TargetGenerator_val (i : Fin 12) (h : i.val ≠ 0) :
    (fi24TargetGenerator i h).val = i.val - 1 := by
  simp only [fi24TargetGenerator]

/-- Rewrite source letters into the Schreier generators `ab` through `al`.

The Boolean records whether the current transversal representative is `a`. Source signs are
ignored because the source square relations make every generator an involution; inversion has
already reversed the order of letters in `Relator.toWord`. Reading any letter switches the
transversal representative, including the distinguished letter `a`, which contributes no factor.
-/
def fi24SchreierFactors : Bool → PresentationWord (Fin 12) → List (Relator (Fin 11))
  | _, [] => []
  | positive, (i, _) :: w =>
      let rest := fi24SchreierFactors (!positive) w
      if h : i.val = 0 then rest
      else
        let g : Relator (Fin 11) := .gen (fi24TargetGenerator i h)
        (if positive then g else .inv g) :: rest

/-- The empty source word contributes no Schreier factor. -/
@[simp]
theorem fi24SchreierFactors_nil (positive : Bool) :
    fi24SchreierFactors positive [] = [] := by
  simp only [fi24SchreierFactors]

/-- One step of `TauCeti.Sporadic.fi24SchreierFactors`: the letter `a` contributes nothing and any
other letter contributes the Schreier generator it names, inverted exactly when the current
transversal representative is `1`. With `TauCeti.Sporadic.fi24SchreierFactors_nil` this determines
the rewrite of every source word. -/
@[simp]
theorem fi24SchreierFactors_cons (positive : Bool) (i : Fin 12) (sign : Bool)
    (w : PresentationWord (Fin 12)) :
    fi24SchreierFactors positive ((i, sign) :: w) =
      if h : i.val = 0 then fi24SchreierFactors (!positive) w
      else
        (if positive then .gen (fi24TargetGenerator i h)
          else .inv (.gen (fi24TargetGenerator i h))) :: fi24SchreierFactors (!positive) w := by
  simp only [fi24SchreierFactors]

/-- Assemble a possibly empty list of Schreier factors as one relator expression. The zero power
is used only for an empty rewrite, which occurs for the eliminated square relation `a²`; the final
presentation rewrites no square relator. -/
private def relatorOfFactors (factors : List (Relator (Fin 11))) : Relator (Fin 11) :=
  factors.foldr .mul (.pow (.gen 0) 0)

/-- Rewrite a source relator using the transversal representative selected by `positive`.
Starting with `false` rewrites `r`; starting with `true` rewrites `a r a`. -/
def fi24SchreierRewrite (positive : Bool) (r : Relator (Fin 12)) : Relator (Fin 11) :=
  relatorOfFactors (fi24SchreierFactors positive r.toWord)

/-- The rewrite of a source relator is the product of its Schreier factors, the empty product being
the trivial relator. The body is sealed, so this equation is what publishes the rewrite. -/
theorem fi24SchreierRewrite_def (positive : Bool) (r : Relator (Fin 12)) :
    fi24SchreierRewrite positive r =
      (fi24SchreierFactors positive r.toWord).foldr .mul (.pow (.gen 0) 0) := by
  simp only [fi24SchreierRewrite, relatorOfFactors]

/-- The `136` relators of the index-two subgroup. The square relations are omitted after their
standard Tietze elimination of the redundant Schreier generators; the `66` off-diagonal Coxeter
relations and the two additional relations each contribute a rewrite of `r` and of `a r a`. -/
def fi24PrimeRelators : List (Relator (Fin 11)) :=
  (fi24SourcePairRelators ++ fi24AutomorphismAdditionalRelators).flatMap
    fun r => [fi24SchreierRewrite false r, fi24SchreierRewrite true r]

/-- The rewritten relators, spelled out as the two rewrites of each source relator. The body is
sealed, so this equation together with `TauCeti.Sporadic.fi24SchreierRewrite_def`,
`TauCeti.Sporadic.fi24SchreierFactors_cons`, `TauCeti.Sporadic.fi24SourcePairRelators_def` and
`TauCeti.Sporadic.fi24AutomorphismAdditionalRelators_def` determines every relation of the
presentation. -/
theorem fi24PrimeRelators_def :
    fi24PrimeRelators =
      (fi24SourcePairRelators ++ fi24AutomorphismAdditionalRelators).flatMap
        fun r => [fi24SchreierRewrite false r, fi24SchreierRewrite true r] := by
  simp only [fi24PrimeRelators]

/-- The off-diagonal source relations consist of the sixty-six unordered pairs of distinct
generators. -/
@[simp]
theorem length_fi24SourcePairRelators : fi24SourcePairRelators.length = 66 := by decide

/-- The Reidemeister--Schreier presentation has `136` relators. -/
@[simp]
theorem length_fi24PrimeRelators : fi24PrimeRelators.length = 136 := by
  simp [fi24PrimeRelators_def, length_fi24SourcePairRelators,
    fi24AutomorphismAdditionalRelators_def]

/-- Hall--Soicher's finite presentation of the third Fischer 3-transposition group, rewritten by
Reidemeister--Schreier for its commutator subgroup `Fi₂₄'`.

Kim and Michler reproduce the source presentation, prove that its commutator subgroup is the
simple group `Fi₂₄'`, and give the first ten Schreier generators. The retained eleventh
generator `al` makes the rewrite directly traceable to the displayed source relations. No
structural property of the resulting `PresentedGroup` is asserted here. -/
def fi24PrimePresentation : GroupPresentation where
  generatorNames := ["ab", "ac", "ad", "ae", "af", "ag", "ah", "ai", "aj", "ak", "al"]
  source := "H. K. Kim and G. O. Michler, Construction of Fischer's sporadic group Fi24' inside \
    GL_8671(13), Journal of Algebra 322 (2009), 193-233; presentation originally due to J. I. \
    Hall and L. H. Soicher"
  sourceLocator := "Kim--Michler, Lemma 6.2 and Theorem 6.3, \
    doi:10.1016/j.jalgebra.2009.05.003, arXiv:0906.1064; Hall--Soicher, Presentations of some \
    3-transposition groups, Communications in Algebra 23 (1995), 2517-2559, \
    doi:10.1080/00927879508825358"
  generatorConvention := "Source generators are a,b,c,d,e,f,g,h,i,j,k,l. Target indices 0 \
    through 10 denote ab,ac,ad,ae,af,ag,ah,ai,aj,ak,al. All source generators are involutions. \
    With transversal {1,a}, an even-position source letter x rewrites as (a*x)^-1 and an \
    odd-position source letter rewrites as a*x; the source letter a contributes no target letter."
  transcriptionNotes := "Expand the source diagram into 78 Coxeter relators and append its two \
    displayed relations. The twelve square relations eliminate the redundant half of the \
    Schreier generators and then rewrite trivially. Each of the 66 off-diagonal Coxeter relators \
    and each of the two displayed relations contributes its rewrite and the rewrite of its \
    conjugate by a, for 2*(66+2)=136 relators. Retain al rather than eliminating it with the first \
    displayed relation, so every target relator remains a direct rewrite of a source relator. A \
    separate source-to-Lean read-through remains an S1 review obligation."
  expectedGeneratorCount := 11
  expectedRelatorCount := 136
  transcribed := fi24PrimeRelators

/-- The generator names recorded for `Fi₂₄'`. The row's body is sealed, so this is what lets a
consumer see that it is an eleven-generator presentation and what each index names. -/
@[simp]
theorem fi24PrimePresentation_generatorNames :
    fi24PrimePresentation.generatorNames =
      ["ab", "ac", "ad", "ae", "af", "ag", "ah", "ai", "aj", "ak", "al"] := by
  simp only [fi24PrimePresentation]

/-- The source recorded for `Fi₂₄'`. The row's body is sealed, so this equation is what publishes
the citation itself, rather than only the row's name, to a downstream audit. -/
theorem fi24PrimePresentation_source :
    fi24PrimePresentation.source = "H. K. Kim and G. O. Michler, Construction of Fischer's \
      sporadic group Fi24' inside GL_8671(13), Journal of Algebra 322 (2009), 193-233; \
      presentation originally due to J. I. Hall and L. H. Soicher" := by
  simp only [fi24PrimePresentation]

/-- The locator recorded for `Fi₂₄'`, pointing at the presentation inside its source. -/
theorem fi24PrimePresentation_sourceLocator :
    fi24PrimePresentation.sourceLocator = "Kim--Michler, Lemma 6.2 and Theorem 6.3, \
      doi:10.1016/j.jalgebra.2009.05.003, arXiv:0906.1064; Hall--Soicher, Presentations of some \
      3-transposition groups, Communications in Algebra 23 (1995), 2517-2559, \
      doi:10.1080/00927879508825358" := by
  simp only [fi24PrimePresentation]

/-- The generator convention recorded for `Fi₂₄'`, fixing which Schreier generator each relator
index names and how a source letter is rewritten. -/
theorem fi24PrimePresentation_generatorConvention :
    fi24PrimePresentation.generatorConvention = "Source generators are a,b,c,d,e,f,g,h,i,j,k,l. \
      Target indices 0 through 10 denote ab,ac,ad,ae,af,ag,ah,ai,aj,ak,al. All source generators \
      are involutions. With transversal {1,a}, an even-position source letter x rewrites as \
      (a*x)^-1 and an odd-position source letter rewrites as a*x; the source letter a contributes \
      no target letter." := by
  simp only [fi24PrimePresentation]

/-- The transcription notes recorded for `Fi₂₄'`, including the arithmetic behind the relator
count and the outstanding read-through obligation. -/
theorem fi24PrimePresentation_transcriptionNotes :
    fi24PrimePresentation.transcriptionNotes = "Expand the source diagram into 78 Coxeter \
      relators and append its two displayed relations. The twelve square relations eliminate the \
      redundant half of the Schreier generators and then rewrite trivially. Each of the 66 \
      off-diagonal Coxeter relators and each of the two displayed relations contributes its \
      rewrite and the rewrite of its conjugate by a, for 2*(66+2)=136 relators. Retain al rather \
      than eliminating it with the first displayed relation, so every target relator remains a \
      direct rewrite of a source relator. A separate source-to-Lean read-through remains an S1 \
      review obligation." := by
  simp only [fi24PrimePresentation]

/-- The generator count of this row: the ten Schreier generators `ab, …, ak` that Kim--Michler
display, together with the eleventh generator `al` that this transcription retains instead of
eliminating it with the source relation `l = (abcdefh)⁹`. With
`TauCeti.Sporadic.fi24PrimePresentation_generatorNames` this is what makes
`TauCeti.Sporadic.fi24PrimePresentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem fi24PrimePresentation_expectedGeneratorCount :
    fi24PrimePresentation.expectedGeneratorCount = 11 := by
  simp only [fi24PrimePresentation]

/-- The relator count obtained by rewriting each of the `66` off-diagonal Coxeter relators and each
of the two displayed relations twice. -/
@[simp]
theorem fi24PrimePresentation_expectedRelatorCount :
    fi24PrimePresentation.expectedRelatorCount = 136 := by
  simp only [fi24PrimePresentation]

/-- The compiled relator words of the `Fi₂₄'` row are the compiled rewritten relators. A letter
`(i, true)` is the generator with index `i` and `(i, false)` is its inverse, so index `0` reads
`ab` and index `10` reads `al`.

The row's body is sealed, so this is the equation that characterizes what it transcribes. Unlike
the other sporadic rows the `136` words are not spelled out:
`TauCeti.Sporadic.fi24PrimeRelators_def` and the `_def` equations it cites determine every one of
them from the eleven-edge source diagram, which is the form in which the source displays the
presentation. Letters rather than relator expressions are compared because the index type of a
relator depends on the generator-name list while the letters do not. -/
theorem fi24PrimePresentation_relatorLetters :
    fi24PrimePresentation.relatorLetters =
      fi24PrimeRelators.map fun r => r.toWord.map fun letter => (letter.1.val, letter.2) := by
  simp only [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    fi24PrimePresentation, List.map_map, Function.comp_def]
  rfl

/-- The generator and relator counts recorded for `Fi₂₄'` agree with the rewritten data. -/
theorem fi24PrimePresentation_matchesMetadata : fi24PrimePresentation.matchesMetadata := by
  rw [GroupPresentation.matchesMetadata_iff]
  exact ⟨rfl, length_fi24PrimeRelators⟩

end TauCeti.Sporadic
