/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
public import TauCeti.RepresentationTheory.Augmentation
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Basic
public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.DoubleCosetPairing

/-!
# The Steinberg representation of `GL₂(𝔽_q)`

The Borel subgroup `B` of `GL₂(𝔽_q)` has index `q + 1`, and `GL₂` permutes the cosets `GL₂ ⧸ B`
— the points of the projective line. The resulting permutation representation `ℂ[GL₂ ⧸ B]` has the
same character as the principal series `Ind_B^{GL₂}(1 ⊗ 1)` of
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries/Basic.lean` at the boundary value
`α = β = 1`, where it is reducible: it contains the line spanned by the sum of the cosets, on
which `GL₂` acts trivially. The complement of that line is the **Steinberg representation**
`TauCeti.GL2Steinberg`, of dimension `q`.

This file builds it as the augmentation subrepresentation of `ℂ[GL₂ ⧸ B]` — the elements whose
coefficients sum to zero, of `TauCeti/RepresentationTheory/Augmentation.lean` — and computes its
dimension and its character. The character values are the fixed-coset counts less one, and the
Bruhat decomposition then gives the character-theoretic form of irreducibility: the Steinberg
character has norm `1` for the character pairing of
`TauCeti/RepresentationTheory/CharacterTable/Pairing.lean`. Everything proved here is an identity
between characters — irreducibility itself, and the splitting of the boundary principal series as a
representation, are not proved; see the implementation notes.

## Main definitions

* `TauCeti.GL2Steinberg`: the Steinberg representation of `GL₂(𝔽_q)`.
* `TauCeti.GL2SteinbergEquiv`: it carries the augmentation subrepresentation of `ℂ[GL₂ ⧸ B]`, so
  that consumers can read anything about it off that subrepresentation.

## Main statements

* `TauCeti.finrank_GL2Steinberg`: the Steinberg representation has dimension `q`. Its character at
  the identity is that dimension, by Mathlib's `FDRep.char_one`.
* `TauCeti.character_GL2Steinberg`: its character at `g` is the number of cosets of `B` fixed by
  `g`, less one.
* `TauCeti.character_GL2PrincipalSeries_one_one_eq_character_ofMulAction`: the boundary principal
  series `TauCeti.GL2PrincipalSeries F 1 1` has the character of `ℂ[GL₂ ⧸ B]`, whence
  `TauCeti.character_GL2PrincipalSeries_one_one_eq_one_add`: its character is the trivial character
  `1` plus the Steinberg character.
* `TauCeti.characterPairing_GL2Steinberg_self`: the Steinberg character has norm `1`, by
  `TauCeti.characterPairing_ofMulAction_quotient_sub_punit_eq_card_doubleCosetQuotient_sub_one`
  and the two double cosets of the Bruhat decomposition.

## Implementation notes

An object of `FDRep ℂ G` carries a `ℂ`-module in `Type`, while the coset space `GL₂(F) ⧸ B` lies
in the universe of `F`; `TauCeti.GL2Steinberg` therefore transports the carrier down with
`FDRep.ofShrink`, exactly as `TauCeti.indFDRep` does for induced representations, so that the
construction stays universe-polymorphic in `F`. The transport itself is never reasoned about here:
the dimension and the character below go through the generic transfer lemmas
`FDRep.finrank_ofShrink` and `FDRep.character_ofShrink`, and `TauCeti.GL2SteinbergEquiv` — the
comparison equivalence that `FDRep.ofShrinkEquiv` supplies — is public so that consumers can read
off anything else the same way. It is not a restatement they could do without: the body of
`TauCeti.GL2Steinberg` is not exposed, so `FDRep.ofShrinkEquiv` does not elaborate at that type
outside this file.

`TauCeti.characterPairing_GL2Steinberg_self` carries a `[DecidableEq F]` hypothesis, which the
other statements do not. It is used, not decorative: `TauCeti.ClassFunction.characterPairing`
averages over a `Fintype` of the group, and a `Fintype (GL (Fin 2) F)` instance needs decidable
equality on the matrix entries.

The irreducibility of the Steinberg representation is *not* proved here. Norm `1` is the
character-theoretic content of it, and Mathlib's `FDRep.simple_iff_char_is_norm_one` is the
converse of `TauCeti.ClassFunction.characterPairing_ofFDRep_self` that would turn it into
`CategoryTheory.Simple`. That lemma is however stated for a coefficient field and a group *in the
same universe*, so applying it to `FDRep ℂ (GL (Fin 2) F)` would pin `F : Type`, giving up the
universe polymorphism that `TauCeti.GL2Steinberg` and `TauCeti.GL2PrincipalSeries` both keep; it
also needs `IsAlgClosed ℂ`, hence the fundamental theorem of algebra, which nothing else in this
layer imports. Simplicity of the Steinberg constituent is not a roadmap build target either — the
roadmap names `simple_GL2PrincipalSeries_iff`, not a Steinberg counterpart — so it is left out.

## References

* [Character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md),
  Layer 9, "The boundary: linear and Steinberg constituents", whose target `GL2Steinberg` this is.
* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 5.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 5.2.
-/

public section

open Matrix MulAction

namespace TauCeti

open ClassFunction

universe u

variable (F : Type u) [Field F] [Fintype F]

/-! ### The definition and the dimension -/

/-- **The Steinberg representation of `GL₂(𝔽_q)`**: the augmentation subrepresentation of the
permutation representation `ℂ[GL₂ ⧸ B]` on the cosets of the Borel subgroup, that is, the
complement of its invariant line. It has dimension `q`, and `ℂ[GL₂ ⧸ B]` has the character of the
boundary principal series `Ind_B^{GL₂}(1 ⊗ 1)`. -/
noncomputable def GL2Steinberg : FDRep ℂ (GL (Fin 2) F) :=
  FDRep.ofShrink (augmentationSubrepresentation ℂ (GL (Fin 2) F)
    (GL (Fin 2) F ⧸ GL2Borel F)).toRepresentation

/-- **The Steinberg representation carries the augmentation subrepresentation of `ℂ[GL₂ ⧸ B]`.**
Shrinking the carrier to `Type` is a change of model, not of representation, so everything about
`TauCeti.GL2Steinberg` may be read off the augmentation subrepresentation through this
equivalence. -/
noncomputable def GL2SteinbergEquiv : Representation.Equiv (GL2Steinberg F).ρ
    (augmentationSubrepresentation ℂ (GL (Fin 2) F)
      (GL (Fin 2) F ⧸ GL2Borel F)).toRepresentation :=
  FDRep.ofShrinkEquiv _

/-- **The projective line over `𝔽_q` has `q + 1` points**, against a chosen `Fintype` structure on
the coset space. This is `TauCeti.GL2Borel.index_eq` at the `Fintype.card` spelling that the
dimension computation below rewrites with. -/
private theorem fintypeCard_quotient_gl2Borel [Fintype (GL (Fin 2) F ⧸ GL2Borel F)] :
    Fintype.card (GL (Fin 2) F ⧸ GL2Borel F) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, GL2Borel.index_eq]

/-- **The Steinberg representation has dimension `q`**, one less than the `q + 1` points of the
projective line. -/
@[simp]
theorem finrank_GL2Steinberg : Module.finrank ℂ (GL2Steinberg F) = Fintype.card F := by
  let _ : Fintype (GL (Fin 2) F ⧸ GL2Borel F) := Fintype.ofFinite _
  rw [GL2Steinberg, FDRep.finrank_ofShrink, finrank_augmentationSubrepresentation,
    fintypeCard_quotient_gl2Borel]
  omega

/-! ### The character -/

/-- **The Steinberg character counts fixed points on the projective line, less one.** The
permutation character of `ℂ[GL₂ ⧸ B]` is the number of cosets fixed by `g`, and the invariant line
accounts for exactly `1` of it. -/
@[simp]
theorem character_GL2Steinberg (g : GL (Fin 2) F) :
    (GL2Steinberg F).character g
      = (Nat.card {q : GL (Fin 2) F ⧸ GL2Borel F // g • q = q} : ℂ) - 1 := by
  rw [GL2Steinberg, FDRep.character_ofShrink, character_augmentationSubrepresentation,
    char_ofMulAction]

/-! ### The character of the boundary principal series -/

/-- **The boundary principal series has the character of the permutation representation on the
projective line.** At `α = β = 1` the character of `Ind_B^{GL₂}(1 ⊗ 1)` is the character of
`ℂ[GL₂ ⧸ B]`, because inducing the trivial character of `B` is inducing the trivial
representation. The two representations are only shown to have the same character here, not
identified. -/
theorem character_GL2PrincipalSeries_one_one_eq_character_ofMulAction (g : GL (Fin 2) F) :
    (GL2PrincipalSeries F 1 1).character g
      = (Representation.ofMulAction ℂ (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F)).character g := by
  have hchar : (GL2BorelRep F 1 1).character
      = (FDRep.of (Representation.trivial ℂ (GL2Borel F) ℂ)).character := by
    funext b
    rw [character_GL2BorelRep, FDRep.character_of_trivial]
    simp
  rw [GL2PrincipalSeries_def, ← indClassFun_ofFDRep_character, hchar,
    indClassFun_ofFDRep_character, character_indFDRep, FDRep.of_ρ', char_ind_trivial,
    char_ofMulAction]

/-- **The character of the boundary principal series is `1` plus the Steinberg character.** The
`1` is the trivial character, carried by the invariant line of `ℂ[GL₂ ⧸ B]`. This is the
character-theoretic form of the two-constituent splitting; the splitting itself, as an
isomorphism of representations, is not proved here. -/
@[simp]
theorem character_GL2PrincipalSeries_one_one_eq_one_add (g : GL (Fin 2) F) :
    (GL2PrincipalSeries F 1 1).character g = 1 + (GL2Steinberg F).character g := by
  rw [character_GL2PrincipalSeries_one_one_eq_character_ofMulAction, character_GL2Steinberg,
    char_ofMulAction]
  ring

/-! ### The norm of the Steinberg character -/

section Pairing

variable [DecidableEq F]

/-- **The Steinberg character has norm `1`.** This is the character-theoretic form of the
irreducibility of the Steinberg representation; see the implementation notes for what turning it
into `CategoryTheory.Simple` would still need. -/
@[simp]
theorem characterPairing_GL2Steinberg_self :
    characterPairing (ofFDRep (GL2Steinberg F)) (ofFDRep (GL2Steinberg F)) = 1 := by
  -- The Steinberg character is the permutation character of the projective line less the trivial
  -- character, so the generic pairing computation applies: the norm is the number of double
  -- cosets `B \ GL₂ / B` less one, and the Bruhat decomposition makes that number `2`.
  have hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hSt : ofFDRep (GL2Steinberg F) =
      ofCharacter (Representation.ofMulAction ℂ (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F)) -
        ofCharacter (Representation.ofMulAction ℂ (GL (Fin 2) F) PUnit.{u + 1}) := by
    refine Subtype.ext (funext fun g => ?_)
    rw [ofFDRep_apply, character_GL2Steinberg]
    have hval : ((ofCharacter (Representation.ofMulAction ℂ (GL (Fin 2) F)
          (GL (Fin 2) F ⧸ GL2Borel F)) -
        ofCharacter (Representation.ofMulAction ℂ (GL (Fin 2) F) PUnit.{u + 1}) :
          ClassFunction ℂ (GL (Fin 2) F)) : _ → ℂ) g
        = (Representation.ofMulAction ℂ (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F)).character g -
          (Representation.ofMulAction ℂ (GL (Fin 2) F) PUnit.{u + 1}).character g := by
      rw [Submodule.coe_sub, Pi.sub_apply, ofCharacter_apply, ofCharacter_apply]
    rw [hval, char_ofMulAction, char_ofMulAction]
    simp
  rw [hSt, characterPairing_ofMulAction_quotient_sub_punit_eq_card_doubleCosetQuotient_sub_one ℂ
    (GL2Borel F) (GL2Borel F) hG, GL2Borel.card_doubleCosetQuotient_eq_two]
  norm_num

end Pairing

end TauCeti
