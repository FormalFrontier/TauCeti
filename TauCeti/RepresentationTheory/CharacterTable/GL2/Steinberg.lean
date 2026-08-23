/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Bruhat
public import TauCeti.RepresentationTheory.Augmentation
public import TauCeti.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Induction.DoubleCosetPairing

/-!
# The Steinberg representation of `GL₂(𝔽_q)`

The Borel subgroup `B` of `GL₂(𝔽_q)` has index `q + 1`, and `GL₂` permutes the cosets `GL₂ ⧸ B`
— the points of the projective line. The resulting permutation representation `ℂ[GL₂ ⧸ B]` is the
principal series `Ind_B^{GL₂}(1 ⊗ 1)` of
`TauCeti/RepresentationTheory/CharacterTable/GL2/PrincipalSeries.lean` at the boundary value
`α = β = 1`, where it is reducible: it contains the line spanned by the sum of the cosets, on
which `GL₂` acts trivially. The complement of that line is the **Steinberg representation**
`TauCeti.GL2Steinberg`, of dimension `q`.

This file builds it as the augmentation subrepresentation of `ℂ[GL₂ ⧸ B]` — the elements whose
coefficients sum to zero, of `TauCeti/RepresentationTheory/Augmentation.lean` — and computes its
dimension and its character. The character values are the fixed-coset counts less one, and the
Bruhat decomposition then gives the identity that makes Steinberg a single irreducible constituent
rather than several: its character has norm `1` for the character pairing of
`TauCeti/RepresentationTheory/CharacterTable/Pairing.lean`.

## Main definitions

* `TauCeti.GL2Steinberg`: the Steinberg representation of `GL₂(𝔽_q)`.

## Main statements

* `TauCeti.finrank_GL2Steinberg`: the Steinberg representation has dimension `q`. Its character at
  the identity is that dimension, by Mathlib's `FDRep.char_one`.
* `TauCeti.character_GL2Steinberg`: its character at `g` is the number of cosets of `B` fixed by
  `g`, less one.
* `TauCeti.character_ofMulAction_quotient_gl2Borel`: the character of `ℂ[GL₂ ⧸ B]` is `1` plus the
  Steinberg character, so the boundary principal series has the trivial representation and
  Steinberg as its two constituents.
* `TauCeti.characterPairing_GL2Steinberg_self`: the Steinberg character has norm `1`, computed
  from the two double cosets of the Bruhat decomposition.

## Implementation notes

An object of `FDRep ℂ G` carries a `ℂ`-module in `Type`, while the coset space `GL₂(F) ⧸ B` lies
in the universe of `F`; `TauCeti.GL2Steinberg` therefore transports the carrier down with
`FDRep.ofShrink`, exactly as `TauCeti.indFDRep` does for induced representations, so that the
construction stays universe-polymorphic in `F`. Nothing below unfolds that transport: the
dimension and the character pass through it by `FDRep.finrank_ofShrink` and
`FDRep.character_ofShrink`.

`TauCeti.characterPairing_GL2Steinberg_self` carries a `[DecidableEq F]` hypothesis, which the
other statements do not. It is used, not decorative: `TauCeti.ClassFunction.characterPairing`
averages over a `Fintype` of the group, and a `Fintype (GL (Fin 2) F)` instance needs decidable
equality on the matrix entries.

The irreducibility of the Steinberg representation is *not* proved here. Norm `1` is the
character-theoretic content of it, but concluding `CategoryTheory.Simple` from it needs the
converse of `TauCeti.ClassFunction.characterPairing_ofFDRep_self` — that a genuine character of
norm `1` is irreducible — which the repository does not yet have.

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
complement of the trivial constituent in the boundary principal series `Ind_B^{GL₂}(1 ⊗ 1)`. It
has dimension `q`. -/
noncomputable def GL2Steinberg : FDRep ℂ (GL (Fin 2) F) :=
  FDRep.ofShrink (augmentationSubrepresentation ℂ (GL (Fin 2) F)
    (GL (Fin 2) F ⧸ GL2Borel F)).toRepresentation

/-- **The projective line over `𝔽_q` has `q + 1` points.**  This is `TauCeti.GL2Borel.index_eq` at
the coset-space spelling of `Subgroup.index`, which is the spelling the dimension and character
computations below rewrite with. It is deliberately not a `simp` lemma: with a `Fintype` structure
on the coset space in scope, `Nat.card_eq_fintype_card` rewrites its left-hand side to
`Fintype.card`, so the `Nat.card` spelling is not in simp-normal form. -/
theorem natCard_quotient_gl2Borel :
    Nat.card (GL (Fin 2) F ⧸ GL2Borel F) = Fintype.card F + 1 :=
  GL2Borel.index_eq F

/-- `TauCeti.natCard_quotient_gl2Borel` against a chosen `Fintype` structure on the coset space. -/
private theorem fintypeCard_quotient_gl2Borel [Fintype (GL (Fin 2) F ⧸ GL2Borel F)] :
    Fintype.card (GL (Fin 2) F ⧸ GL2Borel F) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card, natCard_quotient_gl2Borel]

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
theorem character_GL2Steinberg (g : GL (Fin 2) F) :
    (GL2Steinberg F).character g
      = (Nat.card {q : GL (Fin 2) F ⧸ GL2Borel F // g • q = q} : ℂ) - 1 := by
  let _ : Fintype (GL (Fin 2) F ⧸ GL2Borel F) := Fintype.ofFinite _
  have hne : ((Fintype.card (GL (Fin 2) F ⧸ GL2Borel F) : ℂ)) ≠ 0 := by
    rw [fintypeCard_quotient_gl2Borel]
    exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [GL2Steinberg, FDRep.character_ofShrink, character_augmentationSubrepresentation hne,
    char_ofMulAction]

/-! ### The splitting of the boundary principal series -/

/-- **The permutation representation on the projective line splits off the trivial one.** Its
character is `1` plus the Steinberg character, the `1` being the invariant line: the boundary
principal series `Ind_B^{GL₂}(1 ⊗ 1)` has the trivial representation and Steinberg as its two
constituents. -/
theorem character_ofMulAction_quotient_gl2Borel (g : GL (Fin 2) F) :
    (Representation.ofMulAction ℂ (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F)).character g
      = 1 + (GL2Steinberg F).character g := by
  rw [character_GL2Steinberg, char_ofMulAction]
  ring

/-! ### The norm of the Steinberg character -/

section Pairing

variable [DecidableEq F]

/-- A pretransitive action on a nonempty type has one orbit. This is Mathlib's
`MulAction.pretransitive_iff_unique_quotient_of_nonempty` in counting form, named because the
pairing computation below uses it four times, at four different actions. -/
private theorem card_orbitQuotient_eq_one (G α : Type*) [Group G] [MulAction G α] [Nonempty α]
    [IsPretransitive G α] : Nat.card (orbitRel.Quotient G α) = 1 :=
  let _ := ((MulAction.pretransitive_iff_unique_quotient_of_nonempty G α).mp ‹_›).some
  Nat.card_unique

/-- Pairing a pretransitive action with a one-point one leaves it pretransitive. -/
private theorem isPretransitive_prod_left (G α β : Type*) [Group G] [MulAction G α]
    [MulAction G β] [IsPretransitive G α] [Subsingleton β] : IsPretransitive G (α × β) :=
  ⟨fun p q => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G p.1 q.1
    exact ⟨g, Prod.ext hg (Subsingleton.elim _ _)⟩⟩

/-- The mirror of `isPretransitive_prod_left`, with the one-point factor first. -/
private theorem isPretransitive_prod_right (G α β : Type*) [Group G] [MulAction G α]
    [MulAction G β] [Subsingleton α] [IsPretransitive G β] : IsPretransitive G (α × β) :=
  ⟨fun p q => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G p.2 q.2
    exact ⟨g, Prod.ext (Subsingleton.elim _ _) hg⟩⟩

/-- **The Steinberg character has norm `1`.** Writing it as the permutation character of the
projective line less the trivial character, the pairing expands into four Burnside orbit counts:
the permutation character pairs with itself to the number `2` of double cosets `B \ GL₂ / B`, the
Bruhat decomposition, and the three remaining terms are `1` each because `GL₂` is transitive on
the projective line.  So `⟨χ_St, χ_St⟩ = 2 - 1 - 1 + 1 = 1`.

This is the character-theoretic form of the irreducibility of the Steinberg representation; see the
implementation notes for what turning it into `CategoryTheory.Simple` would still need. -/
theorem characterPairing_GL2Steinberg_self :
    characterPairing (ofFDRep (GL2Steinberg F)) (ofFDRep (GL2Steinberg F)) = 1 := by
  have hG : IsUnit (Nat.card (GL (Fin 2) F) : ℂ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set perm := Representation.ofMulAction ℂ (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F) with hperm
  set pt := Representation.ofMulAction ℂ (GL (Fin 2) F) PUnit.{u + 1} with hpt
  -- the Steinberg character is the permutation character less the trivial one
  have hSt : ofFDRep (GL2Steinberg F) = ofCharacter perm - ofCharacter pt := by
    refine Subtype.ext (funext fun g => ?_)
    rw [ofFDRep_apply, character_GL2Steinberg]
    have hval : ((ofCharacter perm - ofCharacter pt : ClassFunction ℂ (GL (Fin 2) F)) : _ → ℂ) g
        = perm.character g - pt.character g := by
      rw [Submodule.coe_sub, Pi.sub_apply, ofCharacter_apply, ofCharacter_apply]
    rw [hval, hperm, hpt, char_ofMulAction, char_ofMulAction]
    simp
  have hpp : characterPairing (ofCharacter perm) (ofCharacter perm) = 2 := by
    rw [hperm, characterPairing_ofMulAction_quotient_eq_card_doubleCosetQuotient ℂ
      (GL2Borel F) (GL2Borel F) hG, GL2Borel.card_doubleCosetQuotient_eq_two]
    norm_num
  have hpq : characterPairing (ofCharacter perm) (ofCharacter pt) = 1 := by
    have := isPretransitive_prod_left (GL (Fin 2) F) (GL (Fin 2) F ⧸ GL2Borel F) PUnit.{u + 1}
    rw [hperm, hpt, characterPairing_ofMulAction_eq_card_orbits ℂ _ _ hG,
      card_orbitQuotient_eq_one]
    norm_num
  have hqp : characterPairing (ofCharacter pt) (ofCharacter perm) = 1 := by
    have := isPretransitive_prod_right (GL (Fin 2) F) PUnit.{u + 1} (GL (Fin 2) F ⧸ GL2Borel F)
    rw [hperm, hpt, characterPairing_ofMulAction_eq_card_orbits ℂ _ _ hG,
      card_orbitQuotient_eq_one]
    norm_num
  have hqq : characterPairing (ofCharacter pt) (ofCharacter pt) = 1 := by
    have := isPretransitive_prod_left (GL (Fin 2) F) PUnit.{u + 1} PUnit.{u + 1}
    rw [hpt, characterPairing_ofMulAction_eq_card_orbits ℂ _ _ hG, card_orbitQuotient_eq_one]
    norm_num
  rw [hSt]
  simp only [map_sub, LinearMap.sub_apply]
  rw [hpp, hpq, hqp, hqq]
  ring

end Pairing

end TauCeti
