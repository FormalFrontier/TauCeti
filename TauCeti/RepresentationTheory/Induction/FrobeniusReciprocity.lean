/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import TauCeti.RepresentationTheory.Induction.Restriction
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RepresentationTheory.Character

/-!
# Frobenius reciprocity as a character identity

For a finite-index subgroup `S` of a group `G`, Mathlib's adjunction `Rep.indResAdjunction`
identifies `Hom_G(Ind_S^G A, B)` with `Hom_S(A, Res_S B)`.  This file transports that adjunction to
finite-dimensional representations and reads it off as an identity of character scalar products:

`⟨Ind χ, ψ⟩_G = ⟨χ, Res ψ⟩_S`,

together with the identity in the other direction `⟨Res ψ, χ⟩_S = ⟨ψ, Ind χ⟩_G`.

## Main statements

* `TauCeti.finrank_hom_indFDRep`, `TauCeti.finrank_hom_resFDRep`: the paired intertwining spaces
  have the same dimension.
* `TauCeti.frobenius_reciprocity` and `TauCeti.frobenius_reciprocity_resFDRep`: the character form
  in both directions, with all scalar products written out as explicit normalized sums.
* `TauCeti.characterPairing_indFDRep`, `TauCeti.characterPairing_resFDRep`: the same two identities
  phrased against `TauCeti.ClassFunction.characterPairing`.
* `TauCeti.card_inv_mul_sum_character_indFDRep`: reciprocity against the trivial representation,
  which says that induction does not change the (normalized) average of a character.

## Implementation notes

Only the coefficient field and the invertibility of `Nat.card G` are assumed; no algebraic closure
is needed, because each side is computed by
`TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank` rather than by orthogonality of
irreducible characters.  Invertibility of `Nat.card S` is not a separate hypothesis: it follows
from `Subgroup.card_mul_index`.

That pairing-to-dimension lemma computes `⟨χ_V, χ_W⟩` as `finrank k (W ⟶ V)`, exchanging the two
arguments.  So the identity stated in the order `⟨Ind χ, ψ⟩ = ⟨χ, Res ψ⟩` is read off the *second*
reciprocity, `finrank_hom_resFDRep`.  The identity in the order `⟨Res ψ, χ⟩ = ⟨ψ, Ind χ⟩` is then
just that one with both sides flipped, by `TauCeti.ClassFunction.characterPairing_symm`, so it is
derived rather than proved again from `finrank_hom_indFDRep`.  Neither direction needs a reindexing
of the sums.

The two `k`-linear equivalences of intertwining spaces that carry the reciprocities are private:
only their `finrank` corollaries are intended as API, and both are opaque transports whose bodies
would have to be exposed before a consumer could identify the transported intertwiner.

## References

This is the "Frobenius reciprocity as a character identity" item of Layer 2 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`, recorded in its
`Suggested.lean` as `frobenius_reciprocity`.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.2.
* I. M. Isaacs, *Character Theory of Finite Groups*, Lemma 5.2.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G]

section HomSpaces

variable {S : Subgroup G}

/-- **Frobenius reciprocity** for finite-dimensional representations, as a `k`-linear equivalence of
intertwining spaces: `Hom_G(Ind_S^G A, B) ≃ₗ[k] Hom_S(A, Res_S B)`.

This is Mathlib's `Rep.indResHomEquiv`, the linear form of the adjunction
`Rep.indResAdjunction`, conjugated by the fully faithful forgetful functor
`FDRep k G ⥤ Rep k G` and by `TauCeti.indFDRepForgetIso`.

It is private: only `finrank_hom_indFDRep` is intended as API. -/
private noncomputable def indResFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    (indFDRep A ⟶ B) ≃ₗ[k] (A ⟶ resFDRep S B) :=
  -- `resFDRep` is an abbreviation for `Action.res`, so its image under `forget₂` is `Rep.res`
  -- definitionally and the restriction side needs no comparison isomorphism.
  (FDRep.forget₂HomLinearEquiv (indFDRep A) B).symm.trans <|
    ((Linear.homCongr k (indFDRepForgetIso A) (Iso.refl _)).trans
      (Rep.indResHomEquiv S.subtype _ _)).trans
        (FDRep.forget₂HomLinearEquiv A (resFDRep S B))

/-- The intertwining space out of an induced representation has the same dimension as the
intertwining space into the corresponding restriction. This is the quantitative content of
Frobenius reciprocity, and holds over an arbitrary field. -/
theorem finrank_hom_indFDRep [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    Module.finrank k (indFDRep A ⟶ B) = Module.finrank k (A ⟶ resFDRep S B) :=
  (indResFDRepHomEquiv A B).finrank_eq

/-- **The second reciprocity**, available because induction from a finite-index subgroup is also a
*right* adjoint to restriction: `Hom_S(Res_S B, A) ≃ₗ[k] Hom_G(B, Ind_S^G A)`.

Where `TauCeti.indResFDRepHomEquiv` transports Mathlib's `Rep.indResHomEquiv`, this transports
`Rep.resCoindHomEquiv` along Mathlib's finite-index identification `Rep.indCoindIso` of induction
with coinduction; the pair is the finite-dimensional shadow of `Rep.resIndAdjunction`.

It is private: only `finrank_hom_resFDRep` is intended as API. -/
private noncomputable def resIndFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    (resFDRep S B ⟶ A) ≃ₗ[k] (B ⟶ indFDRep A) :=
  -- `Rep.indCoindIso` picks coset representatives, so it wants the coset relation to be decidable.
  letI : DecidableRel ⇑(QuotientGroup.rightRel S) := Classical.decRel _
  (FDRep.forget₂HomLinearEquiv (resFDRep S B) A).symm.trans <|
    (Rep.resCoindHomEquiv S.subtype _ _).trans <|
      (Linear.homCongr k (Iso.refl _)
        ((indFDRepForgetIso A).trans (Rep.indCoindIso _)).symm).trans
          (FDRep.forget₂HomLinearEquiv B (indFDRep A))

/-- The dimension form of the second reciprocity. -/
theorem finrank_hom_resFDRep [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    Module.finrank k (resFDRep S B ⟶ A) = Module.finrank k (B ⟶ indFDRep A) :=
  (resIndFDRepHomEquiv A B).finrank_eq

end HomSpaces

section Characters

variable {S : Subgroup G}

/-- If the order of a finite group is invertible in `k`, then so is the order of any subgroup,
because the two differ by the index. -/
private theorem isUnit_natCard_subgroup [Finite G] (S : Subgroup G)
    (hG : IsUnit (Nat.card G : k)) : IsUnit (Nat.card S : k) := by
  refine isUnit_of_mul_isUnit_left (y := (S.index : k)) ?_
  rwa [← Nat.cast_mul, S.card_mul_index]

open scoped Classical in
/-- **Frobenius reciprocity as a character identity.**  The scalar product over `G` of an induced
character with a character of `G` equals the scalar product over `S` of the original character with
the restricted character.

Both sides are written as explicit normalized sums, so the statement does not depend on the name of
any particular pairing; `TauCeti.characterPairing_indFDRep` is the same identity phrased against
`TauCeti.ClassFunction.characterPairing`.  The hypothesis `hG` is what makes the normalizing factors
meaningful; it also supplies the invertibility of `Nat.card S`. -/
theorem frobenius_reciprocity [Fintype G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, (indFDRep A).character g * B.character g⁻¹ =
      (Nat.card S : k)⁻¹ * ∑ s : S, A.character s * B.character ((s : G)⁻¹) := by
  letI : Invertible (Nat.card G : k) := hG.invertible
  letI : Invertible (Nat.card S : k) := (isUnit_natCard_subgroup S hG).invertible
  calc (Nat.card G : k)⁻¹ * ∑ g : G, (indFDRep A).character g * B.character g⁻¹
      = ClassFunction.characterPairing (ClassFunction.ofFDRep (indFDRep A))
          (ClassFunction.ofFDRep B) := (ClassFunction.characterPairing_ofFDRep _ _).symm
    _ = (Module.finrank k (B ⟶ indFDRep A) : k) :=
        ClassFunction.characterPairing_ofFDRep_eq_finrank _ _
    _ = (Module.finrank k (resFDRep S B ⟶ A) : k) := by rw [finrank_hom_resFDRep]
    _ = ClassFunction.characterPairing (ClassFunction.ofFDRep A)
          (ClassFunction.ofFDRep (resFDRep S B)) :=
        (ClassFunction.characterPairing_ofFDRep_eq_finrank _ _).symm
    _ = (Nat.card S : k)⁻¹ * ∑ s : S, A.character s * (resFDRep S B).character s⁻¹ :=
        ClassFunction.characterPairing_ofFDRep _ _
    _ = (Nat.card S : k)⁻¹ * ∑ s : S, A.character s * B.character ((s : G)⁻¹) := by simp

open scoped Classical in
/-- Frobenius reciprocity, phrased against the normalized pairing of class functions used by the
character-theory development. -/
theorem characterPairing_indFDRep [Fintype G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep (indFDRep A))
        (ClassFunction.ofFDRep B) =
      ClassFunction.characterPairing (ClassFunction.ofFDRep A)
        (ClassFunction.ofFDRep (resFDRep S B)) := by
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply]
  simpa using frobenius_reciprocity hG A B

open scoped Classical in
/-- The reciprocity in the other direction, phrased against
`TauCeti.ClassFunction.characterPairing`.  The pairing is symmetric, so this is
`characterPairing_indFDRep` with both sides flipped. -/
theorem characterPairing_resFDRep [Fintype G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep (resFDRep S B))
        (ClassFunction.ofFDRep A) =
      ClassFunction.characterPairing (ClassFunction.ofFDRep B)
        (ClassFunction.ofFDRep (indFDRep A)) := by
  rw [ClassFunction.characterPairing_symm (ClassFunction.ofFDRep (resFDRep S B)),
    ClassFunction.characterPairing_symm (ClassFunction.ofFDRep B)]
  exact (characterPairing_indFDRep hG A B).symm

open scoped Classical in
/-- **Frobenius reciprocity in the other direction**: the scalar product over `S` of a restricted
character with a character of `S` equals the scalar product over `G` of the original character with
the induced character.  This is `characterPairing_resFDRep` with the pairing unfolded. -/
theorem frobenius_reciprocity_resFDRep [Fintype G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    (Nat.card S : k)⁻¹ * ∑ s : S, B.character (s : G) * A.character s⁻¹ =
      (Nat.card G : k)⁻¹ * ∑ g : G, B.character g * (indFDRep A).character g⁻¹ := by
  have h := characterPairing_resFDRep hG A B
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply] at h
  simpa using h

open scoped Classical in
/-- Reciprocity against the trivial representation: the normalized average of an induced character
over `G` is the normalized average of the original character over `S`.  Equivalently, by
`FDRep.average_char_eq_finrank_invariants`, inducing does not change the dimension of the space of
invariants. -/
theorem card_inv_mul_sum_character_indFDRep [Fintype G]
    (hG : IsUnit (Nat.card G : k)) (A : FDRep k S) :
    (Nat.card G : k)⁻¹ * ∑ g : G, (indFDRep A).character g =
      (Nat.card S : k)⁻¹ * ∑ s : S, A.character s := by
  have htriv (g : G) : (FDRep.of (Representation.trivial k G k)).character g = 1 := by
    simp [FDRep.character, Representation.trivial]
  simpa [htriv] using frobenius_reciprocity hG A (FDRep.of (Representation.trivial k G k))

end Characters

end TauCeti
