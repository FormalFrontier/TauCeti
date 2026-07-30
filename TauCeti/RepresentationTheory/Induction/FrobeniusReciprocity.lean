/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.Induction.FiniteDimensional
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.RepresentationTheory.Character

/-!
# Frobenius reciprocity as a character identity

For a finite-index subgroup `S` of a group `G`, Mathlib's adjunction `Rep.indResAdjunction`
identifies `Hom_G(Ind_S^G A, B)` with `Hom_S(A, Res_S B)`.  This file transports that adjunction to
finite-dimensional representations and reads it off as an identity of character scalar products:

`⟨Ind χ, ψ⟩_G = ⟨χ, Res ψ⟩_S`.

## Main definitions

* `TauCeti.resFDRep`: restriction of a finite-dimensional representation to a subgroup.
* `TauCeti.indResFDRepHomEquiv`: Frobenius reciprocity as a `k`-linear equivalence
  `Hom_G(Ind_S^G A, B) ≃ₗ[k] Hom_S(A, Res_S B)`.
* `TauCeti.resIndFDRepHomEquiv`: the second reciprocity
  `Hom_S(Res_S B, A) ≃ₗ[k] Hom_G(B, Ind_S^G A)`, available because induction from a finite-index
  subgroup is a right adjoint to restriction as well as a left one.

## Main statements

* `TauCeti.finrank_hom_indFDRep`, `TauCeti.finrank_hom_resFDRep`: the paired intertwining spaces
  have the same dimension.
* `TauCeti.frobenius_reciprocity`: the character form, with both scalar products written out as
  explicit normalized sums.
* `TauCeti.characterPairing_indFDRep`: the same identity phrased against
  `TauCeti.ClassFunction.characterPairing`.
* `TauCeti.card_inv_mul_sum_character_indFDRep`: reciprocity against the trivial representation,
  which says that induction does not change the (normalized) average of a character.

## Implementation notes

Only the coefficient field and the invertibility of `Nat.card G` are assumed; no algebraic closure
is needed, because each side is computed by Mathlib's
`FDRep.scalar_product_char_eq_finrank_equivariant` rather than by orthogonality of irreducible
characters.  Invertibility of `Nat.card S` is not a separate hypothesis: it follows from
`Subgroup.card_mul_index`.

Both scalar products are stated in the order `⟨Ind χ, ψ⟩`, matching the roadmap.  Mathlib's
`FDRep.scalar_product_char_eq_finrank_equivariant` computes the opposite order, so the proof first
reindexes each sum by `g ↦ g⁻¹`; this is the symmetry of the pairing, recorded for class functions
as `TauCeti.ClassFunction.characterPairing_symm`.

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

section Restriction

/-- Restriction of a finite-dimensional representation of `G` to a subgroup `S`.  This is Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`; this definition only supplies the representation-theoretic
name. -/
@[expose]
def resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- Restriction acts on the representation by precomposing with the inclusion of the subgroup. -/
@[simp]
theorem resFDRep_ρ (S : Subgroup G) (B : FDRep k G) :
    (resFDRep S B).ρ = B.ρ.comp S.subtype :=
  rfl

/-- The character of a restriction is the restriction of the character. -/
@[simp]
theorem character_resFDRep (S : Subgroup G) (B : FDRep k G) (s : S) :
    (resFDRep S B).character s = B.character (s : G) :=
  rfl

/-- Restriction commutes with forgetting finite-dimensionality. -/
theorem forget₂_obj_resFDRep (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (resFDRep S B) =
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  rfl

end Restriction

section HomSpaces

variable {S : Subgroup G}

/-- **Frobenius reciprocity** for finite-dimensional representations, as a `k`-linear equivalence of
intertwining spaces: `Hom_G(Ind_S^G A, B) ≃ₗ[k] Hom_S(A, Res_S B)`.

This is Mathlib's `Rep.indResHomEquiv`, the linear form of the adjunction
`Rep.indResAdjunction`, conjugated by the fully faithful forgetful functor
`FDRep k G ⥤ Rep k G` and by `TauCeti.indFDRepForgetIso`. -/
noncomputable def indResFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
    (indFDRep A ⟶ B) ≃ₗ[k] (A ⟶ resFDRep S B) :=
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
with coinduction; the pair is the finite-dimensional shadow of `Rep.resIndAdjunction`. -/
noncomputable def resIndFDRepHomEquiv [S.FiniteIndex] (A : FDRep k S) (B : FDRep k G) :
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

/-- The scalar product of two functions on a finite group is symmetric: reindexing by `g ↦ g⁻¹`
exchanges the two arguments.  No class-function hypothesis is needed. -/
private theorem sum_mul_inv_comm {Γ : Type*} [Group Γ] [Fintype Γ] (f h : Γ → k) :
    ∑ g : Γ, f g * h g⁻¹ = ∑ g : Γ, h g * f g⁻¹ :=
  (Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => by simp [mul_comm]).symm

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
theorem frobenius_reciprocity [Fintype G] [S.FiniteIndex] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, (indFDRep A).character g * B.character g⁻¹ =
      (Nat.card S : k)⁻¹ * ∑ s : S, A.character s * B.character ((s : G)⁻¹) := by
  letI : Invertible (Nat.card G : k) := hG.invertible
  letI : Invertible (Nat.card S : k) := (isUnit_natCard_subgroup S hG).invertible
  -- The subgroup element `(s : G)⁻¹` is the coercion of `s⁻¹`, so the right-hand sum is already a
  -- scalar product of characters of `S`.
  have hres (s : S) : B.character ((s : G)⁻¹) = (resFDRep S B).character s⁻¹ := rfl
  simp only [hres]
  -- Reindexing each sum by `g ↦ g⁻¹` puts its two factors in the order Mathlib's scalar-product
  -- lemma expects, and each side then becomes the dimension of an intertwining space.
  rw [sum_mul_inv_comm (indFDRep A).character B.character,
    sum_mul_inv_comm A.character (resFDRep S B).character,
    FDRep.scalar_product_char_eq_finrank_equivariant (indFDRep A) B,
    FDRep.scalar_product_char_eq_finrank_equivariant A (resFDRep S B),
    finrank_hom_indFDRep A B]

open scoped Classical in
/-- Frobenius reciprocity, phrased against the normalized pairing of class functions used by the
character-theory development. -/
theorem characterPairing_indFDRep [Fintype G] [S.FiniteIndex] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k S) (B : FDRep k G) :
    ClassFunction.characterPairing (ClassFunction.ofFDRep (indFDRep A))
        (ClassFunction.ofFDRep B) =
      ClassFunction.characterPairing (ClassFunction.ofFDRep A)
        (ClassFunction.ofFDRep (resFDRep S B)) := by
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply]
  simpa using frobenius_reciprocity hG A B

open scoped Classical in
/-- Reciprocity against the trivial representation: the normalized average of an induced character
over `G` is the normalized average of the original character over `S`.  Equivalently, by
`FDRep.average_char_eq_finrank_invariants`, inducing does not change the dimension of the space of
invariants. -/
theorem card_inv_mul_sum_character_indFDRep [Fintype G] [S.FiniteIndex]
    (hG : IsUnit (Nat.card G : k)) (A : FDRep k S) :
    (Nat.card G : k)⁻¹ * ∑ g : G, (indFDRep A).character g =
      (Nat.card S : k)⁻¹ * ∑ s : S, A.character s := by
  have htriv (g : G) : (FDRep.of (Representation.trivial k G k)).character g = 1 := by
    simp [FDRep.character, Representation.trivial]
  simpa [htriv] using frobenius_reciprocity hG A (FDRep.of (Representation.trivial k G k))

end Characters

end TauCeti
