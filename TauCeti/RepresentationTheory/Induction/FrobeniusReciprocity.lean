/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Index
public import TauCeti.RepresentationTheory.CharacterTable.Pairing
public import TauCeti.RepresentationTheory.Induction.ClassFunction
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

The same identity holds for arbitrary class functions, with `TauCeti.indClassFun` in place of the
induced character and `TauCeti.ClassFunction.comap` in place of restriction.  That version is
proved here too, but by a double count over `G × G` rather than by the adjunction: no
representation is involved, so it also covers class functions that are not characters.

## Main statements

* `TauCeti.finrank_hom_indFDRep`, `TauCeti.finrank_hom_resFDRep`: the paired intertwining spaces
  have the same dimension.
* `TauCeti.frobenius_reciprocity` and `TauCeti.frobenius_reciprocity_resFDRep`: the character form
  in both directions, with all scalar products written out as explicit normalized sums.
* `TauCeti.characterPairing_indFDRep`, `TauCeti.characterPairing_resFDRep`: the same two identities
  phrased against `TauCeti.ClassFunction.characterPairing`.
* `TauCeti.card_inv_mul_sum_character_indFDRep`: reciprocity against the trivial representation,
  which says that induction does not change the (normalized) average of a character.
* `TauCeti.frobenius_reciprocity_classFunction` and `TauCeti.characterPairing_ind`: the class
  function form, `⟨Ind f, h⟩_G = ⟨f, Res h⟩_S`, for arbitrary class functions `f` on `S` and `h`
  on `G`.  `TauCeti.frobenius_reciprocity` is its special case for two characters, but is not
  derived from it: it is what the earlier layers of the roadmap are stated against.

## Implementation notes

Only the coefficient field and the invertibility of `Nat.card G` are assumed; no algebraic closure
is needed, because each side is computed by
`TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank` rather than by orthogonality of
irreducible characters.  Invertibility of `Nat.card S` is not a separate hypothesis: it follows
from `Subgroup.card_mul_index`, via `TauCeti.isUnit_natCard_subgroup`.

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
`Suggested.lean` as `frobenius_reciprocity`.  The class function form belongs to the `indClassFun`
bullet of Layer 6 of the same roadmap.

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.2.
* I. M. Isaacs, *Character Theory of Finite Groups*, Lemma 5.2.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v

section HomSpaces

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G}

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

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G}

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
  let : Invertible (Nat.card G : k) := hG.invertible
  let : Invertible (Nat.card S : k) := (isUnit_natCard_subgroup S hG).invertible
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

section ClassFunctions

variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}

/-! Both steps of the double count are cleared-denominator identities, so they live at the
semiring level alongside `TauCeti.natCard_mul_indClassFun`; only the normalized statements below
divide, and only those need a field. -/

section Semiring

variable [Semiring k]

open scoped Classical in
/-- **The inner sum of the double count.** For a fixed conjugating element `x`, pairing the
conjugation summand `TauCeti.indTerm` against a class function of `G` over all of `G` already gives
the pairing over the subgroup, with no dependence on `x` left.

Reindexing by `y ↦ x y x⁻¹` turns the summand into the plain membership case split, and the sum
then collapses onto `S` because the case split vanishes off it. Only `h` need be a class function;
`f` is arbitrary. -/
private theorem sum_indTerm_mul_eq_sum_subtype [Fintype G] (f : S → k) {h : G → k}
    (hh : h ∈ ClassFunction k G) (x : G) :
    (∑ g : G, indTerm f g x * h g⁻¹) = ∑ s : S, f s * h ((s : G)⁻¹) := by
  have hinv (y : G) : (x * y * x⁻¹)⁻¹ = x * y⁻¹ * x⁻¹ := by group
  calc (∑ g : G, indTerm f g x * h g⁻¹)
      = ∑ y : G, indTerm f (x * y * x⁻¹) x * h (x * y * x⁻¹)⁻¹ := by
        refine (Fintype.sum_equiv ((Equiv.mulRight x⁻¹).trans (Equiv.mulLeft x)) _ _ ?_).symm
        intro y
        simp [mul_assoc]
    _ = ∑ y : G, (if hy : y ∈ S then f ⟨y, hy⟩ else 0) * h y⁻¹ := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [indTerm_conj, inv_mul_cancel, indTerm_one]
        congr 1
        rw [hinv y]
        exact ClassFunction.mem_iff.mp hh y⁻¹ x
    _ = ∑ y ∈ Finset.univ.filter (fun y : G => y ∈ S),
          (if hy : y ∈ S then f ⟨y, hy⟩ else 0) * h y⁻¹ := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun y _ hy => ?_).symm
        rw [Finset.mem_filter] at hy
        rw [dite_eq_right fun hy' => hy ⟨Finset.mem_univ y, hy'⟩, zero_mul]
    _ = ∑ s : S, (if hy : (s : G) ∈ S then f ⟨(s : G), hy⟩ else 0) * h (s : G)⁻¹ :=
        Finset.sum_subtype (p := fun y : G => y ∈ S) _ (by simp) _
    _ = ∑ s : S, f s * h ((s : G)⁻¹) :=
        Finset.sum_congr rfl fun s _ => by rw [dite_eq_left s.2]

open scoped Classical in
/-- **The double count, in cleared-denominator form.** Summing the induced class function against a
class function of `G` over the group, then unfolding the induction into a sum over conjugating
elements and exchanging the two sums, replaces the outer sum by `|G|` copies of the pairing over
`S`. -/
private theorem natCard_mul_sum_indClassFun_mul [Fintype G] {f : S → k}
    (hf : f ∈ ClassFunction k S) {h : G → k} (hh : h ∈ ClassFunction k G) :
    (Nat.card S : k) * ∑ g : G, indClassFun S f g * h g⁻¹
      = (Nat.card G : k) * ∑ s : S, f s * h ((s : G)⁻¹) :=
  calc (Nat.card S : k) * ∑ g : G, indClassFun S f g * h g⁻¹
      = ∑ g : G, ((Nat.card S : k) * indClassFun S f g) * h g⁻¹ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun g _ => (mul_assoc _ _ _).symm
    _ = ∑ g : G, (∑ x : G, indTerm f g x) * h g⁻¹ := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [natCard_mul_indClassFun hf g]
        simp only [indTerm_apply]
    _ = ∑ x : G, ∑ g : G, indTerm f g x * h g⁻¹ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun g _ => by rw [Finset.sum_mul]
    _ = ∑ _x : G, ∑ s : S, f s * h ((s : G)⁻¹) :=
        Finset.sum_congr rfl fun x _ => sum_indTerm_mul_eq_sum_subtype f hh x
    _ = (Nat.card G : k) * ∑ s : S, f s * h ((s : G)⁻¹) := by
        simp [Nat.card_eq_fintype_card]

end Semiring

variable [Field k]

open scoped Classical in
/-- **Frobenius reciprocity for class functions.**  The normalized pairing over `G` of an induced
class function with a class function of `G` is the normalized pairing over `S` of the original
class function with the restricted one.

Both sides are written as explicit normalized sums, so the statement does not depend on the name of
any particular pairing; `TauCeti.characterPairing_ind` is the same identity phrased against
`TauCeti.ClassFunction.characterPairing`.  Specialized to two characters this is
`TauCeti.frobenius_reciprocity`, but no representation is involved here: the identity is a
double count over `G × G` and holds for arbitrary class functions. -/
theorem frobenius_reciprocity_classFunction [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k S) (h : ClassFunction k G) :
    (Nat.card G : k)⁻¹ * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹ =
      (Nat.card S : k)⁻¹ * ∑ s : S, f.1 s * h.1 ((s : G)⁻¹) := by
  have hS : IsUnit (Nat.card S : k) := isUnit_natCard_subgroup S hG
  set X : k := ∑ s : S, f.1 s * h.1 ((s : G)⁻¹) with hX
  refine mul_left_cancel₀ hS.ne_zero ?_
  calc (Nat.card S : k) * ((Nat.card G : k)⁻¹ * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹)
      = (Nat.card G : k)⁻¹ * ((Nat.card S : k) * ∑ g : G, indClassFun S f.1 g * h.1 g⁻¹) := by
        ring
    _ = (Nat.card G : k)⁻¹ * ((Nat.card G : k) * X) := by
        rw [hX, natCard_mul_sum_indClassFun_mul f.2 h.2]
    _ = X := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne_zero, one_mul]
    _ = (Nat.card S : k) * ((Nat.card S : k)⁻¹ * X) := by
        rw [← mul_assoc, mul_inv_cancel₀ hS.ne_zero, one_mul]

open scoped Classical in
/-- Frobenius reciprocity for class functions, phrased against the normalized pairing
`TauCeti.ClassFunction.characterPairing`. -/
theorem characterPairing_ind [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k S) (h : ClassFunction k G) :
    ClassFunction.characterPairing (ClassFunction.ind S f) h =
      ClassFunction.characterPairing f (ClassFunction.comap S.subtype h) := by
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply]
  simpa only [ClassFunction.ind_apply, ClassFunction.comap_apply, Subgroup.coe_subtype,
    Subgroup.coe_inv] using frobenius_reciprocity_classFunction hG f h

end ClassFunctions

end TauCeti
