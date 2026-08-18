/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter

/-!
# Induction, restriction, and virtual characters

This file records the compatibility of induction and of restriction along a subgroup with the
virtual-character lattice: both send virtual characters to virtual characters, because both send
characters to characters and both are additive.

Together they are the two maps `R(S) → R(G)` and `R(G) → R(S)` on virtual-character lattices whose
interplay -- the projection formula `TauCeti.indClassFun_comp_subtype_mul` -- makes induction a map
of `R(G)`-modules.

## Main definitions

* `TauCeti.ClassFunction.indVirtualCharactersOfSubgroupAddHom`: induction bundled as an additive
  homomorphism between the virtual-character lattices of a subgroup and the ambient group.

## Main statements

* `TauCeti.ClassFunction.ind_ofFDRep_mem_virtualCharacters`: induction takes the character of a
  finite-dimensional subgroup representation to a virtual character of the ambient group.
* `TauCeti.indClassFun_mem_virtualCharacters`: the same for an arbitrary virtual character of the
  subgroup, obtained from the previous statement by additivity.
* `TauCeti.ClassFunction.indVirtualCharactersOfSubgroupAddHom_apply_coe`: forgetting the target
  subtype in the bundled map recovers induction of class functions.
* `TauCeti.comp_subtype_mem_virtualCharacters`: restricting a virtual character of `G` to a
  subgroup gives a virtual character of the subgroup.

## References

This supplies a compatibility needed by the virtual-character and Artin-induction targets of
Layer 6 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **A character induced from a subgroup is a virtual character.**  Inducing the class function of
a finite-dimensional representation gives the class function of the induced representation
(`TauCeti.ClassFunction.ind_ofFDRep`), and a character is a virtual character.  This is deliberately
not a simp lemma: its left-hand side reduces through `ind_ofFDRep` to the existing
`TauCeti.character_mem_virtualCharacters` simp lemma. -/
theorem ind_ofFDRep_mem_virtualCharacters (S : Subgroup G) [S.FiniteIndex] (A : FDRep k S) :
    ((ind S (ofFDRep A) : ClassFunction k G) : G → k) ∈ virtualCharacters k G := by
  rw [ClassFunction.ind_ofFDRep]
  have hcharacter :
      ((ofFDRep (indFDRep (k := k) (G := G) A) : ClassFunction k G) : G → k) =
        (indFDRep (k := k) (G := G) A).character :=
    funext fun g => ofFDRep_apply _ g
  rw [hcharacter]
  exact character_mem_virtualCharacters _

end ClassFunction

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- Restriction of functions along the inclusion of a subgroup, as an additive map.  It is the
vehicle for propagating a property through the additive generation of the virtual-character
lattice, and is not part of the interface: `TauCeti.ClassFunction.comap` is the class-function
form, and the restriction of a plain function is written `fun s : S => f s`. -/
private def compSubtypeAddHom (S : Subgroup G) : (G → k) →+ (S → k) where
  toFun f s := f s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Restriction preserves virtual characters.**  The restriction of a character is the character
of the restricted representation (`TauCeti.character_resFDRep`), and restriction is additive, so
the property propagates through the additive generation of the lattice.

This is the additive half of the statement that restriction `R(G) → R(S)` is a ring homomorphism;
its multiplicativity is the pointwise `TauCeti.mul_mem_virtualCharacters` on each side. -/
theorem comp_subtype_mem_virtualCharacters (S : Subgroup G) {f : G → k}
    (hf : f ∈ virtualCharacters k G) : (fun s : S => f s) ∈ virtualCharacters k S := by
  have hle : virtualCharacters k G ≤ (virtualCharacters k S).comap (compSubtypeAddHom S) := by
    refine virtualCharacters_le fun V => ?_
    have h : compSubtypeAddHom S V.character = (resFDRep S V).character :=
      funext fun s => (character_resFDRep S V s).symm
    rw [AddSubgroup.mem_comap, h]
    exact character_mem_virtualCharacters _
  have hmem := hle hf
  rwa [AddSubgroup.mem_comap] at hmem

/-- **Induction preserves virtual characters.**  A character of the subgroup induces to a character
(`TauCeti.ClassFunction.ind_ofFDRep_mem_virtualCharacters`), and induction is additive, so the
property propagates through the additive generation of the lattice. -/
theorem indClassFun_mem_virtualCharacters (S : Subgroup G) [S.FiniteIndex] {ψ : S → k}
    (hψ : ψ ∈ virtualCharacters k S) : indClassFun S ψ ∈ virtualCharacters k G := by
  have hle : virtualCharacters k S ≤ (virtualCharacters k G).comap (indClassFunAddHom S) := by
    refine virtualCharacters_le fun V => ?_
    rw [AddSubgroup.mem_comap, indClassFunAddHom_apply]
    have hcf : ((ClassFunction.ofFDRep V : ClassFunction k S) : S → k) = V.character :=
      funext (ClassFunction.ofFDRep_apply V)
    have hind : ((ClassFunction.ind S (ClassFunction.ofFDRep V) : ClassFunction k G) : G → k) =
        indClassFun S V.character := by
      funext g
      rw [ClassFunction.ind_apply, hcf]
    rw [← hind]
    exact ClassFunction.ind_ofFDRep_mem_virtualCharacters S V
  have hmem := hle hψ
  rwa [AddSubgroup.mem_comap, indClassFunAddHom_apply] at hmem

namespace ClassFunction

variable (k G) in
/-- Induction from a subgroup, restricted and corestricted to the virtual-character lattices. -/
noncomputable def indVirtualCharactersOfSubgroupAddHom (S : Subgroup G) [S.FiniteIndex] :
    virtualCharacters k S →+ virtualCharacters k G :=
  ((indClassFunAddHom S).comp (virtualCharacters k S).subtype).codRestrict
    (virtualCharacters k G) fun ψ ↦ by
      rw [AddMonoidHom.comp_apply, indClassFunAddHom_apply]
      exact indClassFun_mem_virtualCharacters S ψ.2

/-- Forgetting the target subtype after induction on virtual characters gives `indClassFun`. -/
@[simp]
theorem indVirtualCharactersOfSubgroupAddHom_apply_coe (S : Subgroup G) [S.FiniteIndex]
    (ψ : virtualCharacters k S) :
    (indVirtualCharactersOfSubgroupAddHom k G S ψ : G → k) = indClassFun S ψ := by
  simpa only [indVirtualCharactersOfSubgroupAddHom, AddMonoidHom.codRestrict_apply,
    AddMonoidHom.comp_apply, AddSubgroup.subtype_apply] using
      indClassFunAddHom_apply S (ψ : S → k)

end ClassFunction

end TauCeti
