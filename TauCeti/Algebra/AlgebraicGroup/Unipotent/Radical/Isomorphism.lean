/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction

/-!
# Isomorphism invariance of the unipotent radical

An isomorphism of finite-type commutative Hopf algebras carries connected normal smooth
unipotent closed subgroups to such subgroups. Consequently it carries the greatest one to the
greatest one: the defining Hopf ideal of the unipotent radical pulls back to the defining ideal
of the source radical.

This file packages that equality as an isomorphism between the coordinate Hopf algebras of the
two unipotent radicals. The isomorphism commutes with their coordinate quotient maps, which
characterizes it uniquely and makes identity and composition functoriality available without
unfolding the chosen defining ideals.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.comapOfIso`: transport a radical candidate
  across an ambient isomorphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.comapOfSurjective_unipotentRadicalDefiningIdeal`: the defining
  ideal of the unipotent radical is invariant under isomorphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalIsoOfIso`: the induced isomorphism of
  unipotent radicals.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

The formal organization follows the existing center-isomorphism interface in
`TauCeti.Algebra.AlgebraicGroup.Center.Isomorphism`.

This completes the isomorphism-invariance interface of the unipotent-radical construction in
Layer 5 of the ReductiveGroups roadmap. It lets the Layer 6 structure theory use the radical
independently of a chosen coordinate presentation.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable {I : HopfIdeal k K}

/-- Pulling a unipotent-radical candidate back across an ambient isomorphism gives a
unipotent-radical candidate in the source. -/
theorem comapOfIso (hI : IsUnipotentRadicalCandidate K I) (e : H ≅ K) :
    IsUnipotentRadicalCandidate H
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let qIso := FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I
  refine .mk
    (hI.isNormal.comapOfSurjective_of_bijective
      (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom).1
      (ConcreteCategory.bijective_of_isIso e.hom).2) ?_ ?_
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
        (_root_.CommHopfAlgCat.{u} k)).mapIso qIso.symm) hI.geometricallyConnected
  · exact (smoothUnipotentCommHopfAlgProperty k).prop_of_iso qIso.symm hI.smoothUnipotent

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]
variable {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- An ambient isomorphism pulls the defining ideal of the target's unipotent radical back to
the defining ideal of the source's unipotent radical. -/
@[simp]
theorem comapOfSurjective_unipotentRadicalDefiningIdeal (e : H ≅ K) :
    (unipotentRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      unipotentRadicalDefiningIdeal H := by
  let pulled := (unipotentRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpulled : HopfIdeal.IsUnipotentRadicalCandidate H pulled :=
    (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal K).comapOfIso e
  apply le_antisymm
  · let sourcePulled := (unipotentRadicalDefiningIdeal H).comapOfSurjective
      (toBialgHom e.inv) (ConcreteCategory.bijective_of_isIso e.inv).2
    have hsourcePulled : HopfIdeal.IsUnipotentRadicalCandidate K sourcePulled :=
      (isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal H).comapOfIso e.symm
    have hle : unipotentRadicalDefiningIdeal K ≤ sourcePulled :=
      unipotentRadicalDefiningIdeal_le K sourcePulled hsourcePulled
    intro x hx
    have hx' := hle (HopfIdeal.mem_comapOfSurjective.mp hx)
    have hx'' := HopfIdeal.mem_comapOfSurjective.mp hx'
    have hcancel : (toBialgHom e.inv) ((toBialgHom e.hom) x) = x := by
      have h := congrArg (fun f : H ⟶ H => toBialgHom f x) e.hom_inv_id
      simpa only [toBialgHom_comp, BialgHom.comp_apply, toBialgHom_id,
        BialgHom.coe_id, id_eq] using h
    rw [hcancel] at hx''
    exact hx''
  · exact unipotentRadicalDefiningIdeal_le H pulled hpulled

/-- An isomorphism of finite-type commutative Hopf algebras induces an isomorphism of their
unipotent radicals. -/
noncomputable def unipotentRadicalIsoOfIso (e : H ≅ K) :
    unipotentRadical H ≅ unipotentRadical K :=
  eqToIso (congrArg (quotient H)
    (comapOfSurjective_unipotentRadicalDefiningIdeal e).symm) ≪≫
    quotientIsoOfIso e (unipotentRadicalDefiningIdeal K)

/-- The isomorphism of unipotent radicals commutes with the coordinate quotient maps. -/
@[simp]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom (e : H ≅ K) :
    unipotentRadicalCoordinateMap H ≫ (unipotentRadicalIsoOfIso e).hom =
      e.hom ≫ unipotentRadicalCoordinateMap K := by
  rw [unipotentRadicalIsoOfIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    unipotentRadicalCoordinateMap_def H, unipotentRadicalCoordinateMap_def K,
    mkQuotient_comp_eqToHom,
    mkQuotient_comp_quotientIsoOfIso_hom]
  exact comapOfSurjective_unipotentRadicalDefiningIdeal e

/-- The inverse isomorphism of unipotent radicals commutes with the coordinate quotient maps. -/
@[simp]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_inv (e : H ≅ K) :
    unipotentRadicalCoordinateMap K ≫ (unipotentRadicalIsoOfIso e).inv =
      e.inv ≫ unipotentRadicalCoordinateMap H := by
  rw [← cancel_mono (unipotentRadicalIsoOfIso e).hom]
  simp

/-- A morphism out of a unipotent radical is determined by its composite with the coordinate
quotient map. -/
@[ext]
theorem unipotentRadical_hom_ext {X : FiniteTypeCommHopfAlgCat.{u, u} k}
    {f g : unipotentRadical H ⟶ X}
    (h : unipotentRadicalCoordinateMap H ≫ f = unipotentRadicalCoordinateMap H ≫ g) :
    f = g := by
  rw [unipotentRadicalCoordinateMap_def] at h
  exact mkQuotient_hom_ext h

/-- The isomorphism induced by the identity isomorphism is the identity on the unipotent
radical. -/
@[simp]
theorem unipotentRadicalIsoOfIso_refl :
    unipotentRadicalIsoOfIso (Iso.refl H) = Iso.refl (unipotentRadical H) := by
  apply Iso.ext
  apply unipotentRadical_hom_ext
  rw [unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom]
  rfl

/-- Isomorphisms induced on unipotent radicals respect composition. -/
@[simp]
theorem unipotentRadicalIsoOfIso_trans (e : H ≅ K) (f : K ≅ L) :
    unipotentRadicalIsoOfIso (e ≪≫ f) =
      unipotentRadicalIsoOfIso e ≪≫ unipotentRadicalIsoOfIso f := by
  apply Iso.ext
  apply unipotentRadical_hom_ext
  rw [unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom]
  simp only [Iso.trans_hom]
  conv_rhs =>
    rw [← Category.assoc,
      unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom,
      Category.assoc,
      unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom]
  simp

/-- The inverse of the isomorphism induced on unipotent radicals is the isomorphism induced by
the inverse ambient isomorphism. -/
@[simp]
theorem unipotentRadicalIsoOfIso_symm (e : H ≅ K) :
    (unipotentRadicalIsoOfIso e).symm = unipotentRadicalIsoOfIso e.symm := by
  apply Iso.ext
  apply unipotentRadical_hom_ext
  rw [Iso.symm_hom,
    unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_inv,
    unipotentRadicalCoordinateMap_comp_unipotentRadicalIsoOfIso_hom]
  rfl

end FiniteTypeCommHopfAlgCat

end

end TauCeti
