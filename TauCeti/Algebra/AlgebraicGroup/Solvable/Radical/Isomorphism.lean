/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction

/-!
# Isomorphism invariance of the solvable radical

An isomorphism of finite-type commutative Hopf algebras carries connected normal smooth
solvable closed subgroups to such subgroups. Consequently it carries the greatest one to the
greatest one: the defining Hopf ideal of the solvable radical pulls back to the defining ideal
of the source radical.

This file packages that equality as an isomorphism between the coordinate Hopf algebras of the
two solvable radicals. The isomorphism commutes with their coordinate quotient maps, which
characterizes it uniquely and gives its identity, composition, and inverse laws.

## Main declarations

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.comapOfIso`: transport a radical candidate
  across an ambient isomorphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.comapOfSurjective_solvableRadicalDefiningIdeal`: the defining
  ideal of the solvable radical is invariant under isomorphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalIsoOfIso`: the induced isomorphism of
  solvable radicals.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 6.45--6.46.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

The formal organization follows
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism`.

This supplies the isomorphism-invariance interface for the solvable radical required by Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap. It lets the subsequent
structure theory use the radical independently of a chosen coordinate presentation.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k : Type u} [Field k]
variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
variable {I : HopfIdeal k K}

/-- Pulling a solvable-radical candidate back across an ambient isomorphism gives a
solvable-radical candidate in the source. -/
theorem comapOfIso (hI : IsSolvableRadicalCandidate K I) (e : H ≅ K) :
    IsSolvableRadicalCandidate H
      (I.comapOfSurjective (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let qIso := FiniteTypeCommHopfAlgCat.quotientIsoOfIso e I
  let qIso' := (forget₂ (FiniteTypeCommHopfAlgCat.{u, u} k)
    (_root_.CommHopfAlgCat.{u} k)).mapIso qIso.symm
  refine .mk
    (hI.isNormal.comapOfSurjective_of_bijective
      (FiniteTypeCommHopfAlgCat.toBialgHom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom).1
      (ConcreteCategory.bijective_of_isIso e.hom).2) ?_ ?_ ?_
  · exact (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
      qIso' hI.geometricallyConnected
  · exact (smoothCommHopfAlgProperty_iff _).mp <|
      (smoothCommHopfAlgProperty k).prop_of_iso
        qIso'
        ((smoothCommHopfAlgProperty_iff _).mpr hI.smooth)
  · exact (geometricallySolvablePointsCommHopfAlgProperty k).prop_of_iso
      qIso' hI.geometricallySolvable

end HopfIdeal.IsSolvableRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]
variable {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- An ambient isomorphism pulls the defining ideal of the target's solvable radical back to
the defining ideal of the source's solvable radical. -/
@[simp]
theorem comapOfSurjective_solvableRadicalDefiningIdeal (e : H ≅ K) :
    (solvableRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      solvableRadicalDefiningIdeal H := by
  let pulled := (solvableRadicalDefiningIdeal K).comapOfSurjective (toBialgHom e.hom)
    (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpulled : HopfIdeal.IsSolvableRadicalCandidate H pulled :=
    (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal K).comapOfIso e
  apply le_antisymm
  · let sourcePulled := (solvableRadicalDefiningIdeal H).comapOfSurjective
      (toBialgHom e.inv) (ConcreteCategory.bijective_of_isIso e.inv).2
    have hsourcePulled : HopfIdeal.IsSolvableRadicalCandidate K sourcePulled :=
      (isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H).comapOfIso e.symm
    have hle : solvableRadicalDefiningIdeal K ≤ sourcePulled :=
      solvableRadicalDefiningIdeal_le K sourcePulled hsourcePulled
    intro x hx
    have hx' := hle (HopfIdeal.mem_comapOfSurjective.mp hx)
    have hx'' := HopfIdeal.mem_comapOfSurjective.mp hx'
    have hcancel : (toBialgHom e.inv) ((toBialgHom e.hom) x) = x := by
      have h := congrArg (fun f : H ⟶ H => toBialgHom f x) e.hom_inv_id
      simpa only [toBialgHom_comp, BialgHom.comp_apply, toBialgHom_id,
        BialgHom.coe_id, id_eq] using h
    rwa [hcancel] at hx''
  · exact solvableRadicalDefiningIdeal_le H pulled hpulled

/-- An isomorphism of finite-type commutative Hopf algebras induces an isomorphism of their
solvable radicals. -/
noncomputable def solvableRadicalIsoOfIso (e : H ≅ K) :
    solvableRadical H ≅ solvableRadical K :=
  eqToIso (congrArg (quotient H)
    (comapOfSurjective_solvableRadicalDefiningIdeal e).symm) ≪≫
    quotientIsoOfIso e (solvableRadicalDefiningIdeal K)

/-- The isomorphism of solvable radicals commutes with the coordinate quotient maps. -/
@[simp]
theorem solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom (e : H ≅ K) :
    solvableRadicalCoordinateMap H ≫ (solvableRadicalIsoOfIso e).hom =
      e.hom ≫ solvableRadicalCoordinateMap K := by
  rw [solvableRadicalIsoOfIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    solvableRadicalCoordinateMap_def H, solvableRadicalCoordinateMap_def K,
    mkQuotient_comp_eqToHom, mkQuotient_comp_quotientIsoOfIso_hom]
  exact comapOfSurjective_solvableRadicalDefiningIdeal e

/-- The inverse isomorphism of solvable radicals commutes with the coordinate quotient maps. -/
@[simp]
theorem solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_inv (e : H ≅ K) :
    solvableRadicalCoordinateMap K ≫ (solvableRadicalIsoOfIso e).inv =
      e.inv ≫ solvableRadicalCoordinateMap H := by
  rw [← cancel_mono (solvableRadicalIsoOfIso e).hom]
  simp

/-- The isomorphism induced by the identity isomorphism is the identity on the solvable
radical. -/
@[simp]
theorem solvableRadicalIsoOfIso_refl :
    solvableRadicalIsoOfIso (Iso.refl H) = Iso.refl (solvableRadical H) := by
  apply Iso.ext
  apply solvableRadical_hom_ext
  rw [solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom]
  simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- Isomorphisms induced on solvable radicals respect composition. -/
@[simp]
theorem solvableRadicalIsoOfIso_trans (e : H ≅ K) (f : K ≅ L) :
    solvableRadicalIsoOfIso (e ≪≫ f) =
      solvableRadicalIsoOfIso e ≪≫ solvableRadicalIsoOfIso f := by
  apply Iso.ext
  apply solvableRadical_hom_ext
  rw [solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom]
  simp only [Iso.trans_hom]
  conv_rhs =>
    rw [← Category.assoc,
      solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom,
      Category.assoc,
      solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom]
  simp

/-- The inverse of the isomorphism induced on solvable radicals is the isomorphism induced by
the inverse ambient isomorphism. -/
@[simp]
theorem solvableRadicalIsoOfIso_symm (e : H ≅ K) :
    (solvableRadicalIsoOfIso e).symm = solvableRadicalIsoOfIso e.symm := by
  apply Iso.ext
  apply solvableRadical_hom_ext
  rw [Iso.symm_hom,
    solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_inv,
    solvableRadicalCoordinateMap_comp_solvableRadicalIsoOfIso_hom]
  rfl

end FiniteTypeCommHopfAlgCat

end

end TauCeti
