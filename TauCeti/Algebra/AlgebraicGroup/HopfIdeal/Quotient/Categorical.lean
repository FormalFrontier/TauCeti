/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Hopf-ideal quotients as categorical subgroup inclusions

A morphism of commutative Hopf algebras represents a morphism in the opposite category of
commutative algebras. In particular, the quotient map `H ⟶ H/I` represents the closed-subgroup
inclusion `Spec(H/I) ⟶ Spec H`. This file supplies that normality-free categorical inclusion,
its monomorphism and monoid-homomorphism instances, and its action on generalized points.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientGrpObjInclusion`: the categorical closed-subgroup inclusion
  represented by a Hopf-ideal quotient.
* `TauCeti.CommHopfAlgCat.quotientGrpObjInclusion_mono`: the inclusion is a monomorphism.
* `TauCeti.CommHopfAlgCat.quotientGrpObjInclusion_isMonHom`: the inclusion preserves the
  group-object multiplication.

## References

This is the categorical form of the Layer 3 Hopf-ideal/closed-subgroup dictionary in the
ReductiveGroups roadmap. It uses Mathlib's `commHopfAlgCatEquivCogrpCommAlgCat` and
`CategoryTheory.op_mono_of_epi` together with the point-level quotient API in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic`.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- The categorical closed-subgroup inclusion represented contravariantly by the quotient map
`H ⟶ H/I`. -/
noncomputable def quotientGrpObjInclusion (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) : grpObj (quotient H I) ⟶ grpObj H :=
  grpObjMap (mkQuotient H I)

/-- The categorical quotient inclusion is the opposite of the coordinate quotient map. -/
@[simp]
theorem quotientGrpObjInclusion_unop (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    (quotientGrpObjInclusion H I).unop = CommAlgCat.ofHom (mkQuotient H I).hom := by
  exact grpObjMap_unop (mkQuotient H I)

/-- A quotient group-object inclusion preserves multiplication. -/
noncomputable instance quotientGrpObjInclusion_isMonHom
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    IsMonHom (quotientGrpObjInclusion H I) := by
  change IsMonHom (grpObjMap (mkQuotient H I))
  infer_instance

/-- A quotient group-object inclusion is a monomorphism. -/
noncomputable instance quotientGrpObjInclusion_mono
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) :
    Mono (quotientGrpObjInclusion H I) := by
  let q : CommAlgCat.of R H ⟶ CommAlgCat.of R (quotient H I) :=
    CommAlgCat.ofHom (mkQuotient H I).hom
  let _ : Epi q := ConcreteCategory.epi_of_surjective q (mkQuotient_surjective H I)
  apply (unop_epi_iff (quotientGrpObjInclusion H I)).mp
  rw [quotientGrpObjInclusion_unop]
  exact ‹Epi q›

/-- Under the group-object point equivalences, composition with the categorical quotient
inclusion is the usual quotient-points homomorphism. -/
theorem grpObjPointsMulEquiv_comp_quotientGrpObjInclusion
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (X : (CommAlgCat.{u} R)ᵒᵖ) (q : X ⟶ grpObj (quotient H I)) :
    grpObjPointsMulEquiv H X (q ≫ quotientGrpObjInclusion H I) =
      quotientPointsHom H I X.unop (grpObjPointsMulEquiv (quotient H I) X q) := by
  exact grpObjPointsMulEquiv_comp_grpObjMap (mkQuotient H I) X q

end TauCeti.CommHopfAlgCat
