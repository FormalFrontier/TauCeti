/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Yoneda
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Normal

/-!
# Normal Hopf ideals as categorical normal subgroups

A commutative Hopf algebra is equivalently a group object in the opposite category of
commutative algebras. Under this equivalence, a Hopf-ideal quotient `H ⟶ H/I` represents the
closed-subgroup inclusion `Spec(H/I) ⟶ Spec H`.

This file proves that normality of the Hopf ideal makes this inclusion a normal subgroup object
in Mathlib's sense. The proof uses the generalized-point criterion for categorical normality and
the existing characterization of normal Hopf ideals by normality of their subgroups of
algebra-valued points.

The result is the bridge needed to apply the internal semidirect-product construction to two
normal closed affine subgroup schemes. Its multiplication map and scheme-theoretic image are the
binary product used in the maximal-dimension construction of the unipotent radical.

The multiplication bridge used here is `TauCeti.CommHopfAlgCat.grpObjPointsMulEquiv` from
`TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda`.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotientGrpObjInclusion_normal_iff`: a Hopf ideal is normal exactly
  when its categorical inclusion is a normal subgroup object.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–17.
* J. S. Milne, *Algebraic Groups* (2017), §§6.a and 10.20.
* Mathlib's `commHopfAlgCatEquivCogrpCommAlgCat` and
  `CategoryTheory.IsMonHom.normal_iff_normal_monoidHom`; the latter follows Görtz–Wedhorn,
  *Algebraic Geometry II*, Definition 27.3.

This advances Layer 5, "The unipotent radical", of the ReductiveGroups roadmap. It connects the
coordinate normality API to the categorical semidirect-product API used to form the product of
two normal unipotent-radical candidates.
-/

public section

open CategoryTheory Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- Mapping the range of a categorical quotient inclusion through the generalized-point
equivalence gives the subgroup cut out by the Hopf ideal. -/
private theorem quotientGrpObjInclusion_range_map
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (X : (CommAlgCat.{u} R)ᵒᵖ) :
    (IsMonHom.monoidHom (quotientGrpObjInclusion H I) X).range.map
        (grpObjPointsMulEquiv H X).toMonoidHom =
      quotientPointsSubgroup H I X.unop := by
  -- Expose the range definition locally without adding a duplicate public API theorem.
  change _ = (quotientPointsHom H I X.unop).hom.range
  rw [MonoidHom.map_range]
  have hcomp :
      (grpObjPointsMulEquiv H X).toMonoidHom.comp
          (IsMonHom.monoidHom (quotientGrpObjInclusion H I) X) =
        (quotientPointsHom H I X.unop).hom.comp
          (grpObjPointsMulEquiv (quotient H I) X).toMonoidHom := by
    apply MonoidHom.ext
    intro q
    simpa only [MonoidHom.comp_apply, IsMonHom.monoidHom_apply,
      MulEquiv.coe_toMonoidHom] using
      grpObjPointsMulEquiv_comp_quotientGrpObjInclusion H I X q
  rw [hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (grpObjPointsMulEquiv (quotient H I) X).surjective]
  exact (MonoidHom.range_eq_map _).symm

/-- Pointwise normality of the categorical inclusion is equivalent to normality of the
corresponding quotient-points subgroup. -/
private theorem quotientGrpObjInclusion_range_normal_iff
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H)
    (X : (CommAlgCat.{u} R)ᵒᵖ) :
    (IsMonHom.monoidHom (quotientGrpObjInclusion H I) X).range.Normal ↔
      (quotientPointsSubgroup H I X.unop).Normal := by
  let e := grpObjPointsMulEquiv H X
  have hrange := quotientGrpObjInclusion_range_map H I X
  constructor
  · intro h
    rw [← hrange]
    exact h.map e.toMonoidHom e.surjective
  · intro h
    rw [← hrange] at h
    exact e.normal_map_iff.mp h

/-- A Hopf ideal is normal if and only if its categorical closed-subgroup inclusion is a normal
subgroup object in the opposite category of commutative algebras. -/
theorem quotientGrpObjInclusion_normal_iff (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) :
    IsMonHom.Normal (quotientGrpObjInclusion H I) ↔ I.IsNormal := by
  rw [IsMonHom.normal_iff_normal_monoidHom,
    isNormal_iff_quotientPointsSubgroup_normal]
  constructor
  · intro h A
    exact (quotientGrpObjInclusion_range_normal_iff H I (op A)).mp (h (op A))
  · intro h X
    exact (quotientGrpObjInclusion_range_normal_iff H I X).mpr (h X.unop)

end TauCeti.CommHopfAlgCat
