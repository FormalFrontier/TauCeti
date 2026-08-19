/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# The pointwise quotient presheaf of an affine group

A normal Hopf ideal `I` in a commutative Hopf algebra `H` cuts out a normal closed subgroup
`V(I)(A) ≤ G(A)` over every commutative value algebra `A`. This file forms the pointwise quotient

`G(A) / V(I)(A)`

and packages it as a group-valued functor on commutative algebras. The quotient projections are
natural in `A`. At every value algebra the resulting group satisfies the quotient universal
property: a homomorphism out of `G(A)` descends uniquely when it kills `V(I)(A)`.

This is the presheaf quotient that precedes fppf sheafification in Layer 3 of the reductive-groups
roadmap. It is not asserted to be an fppf sheaf or representable; those are separate downstream
steps with additional hypotheses.

## Main declarations

* `TauCeti.CommHopfAlgCat.pointwiseQuotientGroup`: the group `G(A) / V(I)(A)`.
* `TauCeti.CommHopfAlgCat.pointwiseQuotientFunctor`: the pointwise quotient presheaf.
* `TauCeti.CommHopfAlgCat.pointwiseQuotientProjection`: the natural quotient projection.
* `TauCeti.CommHopfAlgCat.pointwiseQuotientLift`: the quotient universal property at each value
  algebra, with its factorization and uniqueness properties.

## References

See J. S. Milne, *Algebraic Groups* (2017), Section 5, for quotient sheaves. The group quotient
and its universal property use Mathlib's `QuotientGroup.map` and `QuotientGroup.lift`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The pointwise quotient `G(A) / V(I)(A)` associated to a normal Hopf ideal `I`.

The denominator is the subgroup of `A`-points which vanish on `I`. Normality follows from the
coordinate conjugation criterion `HopfIdeal.IsNormal`. -/
noncomputable abbrev pointwiseQuotientGroup (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) : GrpCat.{max v w} := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  exact GrpCat.of
    (HopfAlgebra.points (R := R) (H := H) A ⧸ quotientPointsSubgroup H I A)

/-- The quotient projection from ambient points to the pointwise quotient. -/
noncomputable def pointwiseQuotientMk (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    HopfAlgebra.points (R := R) (H := H) A ⟶ pointwiseQuotientGroup H I hI A := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  exact GrpCat.ofHom (QuotientGroup.mk' (quotientPointsSubgroup H I A))

/-- The pointwise quotient projection sends a point to its ordinary quotient class. -/
@[simp]
theorem pointwiseQuotientMk_apply (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    pointwiseQuotientMk H I hI A g =
      QuotientGroup.mk' (quotientPointsSubgroup H I A) g := by
  rfl

/-- The kernel of the pointwise quotient projection is exactly the subgroup cut out by `I`. -/
theorem pointwiseQuotientMk_ker (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    (pointwiseQuotientMk H I hI A).hom.ker = quotientPointsSubgroup H I A := by
  dsimp only
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  simpa only [pointwiseQuotientMk, GrpCat.hom_ofHom] using
    QuotientGroup.ker_mk' (quotientPointsSubgroup H I A)

/-- An ambient point maps to the identity exactly when it belongs to the subgroup cut out by `I`. -/
@[simp]
theorem pointwiseQuotientMk_eq_one_iff (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    pointwiseQuotientMk H I hI A g = 1 ↔ g ∈ quotientPointsSubgroup H I A := by
  dsimp only
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  rw [pointwiseQuotientMk_apply]
  exact QuotientGroup.eq_one_iff g

/-- The pointwise quotient projection is surjective. -/
theorem pointwiseQuotientMk_surjective (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    Function.Surjective (pointwiseQuotientMk H I hI A) := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  exact QuotientGroup.mk'_surjective (quotientPointsSubgroup H I A)

/-- The map on pointwise quotients induced by a morphism of value algebras. -/
noncomputable def mapPointwiseQuotient (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) {A B : CommAlgCat.{w} R} (χ : A ⟶ B) :
    pointwiseQuotientGroup H I hI A ⟶ pointwiseQuotientGroup H I hI B := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  let _ : (quotientPointsSubgroup H I B).Normal :=
    quotientPointsSubgroup_normal H I hI B
  exact GrpCat.ofHom <| QuotientGroup.map
    (N := quotientPointsSubgroup H I A) (quotientPointsSubgroup H I B)
      (HopfAlgebra.mapPoints (H := H) χ).hom
      (fun _ hg => mapPoints_mem_quotientPointsSubgroup H I χ hg)

/-- Mapping a quotient class is represented by mapping any ambient representative. -/
@[simp]
theorem mapPointwiseQuotient_mk (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) {A B : CommAlgCat.{w} R} (χ : A ⟶ B)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    mapPointwiseQuotient H I hI χ (pointwiseQuotientMk H I hI A g) =
      pointwiseQuotientMk H I hI B (HopfAlgebra.mapPoints (H := H) χ g) := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  let _ : (quotientPointsSubgroup H I B).Normal :=
    quotientPointsSubgroup_normal H I hI B
  exact QuotientGroup.map_mk (N := quotientPointsSubgroup H I A)
    (quotientPointsSubgroup H I B) (HopfAlgebra.mapPoints (H := H) χ).hom
      (fun _ hg => mapPoints_mem_quotientPointsSubgroup H I χ hg) g

/-- The pointwise quotient presheaf `A ↦ G(A) / V(I)(A)`. -/
noncomputable def pointwiseQuotientFunctor (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := pointwiseQuotientGroup H I hI A
  map χ := mapPointwiseQuotient H I hI χ
  map_id A := by
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    simpa only [mapPointwiseQuotient, HopfAlgebra.mapPoints_id, GrpCat.hom_id,
      GrpCat.hom_ofHom, GrpCat.ofHom_id] using congrArg GrpCat.ofHom
      (QuotientGroup.map_id (quotientPointsSubgroup H I A))
  map_comp {A B C} χ ψ := by
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    let _ : (quotientPointsSubgroup H I B).Normal :=
      quotientPointsSubgroup_normal H I hI B
    let _ : (quotientPointsSubgroup H I C).Normal :=
      quotientPointsSubgroup_normal H I hI C
    simpa only [mapPointwiseQuotient, HopfAlgebra.mapPoints_comp, GrpCat.hom_comp,
      GrpCat.hom_ofHom, GrpCat.ofHom_comp] using congrArg GrpCat.ofHom
      (QuotientGroup.map_comp_map (quotientPointsSubgroup H I A)
        (quotientPointsSubgroup H I B) (quotientPointsSubgroup H I C)
        (HopfAlgebra.mapPoints (H := H) χ).hom
        (HopfAlgebra.mapPoints (H := H) ψ).hom
        (fun _ hg => mapPoints_mem_quotientPointsSubgroup H I χ hg)
        (fun _ hg => mapPoints_mem_quotientPointsSubgroup H I ψ hg)).symm

/-- The object part of the pointwise quotient functor is the quotient group of ambient points by
the subgroup cut out by `I`. -/
@[simp]
theorem pointwiseQuotientFunctor_obj (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    (pointwiseQuotientFunctor H I hI).obj A = pointwiseQuotientGroup H I hI A :=
  (rfl)

/-- The map part of the pointwise quotient functor is the map induced on quotient groups. -/
@[simp]
theorem pointwiseQuotientFunctor_map (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) {A B : CommAlgCat.{w} R} (χ : A ⟶ B) :
    (pointwiseQuotientFunctor H I hI).map χ =
      eqToHom (pointwiseQuotientFunctor_obj H I hI A) ≫
        mapPointwiseQuotient H I hI χ ≫
          eqToHom (pointwiseQuotientFunctor_obj H I hI B).symm :=
  (rfl)

/-- The natural projection from the ambient functor of points to its pointwise quotient. -/
noncomputable def pointwiseQuotientProjection (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    HopfAlgebra.pointsFunctor (R := R) (H := H) ⟶ pointwiseQuotientFunctor H I hI where
  app A := pointwiseQuotientMk H I hI A ≫
    eqToHom (pointwiseQuotientFunctor_obj H I hI A).symm
  naturality {A B} χ := by
    let _ : (quotientPointsSubgroup H I A).Normal :=
      quotientPointsSubgroup_normal H I hI A
    let _ : (quotientPointsSubgroup H I B).Normal :=
      quotientPointsSubgroup_normal H I hI B
    rw [pointwiseQuotientFunctor_map]
    -- The functor-object theorem inserts `eqToHom` transports around the concrete quotient map.
    -- Since this natural transformation is still being constructed, its component theorem cannot
    -- yet rewrite the structure-field goal; `change` removes exactly those definitional transports.
    change pointwiseQuotientMk H I hI A ≫ mapPointwiseQuotient H I hI χ =
      HopfAlgebra.mapPoints (H := H) χ ≫ pointwiseQuotientMk H I hI B
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact (mapPointwiseQuotient_mk H I hI χ g).symm

/-- Each component of the natural quotient projection is the ordinary quotient-group map. -/
@[simp]
theorem pointwiseQuotientProjection_app (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) :
    (pointwiseQuotientProjection H I hI).app A =
      pointwiseQuotientMk H I hI A ≫
        eqToHom (pointwiseQuotientFunctor_obj H I hI A).symm :=
  (rfl)

/-- A homomorphism from ambient points which kills the normal subgroup descends to the pointwise
quotient group. -/
noncomputable def pointwiseQuotientLift (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) (K : GrpCat.{max v w})
    (f : HopfAlgebra.points (R := R) (H := H) A ⟶ K)
    (hf : quotientPointsSubgroup H I A ≤ f.hom.ker) :
    pointwiseQuotientGroup H I hI A ⟶ K := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  exact GrpCat.ofHom (QuotientGroup.lift (quotientPointsSubgroup H I A) f.hom hf)

/-- The lift from a pointwise quotient agrees with the original homomorphism on every ambient
representative. -/
@[simp]
theorem pointwiseQuotientLift_mk (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) (K : GrpCat.{max v w})
    (f : HopfAlgebra.points (R := R) (H := H) A ⟶ K)
    (hf : quotientPointsSubgroup H I A ≤ f.hom.ker)
    (g : HopfAlgebra.points (R := R) (H := H) A) :
    pointwiseQuotientLift H I hI A K f hf (pointwiseQuotientMk H I hI A g) = f g := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  simpa only [pointwiseQuotientLift, pointwiseQuotientMk, GrpCat.hom_ofHom,
    QuotientGroup.mk'_apply] using
    QuotientGroup.lift_mk' (quotientPointsSubgroup H I A) hf g

/-- A homomorphism out of the pointwise quotient is uniquely determined by its composite with the
quotient projection. -/
theorem pointwiseQuotientLift_unique (H : _root_.CommHopfAlgCat.{v} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) (A : CommAlgCat.{w} R) (K : GrpCat.{max v w})
    (f : HopfAlgebra.points (R := R) (H := H) A ⟶ K)
    (hf : quotientPointsSubgroup H I A ≤ f.hom.ker)
    (g : pointwiseQuotientGroup H I hI A ⟶ K)
    (hg : pointwiseQuotientMk H I hI A ≫ g = f) :
    g = pointwiseQuotientLift H I hI A K f hf := by
  let _ : (quotientPointsSubgroup H I A).Normal :=
    quotientPointsSubgroup_normal H I hI A
  apply GrpCat.hom_ext
  apply QuotientGroup.monoidHom_ext (quotientPointsSubgroup H I A)
  calc
    g.hom.comp (QuotientGroup.mk' (quotientPointsSubgroup H I A)) = f.hom := by
      simpa only [pointwiseQuotientMk, GrpCat.hom_comp, GrpCat.hom_ofHom] using
        congrArg (fun q ↦ q.hom) hg
    _ = (pointwiseQuotientLift H I hI A K f hf).hom.comp
        (QuotientGroup.mk' (quotientPointsSubgroup H I A)) := by
      simpa only [pointwiseQuotientLift, GrpCat.hom_ofHom] using
        (QuotientGroup.lift_comp_mk' (quotientPointsSubgroup H I A) f.hom hf).symm

end CommHopfAlgCat

end TauCeti
