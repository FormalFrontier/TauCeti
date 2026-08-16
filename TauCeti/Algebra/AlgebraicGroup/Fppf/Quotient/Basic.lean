/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Fppf.GroupObject
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Presheaf

/-!
# Fppf quotient sheaves of affine groups

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a normal Hopf
ideal. The pointwise quotient `A ↦ G(A) / V(I)(A)` need not satisfy fppf descent. Its
sheafification is the fppf quotient sheaf of `G` by the closed normal subgroup cut out by `I`.

Nonabelian groups are handled as group objects in type-valued presheaves and sheaves. This is the
natural construction because type-valued sheafification is left exact, hence preserves the finite
products used by a group object. It also avoids requiring colimits in `GrpCat`.

No representability is asserted. Representability of an fppf quotient requires additional
hypotheses and is a separate downstream theorem.

## Main declarations

* `TauCeti.CommHopfAlgCat.pointwiseQuotientPresheaf`: the pointwise quotient on the affine fppf
  site.
* `TauCeti.CommHopfAlgCat.fppfQuotientSheaf`: its sheafification as a group object.
* `TauCeti.CommHopfAlgCat.fppfQuotientProjection`: the sheafified quotient projection.
* `TauCeti.CommHopfAlgCat.fppfQuotientHomEquiv`: the quotient sheaf's universal property.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Section 14.

## Implementation notes

The construction uses Mathlib's `sheafificationAdjunction`, its lift `Adjunction.mapGrp` to group
objects, and the finite-product-preserving monoidal structure on type-valued sheafification.

This is the fppf-sheaf-quotient step of Layer 3, "Normality and quotients", in the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]

/-- The pointwise quotient group functor, presented as a presheaf on the affine fppf site. -/
noncomputable abbrev pointwiseQuotientPresheaf (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{u} :=
  (opOpEquivalence (CommAlgCat.{u} R)).functor ⋙ pointwiseQuotientFunctor H I hI

/-- The quotient projection, presented as a morphism of presheaves on the affine fppf site. -/
noncomputable abbrev pointwiseQuotientPresheafProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    HopfAlgebra.pointsGroupPresheaf H ⟶ pointwiseQuotientPresheaf H I hI :=
  Functor.whiskerLeft (opOpEquivalence (CommAlgCat.{u} R)).functor
    (pointwiseQuotientProjection H I hI)

/-- The pointwise quotient presheaf as a group object in type-valued presheaves. Values are
lifted by one universe because the category of commutative `R`-algebras itself lives in
`Type (u + 1)`, the universe in which type-valued sheafification is available. -/
noncomputable def pointwiseQuotientPresheafGrp
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    Grp (((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :=
  groupFunctorGrp
    (pointwiseQuotientPresheaf H I hI ⋙ GrpCat.uliftFunctor.{u + 1, u})

/-- The quotient projection as a morphism of group objects in type-valued presheaves. -/
noncomputable def pointwiseQuotientPresheafGrpProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    pointsPresheafGrp H ⟶ pointwiseQuotientPresheafGrp H I hI :=
  groupFunctorGrpMap <| Functor.whiskerRight
    (pointwiseQuotientPresheafProjection H I hI) GrpCat.uliftFunctor.{u + 1, u}

/-- The carrier of the points presheaf group object is the universe lift of the underlying
group-valued points presheaf. -/
theorem pointsPresheafGrp_X_eq (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsPresheafGrp H).X =
      HopfAlgebra.pointsGroupPresheaf H ⋙ GrpCat.uliftFunctor.{u + 1, u} ⋙
        forget GrpCat.{u + 1} := by
  rfl

/-- The carrier of the pointwise quotient presheaf group object is the universe lift of the
underlying group-valued quotient presheaf. -/
theorem pointwiseQuotientPresheafGrp_X_eq
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    (pointwiseQuotientPresheafGrp H I hI).X =
      pointwiseQuotientPresheaf H I hI ⋙ GrpCat.uliftFunctor.{u + 1, u} ⋙
        forget GrpCat.{u + 1} := by
  rw [pointwiseQuotientPresheafGrp.eq_1]
  rfl

/-- On underlying presheaves, the group-object quotient projection is the universe lift of the
pointwise quotient projection. -/
theorem pointwiseQuotientPresheafGrpProjection_hom_hom
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    (pointwiseQuotientPresheafGrpProjection H I hI).hom.hom =
      eqToHom (pointsPresheafGrp_X_eq H) ≫
        Functor.whiskerRight
          (Functor.whiskerRight (pointwiseQuotientPresheafProjection H I hI)
            GrpCat.uliftFunctor.{u + 1, u}) (forget GrpCat.{u + 1}) ≫
          eqToHom (pointwiseQuotientPresheafGrp_X_eq H I hI).symm := by
  rw [pointwiseQuotientPresheafGrpProjection.eq_1]
  rfl

/-- The fppf quotient sheaf associated to a normal Hopf ideal, as a group object in type-valued
fppf sheaves.

Its underlying sheaf is the sheafification of `A ↦ G(A) / V(I)(A)`. This definition makes no
representability claim. -/
noncomputable def fppfQuotientSheaf (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1))) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.obj
    (pointwiseQuotientPresheafGrp H I hI)

/-- The canonical morphism from the fppf sheaf of points of `G` to the fppf quotient sheaf
`G / V(I)`. -/
noncomputable def fppfQuotientProjection (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    pointsFppfGroupObject H ⟶ fppfQuotientSheaf H I hI := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.map
    (pointwiseQuotientPresheafGrpProjection H I hI)

/-- The carrier of the fppf points group object is the sheafification of the carrier of its
presheaf group object. -/
theorem pointsFppfGroupObject_X_eq
    (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsFppfGroupObject H).X =
      (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        (pointsPresheafGrp H).X := by
  rfl

/-- The carrier of the fppf quotient group object is the sheafification of the pointwise
quotient presheaf's carrier. -/
theorem fppfQuotientSheaf_X_eq
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    (fppfQuotientSheaf H I hI).X =
      (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
        (pointwiseQuotientPresheafGrp H I hI).X := by
  rw [fppfQuotientSheaf.eq_1]
  rfl

/-- On underlying sheaves, the fppf quotient projection is the sheafification of the pointwise
quotient projection. -/
theorem fppfQuotientProjection_hom
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    (fppfQuotientProjection H I hI).hom.hom =
      eqToHom (pointsFppfGroupObject_X_eq H) ≫
        (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).map
          (pointwiseQuotientPresheafGrpProjection H I hI).hom.hom ≫
            eqToHom (fppfQuotientSheaf_X_eq H I hI).symm := by
  rw [fppfQuotientProjection.eq_1]
  rfl

/-- Maps from the fppf quotient sheaf to a group object in fppf sheaves are naturally equivalent
to group-object maps from the pointwise quotient presheaf to its underlying presheaf. -/
noncomputable def fppfQuotientHomEquiv (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal)
    (F : Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))) :
    (fppfQuotientSheaf H I hI ⟶ F) ≃
      (pointwiseQuotientPresheafGrp H I hI ⟶
        fppfGroupObjectToPresheaf F) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  let _ : (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact ((sheafificationAdjunction (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp).homEquiv
    (pointwiseQuotientPresheafGrp H I hI) F

/-- Under the sheafification adjunction, the quotient projection restricts to the pointwise
quotient projection followed by the sheafification unit. -/
@[simp]
theorem pointsFppfHomEquiv_apply_fppfQuotientProjection
    (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    pointsFppfHomEquiv H (fppfQuotientSheaf H I hI) (fppfQuotientProjection H I hI) =
      pointwiseQuotientPresheafGrpProjection H I hI ≫
        fppfQuotientHomEquiv H I hI (fppfQuotientSheaf H I hI) (𝟙 _) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  let _ : (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  -- Unfold the two `HomEquiv` wrappers and `fppfQuotientProjection` to expose the same
  -- `mapGrp` adjunction on both sides; the resulting statement is precisely unit naturality.
  change
    ((sheafificationAdjunction
      (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp).homEquiv _ _
        ((presheafToSheaf
          (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.map
            (pointwiseQuotientPresheafGrpProjection H I hI)) =
      pointwiseQuotientPresheafGrpProjection H I hI ≫
        ((sheafificationAdjunction
          (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp).homEquiv
            (pointwiseQuotientPresheafGrp H I hI)
            ((presheafToSheaf
              (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.obj
                (pointwiseQuotientPresheafGrp H I hI)) (𝟙 _)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simpa using (((sheafificationAdjunction
    (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp).unit.naturality
      (pointwiseQuotientPresheafGrpProjection H I hI)).symm

/-- A group-object morphism from the pointwise quotient presheaf into the underlying presheaf of
an fppf sheaf extends uniquely to the fppf quotient sheaf. -/
noncomputable def fppfQuotientLift (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal)
    (F : Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1))))
    (f : pointwiseQuotientPresheafGrp H I hI ⟶
      fppfGroupObjectToPresheaf F) :
    fppfQuotientSheaf H I hI ⟶ F :=
  (fppfQuotientHomEquiv H I hI F).symm f

end TauCeti.CommHopfAlgCat
