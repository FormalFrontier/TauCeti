/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Ulift
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Basic
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

universe u v

variable {R : Type u} [CommRing R]

/-- Regard a group-valued functor as a group object in type-valued functors. -/
private noncomputable def groupFunctorGrp {C : Type u} [Category.{v} C]
    (F : C ⥤ GrpCat.{u}) : Grp (C ⥤ Type u) where
  X := F ⋙ forget GrpCat.{u}
  grp :=
    { one :=
        { app := fun X => ↾fun _ => (1 : F.obj X)
          naturality := by
            intro X Y f
            ext x
            exact (F.map f).hom.map_one.symm }
      mul :=
        { app := fun X => ↾fun p => p.1 * p.2
          naturality := by
            intro X Y f
            ext p
            -- The functor-category tensor map acts componentwise on the two entries.
            change (F.map f) p.1 * (F.map f) p.2 = (F.map f) (p.1 * p.2)
            exact ((F.map f).hom.map_mul p.1 p.2).symm }
      one_mul := by
        ext X p
        exact one_mul p.2
      mul_one := by
        ext X p
        exact mul_one p.1
      mul_assoc := by
        ext X p
        exact mul_assoc p.1.1 p.1.2 p.2
      inv :=
        { app := fun X => ↾fun x => x⁻¹
          naturality := by
            intro X Y f
            ext x
            -- Naturality is the inverse-preservation law of the component homomorphism.
            change ((F.map f) x)⁻¹ = (F.map f) x⁻¹
            exact ((F.map f).hom.map_inv x).symm }
      left_inv := by
        ext X p
        exact inv_mul_cancel p
      right_inv := by
        ext X p
        exact mul_inv_cancel p }

/-- A natural transformation of group-valued functors is a morphism of their associated group
objects in type-valued functors. -/
private noncomputable def groupFunctorGrpMap {C : Type u} [Category.{v} C]
    {F G : C ⥤ GrpCat.{u}} (α : F ⟶ G) : groupFunctorGrp F ⟶ groupFunctorGrp G :=
  Grp.homMk'' (Functor.whiskerRight α (forget GrpCat.{u}))
    (one_f := by
      dsimp [groupFunctorGrp]
      ext X p
      -- Evaluating at the tensor unit reduces the group-object law to preservation of `1`.
      change (α.app X) 1 = 1
      exact (α.app X).hom.map_one)
    (mul_f := by
      dsimp [groupFunctorGrp]
      ext X p
      -- The group-object multiplication is pointwise multiplication in every value group.
      change (α.app X) ((p.1 : F.obj X) * (p.2 : F.obj X)) =
        (α.app X) (p.1 : F.obj X) * (α.app X) (p.2 : F.obj X)
      exact (α.app X).hom.map_mul p.1 p.2)

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

/-- The convolution-points presheaf as a group object in type-valued presheaves, with values
lifted to the universe in which the affine-site sheafification lives. -/
noncomputable def pointsPresheafGrp (H : _root_.CommHopfAlgCat.{u} R) :
    Grp (((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :=
  groupFunctorGrp
    (HopfAlgebra.pointsGroupPresheaf H ⋙ GrpCat.uliftFunctor.{u + 1, u})

/-- The quotient projection as a morphism of group objects in type-valued presheaves. -/
noncomputable def pointwiseQuotientPresheafGrpProjection
    (H : _root_.CommHopfAlgCat.{u} R) (I : HopfIdeal R H) (hI : I.IsNormal) :
    pointsPresheafGrp H ⟶ pointwiseQuotientPresheafGrp H I hI :=
  groupFunctorGrpMap <| Functor.whiskerRight
    (pointwiseQuotientPresheafProjection H I hI) GrpCat.uliftFunctor.{u + 1, u}

/-- The fppf sheaf of points, regarded as a group object in type-valued sheaves.

This form is canonically the sheafification of the group-valued points presheaf. Since that
presheaf is already an fppf sheaf, its underlying type-valued sheaf is canonically isomorphic to
`HopfAlgebra.pointsFppfSheaf H` after forgetting the group structure. -/
noncomputable def pointsFppfGroupObject (H : _root_.CommHopfAlgCat.{u} R) :
    Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1))) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.obj
    (pointsPresheafGrp H)

/-- The underlying sheaf of `pointsFppfGroupObject` is canonically the universe lift of the
existing group-valued points sheaf `HopfAlgebra.pointsFppfSheaf`. -/
noncomputable def pointsFppfGroupObjectIso (H : _root_.CommHopfAlgCat.{u} R) :
    (pointsFppfGroupObject H).X ≅
      (sheafCompose (CommAlgCat.fppfTopology R)
        ((forget GrpCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).obj
          (HopfAlgebra.pointsFppfSheaf H) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  let F := (sheafCompose (CommAlgCat.fppfTopology R)
    ((forget GrpCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u})).obj
      (HopfAlgebra.pointsFppfSheaf H)
  let e : (pointsPresheafGrp H).X ≅ F.obj := by
    change _ ≅ (HopfAlgebra.pointsFppfSheaf H).obj ⋙
      (forget GrpCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u}
    rw [HopfAlgebra.pointsFppfSheaf_obj]
    exact Iso.refl _
  change (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
    (pointsPresheafGrp H).X ≅ F
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso e ≪≫
    (sheafificationIso F).symm

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

/-- The group object in type-valued presheaves underlying a group object in fppf sheaves. -/
noncomputable def fppfGroupObjectToPresheaf
    (F : Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))) :
    Grp (((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) := by
  let _ : (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp.obj F

/-- Maps from the sheafified points group object to a group object in fppf sheaves are naturally
equivalent to maps from the points presheaf to its underlying presheaf. -/
noncomputable def pointsFppfHomEquiv (H : _root_.CommHopfAlgCat.{u} R)
    (F : Grp (Sheaf (CommAlgCat.fppfTopology R) (Type (u + 1)))) :
    (pointsFppfGroupObject H ⟶ F) ≃
      (pointsPresheafGrp H ⟶ fppfGroupObjectToPresheaf F) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  let _ : (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  exact ((sheafificationAdjunction
    (CommAlgCat.fppfTopology R) (Type (u + 1))).mapGrp).homEquiv
      (pointsPresheafGrp H) F

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
theorem fppfQuotientProjection_homEquiv (H : _root_.CommHopfAlgCat.{u} R)
    (I : HopfIdeal R H) (hI : I.IsNormal) :
    pointsFppfHomEquiv H (fppfQuotientSheaf H I hI) (fppfQuotientProjection H I hI) =
      pointwiseQuotientPresheafGrpProjection H I hI ≫
        fppfQuotientHomEquiv H I hI (fppfQuotientSheaf H I hI) (𝟙 _) := by
  let _ : (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
  let _ : (sheafToPresheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).Monoidal :=
    Functor.Monoidal.ofChosenFiniteProducts _
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
