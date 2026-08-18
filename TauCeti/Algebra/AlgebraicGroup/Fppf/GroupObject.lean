/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Internal.Types.Grp
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Ulift
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Basic

/-!
# Group objects on the affine fppf site

This file relates group-valued presheaves and sheaves on the affine fppf site to group objects in
type-valued presheaves and sheaves. In particular, it presents the convolution-points sheaf of a
commutative Hopf algebra as a group object and exposes the group-object sheafification adjunction.

This is infrastructure for the fppf-sheaf-quotient step of Layer 3, "Normality and quotients", in
the ReductiveGroups roadmap.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped CategoryTheory.MonObj

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R]

/-- Regard a group-valued functor as a group object in type-valued functors. -/
noncomputable def groupFunctorGrp {C : Type u} [Category.{v} C]
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
noncomputable def groupFunctorGrpMap {C : Type u} [Category.{v} C]
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

/-- A natural isomorphism of group-valued functors induces an isomorphism of their associated
group objects in type-valued functors. -/
noncomputable def groupFunctorGrpIso {C : Type u} [Category.{v} C]
    {F G : C ⥤ GrpCat.{u}} (e : F ≅ G) : groupFunctorGrp F ≅ groupFunctorGrp G where
  hom := groupFunctorGrpMap e.hom
  inv := groupFunctorGrpMap e.inv
  hom_inv_id := by
    ext X x
    exact congrArg (fun f ↦ f x) (e.hom_inv_id_app X)
  inv_hom_id := by
    ext X x
    exact congrArg (fun f ↦ f x) (e.inv_hom_id_app X)

/-- The convolution-points presheaf as a group object in type-valued presheaves, with values
lifted to the universe in which the affine-site sheafification lives. -/
noncomputable def pointsPresheafGrp (H : _root_.CommHopfAlgCat.{u} R) :
    Grp (((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ Type (u + 1)) :=
  groupFunctorGrp
    (HopfAlgebra.pointsGroupPresheaf H ⋙ GrpCat.uliftFunctor.{u + 1, u})

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
    -- Unfold `sheafCompose.obj` and the carrier of `pointsPresheafGrp`: both sides are the
    -- universe lift of the underlying group-valued points presheaf.
    change _ ≅ (HopfAlgebra.pointsFppfSheaf H).obj ⋙
      (forget GrpCat.{u}) ⋙ CategoryTheory.uliftFunctor.{u + 1, u}
    rw [HopfAlgebra.pointsFppfSheaf_obj]
    exact Iso.refl _
  -- The carrier of `mapGrp.obj` is definitionally the image of the original carrier; Mathlib's
  -- `mapGrp` API does not provide a separate comparison isomorphism for this wrapper.
  change (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).obj
    (pointsPresheafGrp H).X ≅ F
  exact (presheafToSheaf (CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso e ≪≫
    (sheafificationIso F).symm

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

end TauCeti.CommHopfAlgCat
