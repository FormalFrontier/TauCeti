/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.ObjectProperty.Opposite
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Equivalence
public import TauCeti.Algebra.Coalgebra.Convolution
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Cartier duality for finite commutative affine group schemes

This file transports finite-dimensional Cartier duality from coordinate Hopf algebras to affine
group schemes over a field. A Hopf spectrum is finite over the base precisely when its coordinate
algebra is finite-dimensional, and it is a commutative group object precisely when its coordinate
Hopf algebra is cocommutative.

## Main declarations

* `TauCeti.finiteCommAffineGroupSchemeProperty`: the object property selecting finite
  commutative affine group schemes over a field.
* `TauCeti.finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat`: the restricted
  Hopf--`Spec` anti-equivalence.
* `TauCeti.finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.functorCompιIso`:
  after both inclusions, the restricted equivalence is Mathlib's `hopfSpec`.
* `TauCeti.finiteCommAffineGroupSchemeCartierDuality`: Cartier duality transported to finite
  commutative affine group schemes.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This completes the field-level scheme transport in Layer 4, "Cartier duality", of the
ReductiveGroups roadmap. Extension to finite locally free group schemes over a general base is a
separate step.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti

universe u

private instance finite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite) where
  toRespectsLeft :=
    { precomp := fun i hi f hf => by
        let _ := hi
        let _ := hf
        infer_instance }
  toRespectsRight :=
    { postcomp := fun i hi f hf => by
        let _ := hi
        let _ := hf
        infer_instance }

/-- A Hopf spectrum is a commutative group object exactly when its coordinate Hopf algebra is
cocommutative. -/
theorem isCocomm_iff_isCommMonObj_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    Coalgebra.IsCocomm k H ↔
      IsCommMonObj
        (((hopfSpec (CommRingCat.of k)).obj (op H)).X) := by
  constructor
  · intro h
    let _ := h
    rw [hopfSpec_obj_eq_asOver]
    infer_instance
  · intro h
    rw [hopfSpec_obj_eq_asOver] at h
    let _ := h
    constructor
    let leftPoint : WithConv (H →ₐ[k] TensorProduct k H H) :=
      toConv (Bialgebra.TensorProduct.includeLeft
        (R := k) (H₁ := H) (H₂ := H)).toAlgHom
    let rightPoint : WithConv (H →ₐ[k] TensorProduct k H H) :=
      toConv (Bialgebra.TensorProduct.includeRight
        (R := k) (H₁ := H) (H₂ := H)).toAlgHom
    have hcomm : leftPoint * rightPoint = rightPoint * leftPoint := by
      apply (AlgebraicGeometry.Spec.mapMulEquiv
        (R := k) (S := H) (T := TensorProduct k H H)).injective
      simpa only [map_mul] using mul_comm
        ((AlgebraicGeometry.Spec.mapMulEquiv
          (R := k) (S := H) (T := TensorProduct k H H)) leftPoint)
        ((AlgebraicGeometry.Spec.mapMulEquiv
          (R := k) (S := H) (T := TensorProduct k H H)) rightPoint)
    have hswap :
        toConv ((Algebra.TensorProduct.comm k H H).toAlgHom.comp
          (Bialgebra.comulAlgHom k H)) = rightPoint * leftPoint := by
      rw [Bialgebra.toConv_comp_comulAlgHom]
      simp only [leftPoint, rightPoint,
        Bialgebra.TensorProduct.includeLeft_toAlgHom,
        Bialgebra.TensorProduct.includeRight_toAlgHom,
        Algebra.TensorProduct.comm_comp_includeLeft,
        Algebra.TensorProduct.comm_comp_includeRight]
    have hcomul :
        toConv ((Algebra.TensorProduct.comm k H H).toAlgHom.comp
          (Bialgebra.comulAlgHom k H)) =
            toConv (Bialgebra.comulAlgHom k H) := by
      rw [hswap, ← hcomm]
      exact Bialgebra.comulPoint_eq_include_mul.symm
    have hlinear := congrArg
      (fun f : WithConv (H →ₐ[k] TensorProduct k H H) => f.ofConv.toLinearMap) hcomul
    simp only [AlgHom.comp_toLinearMap, Bialgebra.toLinearMap_comulAlgHom] at hlinear
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hlinear x

/-- A Hopf spectrum is finite over its base exactly when its coordinate algebra is
finite-dimensional. -/
theorem moduleFinite_iff_isFinite_hopfSpec
    (k : Type u) [Field k] (H : CommHopfAlgCat.{u} k) :
    Module.Finite k H ↔
      IsFinite (((hopfSpec (CommRingCat.of k)).obj (op H)).X.hom) := by
  rw [hopfSpec_obj_X_hom]
  rw [MorphismProperty.cancel_left_of_respectsIso
    (P := @IsFinite) (eqToHom (hopfSpec_obj_X_left k H))]
  rw [IsFinite.SpecMap_iff]
  -- `SpecMap_iff` leaves the algebra map behind the `CommRingCat.ofHom` projection.
  change Module.Finite k H ↔ (algebraMap k H).Finite
  exact RingHom.finite_algebraMap.symm

/-- The object property selecting finite commutative affine group schemes over a field. -/
def finiteCommAffineGroupSchemeProperty (k : Type u) [Field k] :
    ObjectProperty (AffineGroupSchemeCat (CommRingCat.of k)) :=
  fun G => IsFinite G.obj.X.hom ∧ IsCommMonObj G.obj.X

/-- Membership in the finite-commutative affine-group-scheme property. -/
@[simp]
theorem finiteCommAffineGroupSchemeProperty_iff
    (k : Type u) [Field k] (G : AffineGroupSchemeCat (CommRingCat.of k)) :
    finiteCommAffineGroupSchemeProperty k G ↔
      IsFinite G.obj.X.hom ∧ IsCommMonObj G.obj.X :=
  Iff.rfl

private theorem isCommMonObj_of_grp_iso
    {C : Type u} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {G H : Grp C} (e : G ≅ H) (hG : IsCommMonObj G.X) : IsCommMonObj H.X := by
  let _ := hG
  constructor
  apply (cancel_mono e.inv.hom.hom).1
  simp only [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality]
  simp only [Category.assoc, IsCommMonObj.mul_comm]

instance (k : Type u) [Field k] :
    (finiteCommAffineGroupSchemeProperty k).IsClosedUnderIsomorphisms where
  of_iso e hG := by
    constructor
    · exact (MorphismProperty.over_iso_iff (@IsFinite)
        ((Grp.forget _).mapIso
          ((affineGroupSchemeProperty (CommRingCat.of k)).ι.mapIso e))).mp hG.1
    · exact isCommMonObj_of_grp_iso
        ((affineGroupSchemeProperty (CommRingCat.of k)).ι.mapIso e) hG.2

/-- Under the affine Hopf/group-scheme anti-equivalence, finite-dimensionality and
cocommutativity of the coordinate Hopf algebra correspond to finiteness and commutativity of the
affine group scheme. -/
theorem finiteCommAffineGroupSchemeProperty_inverseImage
    (k : Type u) [Field k] :
    (finiteCommAffineGroupSchemeProperty k).inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor =
      (finiteBicommutativeHopfAlgProperty k).op := by
  ext H
  let G : AffineGroupSchemeCat (CommRingCat.of k) :=
    ⟨(hopfSpec (CommRingCat.of k)).obj H, by
      apply (affineGroupSchemeProperty_iff _).mpr
      rw [← essImage_hopfSpec]
      exact ⟨H, ⟨Iso.refl _⟩⟩⟩
  let e : (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).functor.obj H ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of k)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k)).app H)
  rw [ObjectProperty.prop_inverseImage_iff,
    finiteCommAffineGroupSchemeProperty_iff, ObjectProperty.op_iff,
    finiteBicommutativeHopfAlgProperty_iff]
  constructor
  · intro h
    have hG : finiteCommAffineGroupSchemeProperty k G :=
      (finiteCommAffineGroupSchemeProperty k).prop_of_iso e h
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec k H.unop).mpr hG.1,
      (isCocomm_iff_isCommMonObj_hopfSpec k H.unop).mpr hG.2⟩
  · intro h
    apply (finiteCommAffineGroupSchemeProperty k).prop_of_iso e.symm
    exact ⟨(moduleFinite_iff_isFinite_hopfSpec k H.unop).mp h.1,
      (isCocomm_iff_isCommMonObj_hopfSpec k H.unop).mp h.2⟩

/-- The category of finite commutative affine group schemes over a field. -/
abbrev FiniteCommAffineGroupSchemeCat (k : Type u) [Field k] :=
  (finiteCommAffineGroupSchemeProperty k).FullSubcategory

instance {k : Type u} [Field k] (G : FiniteCommAffineGroupSchemeCat.{u} k) :
    IsFinite G.obj.obj.X.hom :=
  G.property.1

instance {k : Type u} [Field k] (G : FiniteCommAffineGroupSchemeCat.{u} k) :
    IsCommMonObj G.obj.obj.X :=
  G.property.2

/-- `Spec` as an anti-equivalence from finite-dimensional bicommutative Hopf algebras to finite
commutative affine group schemes over a field. -/
noncomputable def finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat
    (k : Type u) [Field k] :
    (FiniteBicommutativeHopfAlgCat.{u} k)ᵒᵖ ≌
      FiniteCommAffineGroupSchemeCat k :=
  (ObjectProperty.opEquivalence (finiteBicommutativeHopfAlgProperty k)).symm.trans <|
    (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of k)).congrFullSubcategory
        (finiteCommAffineGroupSchemeProperty_inverseImage k)

/-- The restricted equivalence followed by the finite-commutative inclusion is definitionally
the unrestricted equivalence applied after forgetting the finiteness and cocommutativity proofs.
This private isomorphism isolates the implementation of the object-property restrictions. -/
private noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCatFunctorCompιIso
    (k : Type u) [Field k] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).functor ⋙
        (finiteCommAffineGroupSchemeProperty k).ι ≅
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} k)
          (CommHopfAlgCat.{u} k)).op ⋙
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of k)).functor :=
  Iso.refl _

/-- The forward restricted anti-equivalence, followed by the inclusions into affine group schemes
and all group schemes, is `hopfSpec` applied after forgetting the finiteness and cocommutativity
proofs. This is the computation interface for the restricted equivalence. -/
noncomputable def
    finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat.functorCompιIso
    (k : Type u) [Field k] :
    (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).functor ⋙
          (finiteCommAffineGroupSchemeProperty k).ι ⋙
        (affineGroupSchemeProperty (CommRingCat.of k)).ι ≅
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} k)
          (CommHopfAlgCat.{u} k)).op ⋙ hopfSpec (CommRingCat.of k) :=
  Functor.isoWhiskerRight
      (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCatFunctorCompιIso k)
      (affineGroupSchemeProperty (CommRingCat.of k)).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (forget₂ (FiniteBicommutativeHopfAlgCat.{u} k)
        (CommHopfAlgCat.{u} k)).op
      (commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of k))

/-- **Cartier duality for finite commutative affine group schemes over a field.** On coordinate
Hopf algebras this is finite linear dualization. -/
noncomputable def finiteCommAffineGroupSchemeCartierDuality
    (k : Type u) [Field k] :
    (FiniteCommAffineGroupSchemeCat k)ᵒᵖ ≌
      FiniteCommAffineGroupSchemeCat k :=
  ((finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k).rightOp).symm.trans <|
    (FiniteBicommutativeHopfAlgCat.cartierDuality (k := k)).symm |>.trans
      (finiteBicommutativeHopfAlgCatOpEquivFiniteCommAffineGroupSchemeCat k)

end TauCeti
