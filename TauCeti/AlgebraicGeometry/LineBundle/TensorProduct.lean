/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct.Closure
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Tensor products of line bundles

The sheafified tensor product of `𝒪_X`-modules sends two line bundles to a line bundle. This file
packages that operation in the category `InvertibleSheaf X`, together with the unit computations
for the trivial line bundle.

## Main declarations

* `InvertibleSheaf.tensorProduct` packages the tensor product of two line bundles;
* `InvertibleSheaf.tensorProduct_obj` identifies its underlying sheaf;
* `InvertibleSheaf.tensorProductCongrLeft` and `InvertibleSheaf.tensorProductCongrRight` transport
  isomorphisms through either tensor factor;
* `InvertibleSheaf.tensorProductComm` exchanges the two tensor factors;
* `InvertibleSheaf.tensorTrivialLeftIso` and `InvertibleSheaf.tensorTrivialRightIso` are the
  unit isomorphisms in the full category of invertible sheaves.

The underlying sheaf is exposed by `tensorProduct_obj`, while the congruence, symmetry, and unit
isomorphisms provide the categorical API for manipulating tensor products of line bundles.
-/

-- This implementation follows `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A.

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The tensor product of two line bundles on a scheme. -/
def tensorProduct (L K : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨Scheme.Modules.tensorProduct X L.obj K.obj,
    by
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
      exact SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf) (M := L.obj) (N := K.obj)⟩

/-- The underlying sheaf of `tensorProduct L K` is the sheafified tensor product of the
underlying sheaves of `L` and `K`. -/
@[simp]
lemma tensorProduct_obj (L K : InvertibleSheaf X) :
    (tensorProduct L K).obj = Scheme.Modules.tensorProduct X L.obj K.obj :=
  (rfl)

/-- The sheaf isomorphism underlying transport through the first tensor factor. -/
def tensorProductCongrLeftIso {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L' K).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj,
    _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct] using
    (SheafOfModules.tensorProductCongrLeft (N := K.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- An isomorphism of the first factor transports through the tensor product. -/
def tensorProductCongrLeft {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    tensorProduct L K ≅ tensorProduct L' K :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrLeftIso e))

@[simp]
lemma tensorProductCongrLeft_hom_val {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).hom.hom.val =
      (tensorProductCongrLeftIso e).hom.val := by
  simp only [tensorProductCongrLeft, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductCongrLeft_inv_val {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    (tensorProductCongrLeft (K := K) e).inv.hom.val =
      (tensorProductCongrLeftIso e).inv.val := by
  simp only [tensorProductCongrLeft, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying transport through the second tensor factor. -/
def tensorProductCongrRightIso {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct L K').obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj,
    _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct] using
    (SheafOfModules.tensorProductCongrRight (M := L.obj) X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e))

/-- An isomorphism of the second factor transports through the tensor product. -/
def tensorProductCongrRight {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProduct L K ≅ tensorProduct L K' :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCongrRightIso e))

@[simp]
lemma tensorProductCongrRight_hom_val {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).hom.hom.val =
      (tensorProductCongrRightIso e).hom.val := by
  simp only [tensorProductCongrRight, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductCongrRight_inv_val {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    (tensorProductCongrRight (L := L) e).inv.hom.val =
      (tensorProductCongrRightIso e).inv.val := by
  simp only [tensorProductCongrRight, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying symmetry of the tensor product of line bundles. -/
def tensorProductCommIso (L K : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L K).obj (tensorProduct K L).obj := by
  simpa only [tensorProduct_obj, ObjectProperty.ι_obj,
    _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct] using
    (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj)

/-- The tensor product of line bundles is symmetric. -/
def tensorProductComm (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorProductCommIso L K))

@[simp]
lemma tensorProductComm_hom_val (L K : InvertibleSheaf X) :
    (tensorProductComm L K).hom.hom.val =
      (tensorProductCommIso L K).hom.val := by
  simp only [tensorProductComm, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorProductComm_inv_val (L K : InvertibleSheaf X) :
    (tensorProductComm L K).inv.hom.val =
      (tensorProductCommIso L K).inv.val := by
  simp only [tensorProductComm, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying the left unit for the tensor product of line bundles. -/
def tensorTrivialLeftIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct (trivial X) L).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj,
    _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)

/-- The trivial line bundle is a left unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorProduct (trivial X) L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialLeftIsoSheaf L))

@[simp]
lemma tensorTrivialLeftIso_hom_val (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).hom.hom.val =
      (tensorTrivialLeftIsoSheaf L).hom.val := by
  simp only [tensorTrivialLeftIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorTrivialLeftIso_inv_val (L : InvertibleSheaf X) :
    (tensorTrivialLeftIso L).inv.hom.val =
      (tensorTrivialLeftIsoSheaf L).inv.val := by
  simp only [tensorTrivialLeftIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

/-- The sheaf isomorphism underlying the right unit for the tensor product of line bundles. -/
def tensorTrivialRightIsoSheaf (L : InvertibleSheaf X) :
    @Iso (SheafOfModules X.ringCatSheaf) _ (tensorProduct L (trivial X)).obj L.obj := by
  simpa only [tensorProduct_obj, trivial_obj,
    _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct] using
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)

/-- The trivial line bundle is a right unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorProduct L (trivial X) ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (tensorTrivialRightIsoSheaf L))

@[simp]
lemma tensorTrivialRightIso_hom_val (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).hom.hom.val =
      (tensorTrivialRightIsoSheaf L).hom.val := by
  simp only [tensorTrivialRightIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_hom_val]

@[simp]
lemma tensorTrivialRightIso_inv_val (L : InvertibleSheaf X) :
    (tensorTrivialRightIso L).inv.hom.val =
      (tensorTrivialRightIsoSheaf L).inv.val := by
  simp only [tensorTrivialRightIso, ObjectProperty.isoMk, ObjectProperty.homMk,
    _root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso_inv_val]

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
