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

/-- An isomorphism of the first factor transports through the tensor product. -/
def tensorProductCongrLeft {L L' K : InvertibleSheaf X} (e : L ≅ L') :
    tensorProduct L K ≅ tensorProduct L' K :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (SheafOfModules.tensorProductCongrLeft X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e)))

/-- An isomorphism of the second factor transports through the tensor product. -/
def tensorProductCongrRight {L K K' : InvertibleSheaf X} (e : K ≅ K') :
    tensorProduct L K ≅ tensorProduct L K' :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (SheafOfModules.tensorProductCongrRight X.sheaf
      ((SheafOfModules.isInvertible X).ι.mapIso e)))

/-- The tensor product of line bundles is symmetric. -/
def tensorProductComm (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X
      (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj))

/-- The trivial line bundle is a left unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorProduct (trivial X) L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X (by
      simpa only [tensorProduct_obj, trivial_obj] using
        (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)))

/-- The trivial line bundle is a right unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorProduct L (trivial X) ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (_root_.AlgebraicGeometry.Scheme.Modules.isoOfSheafIso X (by
      simpa only [tensorProduct_obj, trivial_obj] using
        (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)))

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
