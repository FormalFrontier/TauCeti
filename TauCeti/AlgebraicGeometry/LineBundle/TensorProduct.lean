/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProductClosure
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Tensor products of line bundles

The sheafified tensor product of `𝒪_X`-modules sends two line bundles to a line bundle. This file
packages that operation in the category `InvertibleSheaf X`, together with the unit computations
for the trivial line bundle.

## Main declarations

* `InvertibleSheaf.tensorProduct` packages the tensor product of two line bundles;
* `InvertibleSheaf.tensorProduct_obj` identifies its underlying sheaf;
* `InvertibleSheaf.tensorProductCommIso` exchanges the two tensor factors;
* `InvertibleSheaf.tensorTrivialLeftIso` and `InvertibleSheaf.tensorTrivialRightIso` are their
  unit isomorphisms in the full category of invertible sheaves.

This is the scheme-level tensor-product step in Layer A of the Jacobian challenge, item
"Invertible sheaves on a scheme; the Picard group `Pic X` under `⊗`". Duals, associativity, and
the group of isomorphism classes remain subsequent work.

No formalization is vendored. The proofs specialize the site-level isomorphisms from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/TensorProduct.lean` to the structure sheaf of
`X`.
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
  ⟨SheafOfModules.tensorProduct X.sheaf L.obj K.obj,
    by
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      let _ : SheafOfModules.IsInvertible (R := X.ringCatSheaf) K.obj := K.property
      exact SheafOfModules.IsInvertible.tensorProduct (R := X.sheaf) (M := L.obj) (N := K.obj)⟩

@[simp]
lemma tensorProduct_obj (L K : InvertibleSheaf X) :
    (tensorProduct L K).obj = SheafOfModules.tensorProduct X.sheaf L.obj K.obj :=
  (rfl)

/-- The tensor product of line bundles is symmetric. -/
def tensorProductCommIso (L K : InvertibleSheaf X) : tensorProduct L K ≅ tensorProduct K L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (SheafOfModules.tensorProductComm X.sheaf L.obj K.obj)

/-- Tensoring an invertible sheaf on the left by the trivial line bundle, packaged as an
invertible sheaf. -/
def tensorTrivialLeft (L : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨TauCeti.SheafOfModules.tensorProduct X.sheaf
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit) L.obj,
    by
      let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      exact TauCeti.SheafOfModules.IsInvertible.tensorProduct_of_iso_unit_left X.sheaf
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf)⟩

/-- The underlying sheaf of `tensorTrivialLeft` is the tensor product of the trivial sheaf and
the given sheaf. -/
@[simp]
lemma tensorTrivialLeft_obj (L : InvertibleSheaf X) :
    (tensorTrivialLeft L).obj =
      TauCeti.SheafOfModules.tensorProduct X.sheaf
        (trivial X).obj L.obj := by
  rw [trivial_obj]
  exact (rfl)

/-- Tensoring an invertible sheaf on the right by the trivial line bundle, packaged as an
invertible sheaf. -/
def tensorTrivialRight (L : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨TauCeti.SheafOfModules.tensorProduct X.sheaf L.obj
      (_root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit),
    by
      let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
      exact TauCeti.SheafOfModules.IsInvertible.tensorProduct_of_iso_unit_right X.sheaf
        (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf)⟩

/-- The underlying sheaf of `tensorTrivialRight` is the tensor product of the given sheaf and
the trivial sheaf. -/
@[simp]
lemma tensorTrivialRight_obj (L : InvertibleSheaf X) :
    (tensorTrivialRight L).obj =
      TauCeti.SheafOfModules.tensorProduct X.sheaf L.obj
        (trivial X).obj := by
  rw [trivial_obj]
  exact (rfl)

/-- The trivial line bundle is a left unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialLeftIso (L : InvertibleSheaf X) : tensorTrivialLeft L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoLeft X.sheaf L.obj)

/-- The trivial line bundle is a right unit for the sheafified tensor product of invertible
sheaves. -/
def tensorTrivialRightIso (L : InvertibleSheaf X) : tensorTrivialRight L ≅ L :=
  ObjectProperty.isoMk (SheafOfModules.isInvertible X)
    (TauCeti.SheafOfModules.tensorProductFreePUnitIsoRight X.sheaf L.obj)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
