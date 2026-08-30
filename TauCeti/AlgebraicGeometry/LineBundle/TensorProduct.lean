/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.TensorProduct
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Tensoring line bundles with the trivial bundle

The sheafified tensor product of `𝒪_X`-modules has the trivial line bundle as a unit. This file
packages that computation in the category `InvertibleSheaf X`: tensoring an invertible sheaf on
either side by `InvertibleSheaf.trivial X` again gives an invertible sheaf, canonically isomorphic
to the original one.

## Main declarations

* `InvertibleSheaf.tensorTrivialLeft` and `InvertibleSheaf.tensorTrivialRight` package the two
  tensor products as invertible sheaves;
* `InvertibleSheaf.tensorTrivialLeftIso` and `InvertibleSheaf.tensorTrivialRightIso` are their
  unit isomorphisms in the full category of invertible sheaves.

This is the scheme-level local computation used in the construction of the tensor product of two
arbitrary line bundles. It advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item
"Invertible sheaves on a scheme; the Picard group `Pic X` under `⊗`". Closure under tensor
product for two arbitrary locally trivial factors, duals, and the Picard group remain subsequent
work.

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
