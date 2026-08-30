/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic

/-!
# Tensor products with trivial invertible sheaves

For a sheaf of commutative rings `R` on a site, the free sheaf of `R`-modules on one generator
is canonically isomorphic to the tensor unit by `SheafOfModules.freePUnitIsoUnit`, defined in
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Free.lean`. This file uses that comparison to show that
tensoring an invertible sheaf with a globally trivial rank-one sheaf preserves invertibility.

## Main declarations

* `SheafOfModules.tensorProductFreePUnitIsoLeft` and
  `SheafOfModules.tensorProductFreePUnitIsoRight` identify tensoring with that standard sheaf
  with the identity;
* `SheafOfModules.IsInvertible.tensorProduct_of_iso_unit_left` and
  `SheafOfModules.IsInvertible.tensorProduct_of_iso_unit_right` show that a tensor product is
  invertible when one factor is globally trivial and the other is invertible.

These are the local computations needed to prove that arbitrary invertible sheaves are closed
under tensor product: after refining two trivializing covers to a common cover, both factors are
the standard free rank-one sheaf there. This advances
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a scheme; the
Picard group `Pic X` under `⊗`". Restriction compatibility is provided by
`TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction`; the common-refinement step
needed for the full closure theorem remains subsequent work.

No formalization is vendored. The construction reuses Tau Ceti's generic free-rank-one/unit
comparison and sheafified tensor-unit isomorphisms.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
variable [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

variable (R : Sheaf J CommRingCat.{u})

/-- Tensoring on the left by the standard free rank-one sheaf does nothing. -/
def tensorProductFreePUnitIsoLeft
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) M ≅ M :=
  tensorProductCongrLeft R (freePUnitIsoUnit (ringCatSheaf R)) ≪≫
    tensorProductUnitIsoLeft R M

/-- Tensoring on the right by the standard free rank-one sheaf does nothing. -/
def tensorProductFreePUnitIsoRight
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) ≅ M :=
  tensorProductCongrRight R (freePUnitIsoUnit (ringCatSheaf R)) ≪≫
    tensorProductUnitIsoRight R M

namespace IsInvertible

variable {M N : SheafOfModules.{u} (ringCatSheaf R)}

/-- A tensor product is invertible when its left factor is isomorphic to the tensor unit and its
right factor is invertible. This is the local form used after trivializing the left factor. -/
theorem tensorProduct_of_iso_unit_left [IsInvertible N]
    (e : M ≅ _root_.SheafOfModules.unit (ringCatSheaf R)) :
    IsInvertible (tensorProduct R M N) :=
  IsInvertible.of_iso
    ((tensorProductCongrLeft R e ≪≫ tensorProductUnitIsoLeft R N).symm)

/-- A tensor product is invertible when its right factor is isomorphic to the tensor unit and its
left factor is invertible. This is the local form used after trivializing the right factor. -/
theorem tensorProduct_of_iso_unit_right [IsInvertible M]
    (e : N ≅ _root_.SheafOfModules.unit (ringCatSheaf R)) :
    IsInvertible (tensorProduct R M N) :=
  IsInvertible.of_iso
    ((tensorProductCongrRight R e ≪≫ tensorProductUnitIsoRight R M).symm)

/-- Tensoring an invertible sheaf on the left by the standard free rank-one sheaf preserves
invertibility. -/
instance tensorProduct_freePUnit_left [IsInvertible N] :
    IsInvertible
      (tensorProduct R (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit) N) :=
  tensorProduct_of_iso_unit_left R (freePUnitIsoUnit (ringCatSheaf R))

/-- Tensoring an invertible sheaf on the right by the standard free rank-one sheaf preserves
invertibility. -/
instance tensorProduct_freePUnit_right [IsInvertible M] :
    IsInvertible
      (tensorProduct R M (_root_.SheafOfModules.free (R := ringCatSheaf R) PUnit)) :=
  tensorProduct_of_iso_unit_right R (freePUnitIsoUnit (ringCatSheaf R))

end IsInvertible

end SheafOfModules

end

end TauCeti
