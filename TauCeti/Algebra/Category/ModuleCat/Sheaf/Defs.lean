/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Basic definitions for sheaves of modules

This file collects the coefficient sheaf obtained by forgetting commutativity and the counit
identifying the sheafification of the underlying presheaf of a sheaf of modules with that sheaf.

## Main declarations

* `SheafOfModules.ringCatSheaf` forgets commutativity in a sheaf of commutative rings;
* `SheafOfModules.sheafificationIso` identifies a sheaf of modules with the sheafification of its
  underlying presheaf.

This supports `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`".
-/

public section

open CategoryTheory Category

namespace TauCeti

universe u v v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The sheaf of rings underlying a sheaf of commutative rings on a site; the site-level
analogue of `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
abbrev ringCatSheaf (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})] : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- Sheafifying the underlying presheaf of modules of a sheaf of `R`-modules `M`, for a sheaf of
rings `R`, recovers `M`; this is the counit of the sheafification adjunction. -/
def sheafificationIso (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).app M

/-- The forward map of `sheafificationIso` is the counit of the sheafification adjunction. -/
@[simp]
theorem sheafificationIso_hom (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{v} R) :
    (sheafificationIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit.app M := by
  simp only [sheafificationIso]
  rfl

end SheafOfModules

end


end TauCeti
