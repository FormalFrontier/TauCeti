/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Geometry.Hodge.Mixed.Morphism

/-!
# The category of mixed Hodge structures

This file bundles mixed Hodge structures whose integral, rational, and complex carriers lie in a
fixed universe. Morphisms are the rational maps from
`TauCeti.Hodge.MixedHodgeStructure.Hom`; their complex actions remain derived by base change.

The resulting category is preadditive and `ℚ`-linear. The rational realization is a faithful
`ℚ`-linear functor to `ModuleCat ℚ`, while the complex realization is a `ℚ`-linear functor to
`ModuleCat ℂ`. These structures are the categorical input for packaging strictness as kernels and
cokernels in the category of mixed Hodge structures.

## Main declarations

* `TauCeti.Hodge.MixedHodgeStructureCat`: a bundled mixed Hodge structure.
* `TauCeti.Hodge.MixedHodgeStructureCat.rational`: the faithful rational realization functor.
* `TauCeti.Hodge.MixedHodgeStructureCat.complex`: the complex realization functor.

## References

Deligne, *Théorie de Hodge II*, §2.3; Peters--Steenbrink, *Mixed Hodge Structures*, Ch. 3.
-/

public section

namespace TauCeti.Hodge

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

/-- The category of mixed Hodge structures with integral, rational, and complex carriers in
`Type u`.

The three carrier types and the two base-change witnesses are bundled so that objects may have
different underlying integral carriers. A morphism is still a single rational map: the integral
carrier is the arithmetic source of the base-change models, not an extra component of a morphism. -/
structure MixedHodgeStructureCat where
  /-- The integral carrier underlying a mixed Hodge structure. -/
  intCarrier : Type u
  /-- The rational vector space underlying a mixed Hodge structure. -/
  ratCarrier : Type u
  /-- The complex vector space underlying a mixed Hodge structure. -/
  complexCarrier : Type u
  /-- The additive group structure on the integral carrier. -/
  [intAddCommGroup : AddCommGroup intCarrier]
  /-- The additive group structure on the rational vector space. -/
  [ratAddCommGroup : AddCommGroup ratCarrier]
  /-- The rational module structure. -/
  [ratModule : Module ℚ ratCarrier]
  /-- The additive group structure on the complex vector space. -/
  [complexAddCommGroup : AddCommGroup complexCarrier]
  /-- The complex module structure. -/
  [complexModule : Module ℂ complexCarrier]
  /-- The structure map from the integral carrier to the rational model. -/
  toRat : intCarrier →ₗ[ℤ] ratCarrier
  /-- The structure map from the integral carrier to the complex model. -/
  toComplex : intCarrier →ₗ[ℤ] complexCarrier
  /-- The rational model is a base change of the integral carrier. -/
  isBaseChangeRat : IsBaseChange ℚ toRat
  /-- The complex model is a base change of the integral carrier. -/
  isBaseChangeComplex : IsBaseChange ℂ toComplex
  /-- The mixed Hodge structure on the bundled base-change models. -/
  hs : MixedHodgeStructure isBaseChangeRat isBaseChangeComplex

namespace MixedHodgeStructureCat

attribute [instance] MixedHodgeStructureCat.intAddCommGroup
  MixedHodgeStructureCat.ratAddCommGroup MixedHodgeStructureCat.ratModule
  MixedHodgeStructureCat.complexAddCommGroup MixedHodgeStructureCat.complexModule

/-- Bundle an existing mixed Hodge structure as an object of `MixedHodgeStructureCat`. -/
abbrev of {Vℤ Vℚ Vℂ : Type u} [AddCommGroup Vℤ] [AddCommGroup Vℚ] [Module ℚ Vℚ]
    [AddCommGroup Vℂ] [Module ℂ Vℂ] {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}
    (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)
    (X : MixedHodgeStructure hℚ hℂ) : MixedHodgeStructureCat.{u} :=
  ⟨Vℤ, Vℚ, Vℂ, ιℚ, ιℂ, hℚ, hℂ, X⟩

/-- The rational vector space underlying a bundled mixed Hodge structure. -/
abbrev rat (X : MixedHodgeStructureCat.{u}) : ModuleCat.{u} ℚ :=
  ModuleCat.of ℚ X.ratCarrier

/-- The complex vector space underlying a bundled mixed Hodge structure. -/
abbrev complexSpace (X : MixedHodgeStructureCat.{u}) : ModuleCat.{u} ℂ :=
  ModuleCat.of ℂ X.complexCarrier

noncomputable instance : Category.{u} MixedHodgeStructureCat.{u} where
  Hom X Y := MixedHodgeStructure.Hom X.hs Y.hs
  id X := MixedHodgeStructure.Hom.id X.hs
  comp f g := g.comp f

/-- Two categorical morphisms of mixed Hodge structures are equal if their rational maps agree. -/
@[ext]
theorem hom_ext {X Y : MixedHodgeStructureCat.{u}} {f g : X ⟶ Y}
    (h : f.toRatLinearMap = g.toRatLinearMap) : f = g :=
  MixedHodgeStructure.Hom.ext (LinearMap.congr_fun h)

/-- The identity morphism has the identity rational linear map. -/
@[simp]
theorem id_toRatLinearMap (X : MixedHodgeStructureCat.{u}) :
    MixedHodgeStructure.Hom.toRatLinearMap (𝟙 X) = LinearMap.id :=
  MixedHodgeStructure.Hom.id_toRatLinearMap

/-- Composition of categorical morphisms is composition of their rational maps. -/
@[simp]
theorem comp_toRatLinearMap {X Y Z : MixedHodgeStructureCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    MixedHodgeStructure.Hom.toRatLinearMap (f ≫ g) =
      g.toRatLinearMap ∘ₗ f.toRatLinearMap :=
  MixedHodgeStructure.Hom.comp_toRatLinearMap g f

/-- The identity morphism has the identity complex linear map. -/
@[simp]
theorem id_toLinearMap (X : MixedHodgeStructureCat.{u}) :
    MixedHodgeStructure.Hom.toLinearMap (𝟙 X) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact MixedHodgeStructure.Hom.id_apply x

/-- Composition of categorical morphisms is composition of their complex linear maps. -/
@[simp]
theorem comp_toLinearMap {X Y Z : MixedHodgeStructureCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    MixedHodgeStructure.Hom.toLinearMap (f ≫ g) = g.toLinearMap ∘ₗ f.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact MixedHodgeStructure.Hom.comp_apply g f x

noncomputable instance : Preadditive MixedHodgeStructureCat.{u} where
  homGroup X Y := inferInstanceAs (AddCommGroup (MixedHodgeStructure.Hom X.hs Y.hs))
  add_comp _ _ _ f g h := MixedHodgeStructure.Hom.comp_add h f g
  comp_add _ _ _ f g h := MixedHodgeStructure.Hom.add_comp g h f

noncomputable instance : Linear ℚ MixedHodgeStructureCat.{u} where
  homModule X Y := inferInstanceAs (Module ℚ (MixedHodgeStructure.Hom X.hs Y.hs))
  smul_comp _ _ _ q f g := MixedHodgeStructure.Hom.comp_smul g q f
  comp_smul _ _ _ f q g := MixedHodgeStructure.Hom.smul_comp q g f

/-- The rational realization of a mixed Hodge structure and its morphisms. -/
@[expose]
noncomputable def rational : MixedHodgeStructureCat.{u} ⥤ ModuleCat.{u} ℚ where
  obj X := X.rat
  map f := ModuleCat.ofHom f.toRatLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    exact id_toRatLinearMap X
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact comp_toRatLinearMap f g

/-- The rational realization sends a mixed Hodge structure to its rational vector space. -/
@[simp]
theorem rational_obj (X : MixedHodgeStructureCat.{u}) : rational.obj X = X.rat :=
  rfl

/-- The rational realization sends a morphism to its underlying rational linear map. -/
@[simp]
theorem rational_map_hom {X Y : MixedHodgeStructureCat.{u}} (f : X ⟶ Y) :
    (rational.map f).hom = f.toRatLinearMap :=
  rfl

noncomputable instance : rational.Faithful where
  map_injective {X Y} f g h := by
    apply hom_ext
    exact congrArg ModuleCat.Hom.hom h

noncomputable instance : rational.Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    exact MixedHodgeStructure.Hom.add_toRatLinearMap f g

noncomputable instance : rational.Linear ℚ where
  map_smul := by
    intro X Y f q
    apply ModuleCat.hom_ext
    exact MixedHodgeStructure.Hom.smul_toRatLinearMap q f

/-- The complex realization of a mixed Hodge structure and the complexification of its
morphisms. -/
@[expose]
noncomputable def complex : MixedHodgeStructureCat.{u} ⥤ ModuleCat.{u} ℂ where
  obj X := X.complexSpace
  map f := ModuleCat.ofHom f.toLinearMap
  map_id X := by
    apply ModuleCat.hom_ext
    exact id_toLinearMap X
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact comp_toLinearMap f g

/-- The complex realization sends a mixed Hodge structure to its complex vector space. -/
@[simp]
theorem complex_obj (X : MixedHodgeStructureCat.{u}) : complex.obj X = X.complexSpace :=
  rfl

/-- The complex realization sends a morphism to its derived complex linear map. -/
@[simp]
theorem complex_map_hom {X Y : MixedHodgeStructureCat.{u}} (f : X ⟶ Y) :
    (complex.map f).hom = f.toLinearMap :=
  rfl

noncomputable instance : complex.Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact MixedHodgeStructure.Hom.add_apply f g x

/-- The complex realization is `ℚ`-linear through the standard inclusion `ℚ → ℂ`. -/
noncomputable instance : complex.Linear ℚ where
  map_smul := by
    intro X Y f q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact MixedHodgeStructure.Hom.smul_apply q f x

end MixedHodgeStructureCat

end TauCeti.Hodge
