/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction and sheafification for sheaves of modules

For a continuous and cocontinuous functor between sites, this file identifies pushforward of the
sheafification of a presheaf of modules with sheafification after pushforward. Restriction to a
slice site is the special case given by `Over.forget X`.

The comparison is obtained from the unit of Mathlib's sheafification adjunction. Its underlying
morphism of presheaves of abelian groups is the sheafification map whiskered by the functor between
sites. Cocontinuity preserves its local injectivity and surjectivity, so Mathlib's localization
theorem makes the comparison an isomorphism after sheafification. No formalization is vendored:
the ingredients are Mathlib's `PresheafOfModules.sheafificationAdjunction`,
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`, and
`Presheaf.isLocallyInjective_whisker`/`Presheaf.isLocallySurjective_whisker`.

## Main declarations

* `SheafOfModules.pushforwardSheafificationIso` is the sheafification-pushforward comparison for
  a continuous and cocontinuous functor;
* `SheafOfModules.overSheafificationIso` is its specialization to a slice site.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`", by providing the restriction compatibility needed to
compare local trivializations on refinements.
-/

public section

open CategoryTheory Category Opposite

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section General

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K RingCat.{u})
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private abbrev pushedRing : Sheaf J RingCat.{u} :=
  (F.sheafPushforwardContinuous RingCat.{u} J K).obj R

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The underlying presheaf of the continuous pushforward is precomposition by the functor
between sites. -/
abbrev pushforwardRingIso : F.op ⋙ R.obj ≅
    ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj :=
  Iso.refl _

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private abbrev presheafPushforward :
    PresheafOfModules.{u} R.obj ⥤
      PresheafOfModules.{u} (pushedRing (J := J) (K := K) F R).obj :=
  PresheafOfModules.pushforward (F := F)
    (pushforwardRingIso (J := J) (K := K) F R).inv

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private abbrev sheafPushforward :
    SheafOfModules.{u} R ⥤
      SheafOfModules.{u} (pushedRing (J := J) (K := K) F R) :=
  SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.IsCocontinuous J K] in
/-- The pushforward of a sheafification unit, as a map of presheaves of modules. This is the
canonical comparison whose sheafification is inverted by `pushforwardSheafificationIso`. -/
def pushforwardToSheafify (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.pushforward (F := F)
        (pushforwardRingIso (J := J) (K := K) F R).inv).obj P ⟶
      ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P)).val :=
  (presheafPushforward F R).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P)

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.IsCocontinuous J K] in
/-- Pushforward of the sheafification unit becomes whiskering on underlying presheaves. -/
private theorem toPresheaf_map_pushforwardToSheafify_def
    (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op
        ((PresheafOfModules.toPresheaf _).map
          ((PresheafOfModules.sheafificationAdjunction (R := R)
            (𝟙 R.obj)).unit.app P)) := by
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.IsCocontinuous J K] in
/-- On underlying presheaves of abelian groups, `pushforwardToSheafify` is the canonical
sheafification map whiskered by the functor between sites. -/
theorem toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{u} R.obj) :
    (PresheafOfModules.toPresheaf _).map
        (pushforwardToSheafify (J := J) (K := K) F R P) =
      Functor.whiskerLeft F.op (CategoryTheory.toSheafify K P.presheaf) := by
  rw [toPresheaf_map_pushforwardToSheafify_def,
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] in
private theorem W_toPresheaf_map_pushforwardToSheafify
    (P : PresheafOfModules.{u} R.obj) :
    J.W ((PresheafOfModules.toPresheaf _).map
      (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  rw [toPresheaf_map_pushforwardToSheafify]
  exact (J.W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker J K F _,
      Presheaf.isLocallySurjective_whisker J K F _⟩

private instance isIso_sheafification_map_pushforwardToSheafify
    (P : PresheafOfModules.{u} R.obj) :
    IsIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P)) := by
  -- `IsIso` is the inverse image of the isomorphism morphism property under sheafification.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)))
        (pushforwardToSheafify (J := J) (K := K) F R P)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact W_toPresheaf_map_pushforwardToSheafify (J := J) (K := K) F R P

/-- For each presheaf of modules, pushforward along a continuous and cocontinuous functor of its
sheafification is isomorphic to sheafification after pushforward. -/
def pushforwardSheafificationIso (P : PresheafOfModules.{u} R.obj) :
    (SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) ≅
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).obj
          ((PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := J) (K := K) F R).inv).obj P) :=
  (sheafificationIso (pushedRing (J := J) (K := K) F R)
      ((sheafPushforward (J := J) (K := K) F R).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).symm ≪≫
    (asIso ((PresheafOfModules.sheafification
      (R := pushedRing (J := J) (K := K) F R)
      (𝟙 (pushedRing (J := J) (K := K) F R).obj)).map
        (pushforwardToSheafify (J := J) (K := K) F R P))).symm

/-- The inverse of `pushforwardSheafificationIso` is the canonical comparison obtained from the
sheafification unit and counit. -/
theorem pushforwardSheafificationIso_inv (P : PresheafOfModules.{u} R.obj) :
    (pushforwardSheafificationIso F R P).inv =
      (PresheafOfModules.sheafification
        (R := (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
        (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R).obj)).map
          (pushforwardToSheafify (J := J) (K := K) F R P) ≫
        (sheafificationIso ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
          ((SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)).obj
            ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P))).hom := by
  simp [pushforwardSheafificationIso]

end General

/-- For each presheaf of modules and object of the site, restriction of its sheafification is
isomorphic to the sheafification of its restriction. -/
def overSheafificationIso (R : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} R.obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P).over X ≅
      (PresheafOfModules.sheafification (R := R.over X) (𝟙 (R.over X).obj)).obj
        ((PresheafOfModules.pushforward (F := Over.forget X)
          (pushforwardRingIso (J := J.over X) (K := J) (Over.forget X) R).inv).obj P) :=
  pushforwardSheafificationIso (J := J.over X) (K := J) (Over.forget X) R P

end SheafOfModules

end

end TauCeti
