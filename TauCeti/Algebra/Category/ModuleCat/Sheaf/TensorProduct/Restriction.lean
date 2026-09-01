/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-!
# Restriction of tensor products of sheaves of modules

For a sheaf of commutative rings `R`, sheaves of `R`-modules `M` and `N`, and a continuous and
cocontinuous functor between sites, this file identifies the pushforward of `M ⊗ N` with the tensor
product of the pushforwards of `M` and `N`. Restriction to a slice site is the special case given by
`Over.forget X`.

The proof combines `SheafOfModules.pushforwardSheafificationIso` with Mathlib's monoidal structure
on `PresheafOfModules.pushforward₀OfCommRingCat`. No formalization is vendored.

## Main declarations

* `SheafOfModules.pushforwardTensorProductIso` is the generic comparison;
* `SheafOfModules.overTensorProductIso` specializes it to restriction over an object.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`". It supplies the restriction compatibility needed to
put two local trivializations over a common refinement and prove that an arbitrary tensor product
of invertible sheaves is invertible.
-/

public section

open CategoryTheory Category MonoidalCategory Opposite

namespace TauCeti

universe u v₁ v₂ u₁ u₂

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
variable (R : Sheaf K CommRingCat.{u})

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Pushforward of a sheaf of commutative rings along a continuous functor. -/
abbrev pushforwardCommRing : Sheaf J CommRingCat.{u} :=
  (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R

omit [F.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Pushforward of modules over a sheaf of commutative rings, with commutativity forgotten on the
coefficient sheaves. After unfolding `ringCatSheaf` and `sheafPushforwardContinuous`, the source
and target coefficient sheaves are definitionally equal. -/
abbrev pushforwardModule :
    SheafOfModules.{u} (ringCatSheaf R) ⥤
      SheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := J) (K := K) F R)) :=
  SheafOfModules.pushforward (J := J) (K := K) (F := F) (𝟙 _)

/-- For each pair of sheaves of modules, pushforward along a continuous and cocontinuous functor
commutes with their tensor product. -/
def pushforwardTensorProductIso
    (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardModule (J := J) (K := K) F R).obj (tensorProduct R M N) ≅
      tensorProduct (pushforwardCommRing (J := J) (K := K) F R)
        ((pushforwardModule (J := J) (K := K) F R).obj M)
        ((pushforwardModule (J := J) (K := K) F R).obj N) :=
  (pushforwardModule (J := J) (K := K) F R).mapIso (tensorProductIso R M N) ≪≫
    pushforwardSheafificationIso F (ringCatSheaf R) (M.val ⊗ N.val) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (pushforwardCommRing (J := J) (K := K) F R)).obj)).mapIso
        (Functor.Monoidal.μIso
          (PresheafOfModules.pushforward₀OfCommRingCat F R.obj) M.val N.val).symm ≪≫
    (tensorProductIso (pushforwardCommRing (J := J) (K := K) F R)
      ((pushforwardModule (J := J) (K := K) F R).obj M)
      ((pushforwardModule (J := J) (K := K) F R).obj N)).symm

/-- For each object of the site, restriction of a tensor product is isomorphic to the tensor
product of the restrictions. The coefficient sheaves on the target are definitionally equal after
unfolding `ringCatSheaf`, `Sheaf.over`, and `sheafPushforwardContinuous`. -/
def overTensorProductIso (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : D)
    [(K.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [(K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (tensorProduct R M N).over X ≅ tensorProduct (R.over X) (M.over X) (N.over X) :=
  pushforwardTensorProductIso (J := K.over X) (K := K) (Over.forget X) R M N

/-- The forward map of `pushforwardTensorProductIso` is the sheafification comparison composed
with the tensorator of the pushforward, read through the defining identifications of the two
tensor products. -/
@[simp]
theorem pushforwardTensorProductIso_hom (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardTensorProductIso (J := J) (K := K) F R M N).hom =
      (pushforwardModule (J := J) (K := K) F R).map (tensorProductIso R M N).hom ≫
        (pushforwardSheafificationIso F (ringCatSheaf R) (M.val ⊗ N.val)).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (ringCatSheaf (pushforwardCommRing (J := J) (K := K) F R)).obj)).map
            (Functor.Monoidal.μIso
              (PresheafOfModules.pushforward₀OfCommRingCat F R.obj) M.val N.val).inv ≫
        (tensorProductIso (pushforwardCommRing (J := J) (K := K) F R)
          ((pushforwardModule (J := J) (K := K) F R).obj M)
          ((pushforwardModule (J := J) (K := K) F R).obj N)).inv := by
  -- `Iso.trans_hom` does not fire: the coefficient sheaf carried by the middle isomorphism is
  -- only definitionally the one carried by the outer isomorphisms, so `simp` cannot match it,
  -- and the two sides are identified by unfolding `Iso.trans`.
  rfl

/-- The forward map of `overTensorProductIso` is the slice-site instance of
`pushforwardTensorProductIso_hom`. -/
@[simp]
theorem overTensorProductIso_hom (M N : SheafOfModules.{u} (ringCatSheaf R)) (X : D)
    [(K.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
    [(K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (overTensorProductIso R M N X).hom =
      (pushforwardModule (J := K.over X) (K := K) (Over.forget X) R).map
          (tensorProductIso R M N).hom ≫
        (pushforwardSheafificationIso (J := K.over X) (K := K) (Over.forget X)
            (ringCatSheaf R) (M.val ⊗ N.val)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf (R.over X)).obj)).map
            (Functor.Monoidal.μIso
              (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj)
              M.val N.val).inv ≫
        (tensorProductIso (R.over X) (M.over X) (N.over X)).inv :=
  pushforwardTensorProductIso_hom (J := K.over X) (K := K) (Over.forget X) R M N

end SheafOfModules

end

end TauCeti
