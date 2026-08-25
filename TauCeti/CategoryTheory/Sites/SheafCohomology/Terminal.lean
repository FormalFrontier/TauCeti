/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology at a terminal object

Mathlib carries two accounts of the cohomology of an abelian sheaf `F` on a site `(C, J)`:

* `CategoryTheory.Sheaf.H F n`, the `Ext`-groups from the constant sheaf `ℤ`, which is the
  cohomology of the site as a whole;
* `CategoryTheory.Sheaf.H' F n X`, the `Ext`-groups from the sheafification of the free abelian
  presheaf on `yoneda.obj X`, which is the cohomology of the object `X`.

They agree when `X` is a terminal object, and this file supplies that comparison. The abstract
Mayer-Vietoris sequence of `Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris` is stated
in terms of `Sheaf.H'`, so the comparison is what lets a covering of the whole site compute
`Sheaf.H`.

## Main declarations

* `TauCeti.CategoryTheory.Sheaf.cohomologyPresheafObjIsoH`: the comparison
  `Hⁿ(T, F) ≅ Hⁿ(F)` at a terminal object `T`, as an isomorphism of abelian groups;
* `TauCeti.CategoryTheory.Sheaf.cohomologyPresheafEvaluationIsoFunctorH`: the same comparison as a
  natural isomorphism in the coefficient sheaf.

This settles the first item of the `## TODO` list of
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`. It is used in
`TauCeti/AlgebraicGeometry/Cohomology/MayerVietoris.lean` to obtain the Mayer-Vietoris sequence
for the cohomology of a scheme, which is Layer B infrastructure for
`TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is vendored: the ingredients are
Mathlib's `CategoryTheory.Limits.IsTerminal.isTerminalObj`, `FreeAbelianGroup.uniqueEquiv`,
`CategoryTheory.Functor.constComp` and `CategoryTheory.Abelian.extFunctor`.
-/

public section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

private noncomputable def yonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  (hT.isTerminalObj yoneda).uniqueUpToIso (Functor.isTerminalConst Cᵒᵖ Types.isTerminalPUnit)

private def freeObjPUnitIso :
    AddCommGrpCat.free.obj PUnit.{v + 1} ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  AddEquiv.toAddCommGrpIso ((FreeAbelianGroup.uniqueEquiv PUnit).trans AddEquiv.ulift.symm)

private noncomputable def freeYonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.isoWhiskerRight (yonedaObjIsoConst hT) AddCommGrpCat.free ≪≫
    Functor.constComp (J := Cᵒᵖ) PUnit.{v + 1} AddCommGrpCat.free ≪≫
      (Functor.const Cᵒᵖ).mapIso freeObjPUnitIso

noncomputable section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

private def freeYonedaSheafIsoConstantSheaf {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J _).mapIso (freeYonedaObjIsoConst hT)

end

noncomputable section

namespace Sheaf

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

-- Mathlib's `functorH` and `extFunctorObj` use definitionally equal object and map data.
-- Naming that identification here isolates the definitional coincidence used below.
private noncomputable def functorHIso (n : ℕ) :
    _root_.CategoryTheory.Sheaf.functorH J n ≅
      (_root_.CategoryTheory.Abelian.extFunctor n).obj
        (op ((constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift ℤ)))) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by
      intros
      ext
      rfl)

variable (J) in
/-- At a terminal object `T`, the cohomology presheaf evaluated at `T` is the cohomology of the
site, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorH (n : ℕ) {T : C} (hT : IsTerminal T) :
    _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ≅
      _root_.CategoryTheory.Sheaf.functorH J n :=
  (_root_.CategoryTheory.Abelian.extFunctor n).mapIso
      (freeYonedaSheafIsoConstantSheaf hT).symm.op ≪≫
    functorHIso n

variable (n : ℕ) {T : C} (hT : IsTerminal T)

/-- At a terminal object, the cohomology of the object is the cohomology of the site. -/
noncomputable abbrev cohomologyPresheafObjIsoH (F : Sheaf J AddCommGrpCat.{v}) :
    _root_.CategoryTheory.Sheaf.H' F n T ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H F n) :=
  (cohomologyPresheafEvaluationIsoFunctorH J n hT).app F

end Sheaf

end

end CategoryTheory

end TauCeti
