/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

* `TauCeti.CategoryTheory.yonedaObjIsoConst`: the presheaf of points of a terminal object is the
  constant presheaf on a point;
* `TauCeti.CategoryTheory.freeYonedaObjIsoConst`: consequently the free abelian presheaf on it is
  the constant presheaf `ℤ`, and `freeYonedaSheafIsoConstantSheaf` sheafifies this;
* `TauCeti.CategoryTheory.cohomologyPresheafObjIsoH` and
  `TauCeti.CategoryTheory.cohomologyPresheafObjAddEquivH`: the resulting comparison
  `Hⁿ(T, F) ≅ Hⁿ(F)` at a terminal object `T`, as an isomorphism of abelian groups and as an
  additive equivalence;
* `TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoFunctorH`: the same comparison as a
  natural isomorphism in the coefficient sheaf.

This settles the first item of the `## TODO` list of
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`. It is used in
`TauCeti/AlgebraicGeometry/Cohomology/MayerVietoris.lean` to obtain the Mayer-Vietoris sequence
for the cohomology of a scheme, which is Layer B infrastructure for
`TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is vendored: the ingredients are
Mathlib's `CategoryTheory.isTerminalEquivUnique`, `FreeAbelianGroup.uniqueEquiv`,
`CategoryTheory.Functor.constComp` and `CategoryTheory.Abelian.extFunctor`.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The presheaf of points of a terminal object is the constant presheaf on a point. -/
def yonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ≅ (Functor.const Cᵒᵖ).obj PUnit.{v + 1} :=
  have (U : Cᵒᵖ) : Unique (U.unop ⟶ T) := isTerminalEquivUnique _ T hT _
  NatIso.ofComponents (fun _ => Equiv.toIso (Equiv.equivPUnit _))
    (by intros; ext; exact Subsingleton.elim (α := PUnit.{v + 1}) _ _)

/-- The free abelian group on a one-element type is `ℤ`. -/
def freeObjPUnitIso :
    AddCommGrpCat.free.obj PUnit.{v + 1} ≅ AddCommGrpCat.of (ULift.{v} ℤ) :=
  AddEquiv.toAddCommGrpIso ((FreeAbelianGroup.uniqueEquiv PUnit).trans AddEquiv.ulift.symm)

/-- The free abelian presheaf on the presheaf of points of a terminal object is the constant
presheaf `ℤ`. -/
def freeYonedaObjIsoConst {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free.{v} ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  Functor.isoWhiskerRight (yonedaObjIsoConst hT) AddCommGrpCat.free ≪≫
    Functor.constComp (J := Cᵒᵖ) PUnit.{v + 1} AddCommGrpCat.free ≪≫
      (Functor.const Cᵒᵖ).mapIso freeObjPUnitIso

noncomputable section

variable [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The free abelian sheaf on a terminal object is the constant sheaf `ℤ`. This is the object
that `CategoryTheory.Sheaf.H` takes `Ext`-groups out of. -/
def freeYonedaSheafIsoConstantSheaf {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  (presheafToSheaf J _).mapIso (freeYonedaObjIsoConst hT)

variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (J) in
/-- At a terminal object `T`, the cohomology presheaf evaluated at `T` is the cohomology of the
site, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoFunctorH (n : ℕ) {T : C} (hT : IsTerminal T) :
    Sheaf.cohomologyPresheafFunctor J n ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op T) ≅
      Sheaf.functorH J n :=
  (_root_.CategoryTheory.Abelian.extFunctor n).mapIso
    (freeYonedaSheafIsoConstantSheaf hT).symm.op

variable (n : ℕ) {T : C} (hT : IsTerminal T)

/-- At a terminal object, the cohomology of the object is the cohomology of the site. -/
def cohomologyPresheafObjIsoH (F : Sheaf J AddCommGrpCat.{v}) :
    Sheaf.H' F n T ≅ AddCommGrpCat.of (Sheaf.H F n) :=
  (cohomologyPresheafEvaluationIsoFunctorH J n hT).app F

/-- At a terminal object, the cohomology of the object is the cohomology of the site. -/
def cohomologyPresheafObjAddEquivH (F : Sheaf J AddCommGrpCat.{v}) :
    Sheaf.H' F n T ≃+ Sheaf.H F n :=
  (cohomologyPresheafObjIsoH n hT F).addCommGroupIsoToAddEquiv

end

end CategoryTheory

end TauCeti
