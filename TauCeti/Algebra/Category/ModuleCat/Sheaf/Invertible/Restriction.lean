/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restricting local trivializations

A local trivialization of a sheaf of modules over an object `X` remains a trivialization after
restriction along a morphism `f : Y ⟶ X`. This file packages that elementary but necessary
step for the local-triviality formulation of invertible sheaves.

## Main declarations

* `SheafOfModules.overMapFreePUnitIso` identifies the restriction of the standard free
  rank-one sheaf over `X` with the standard free rank-one sheaf over `Y`;
* `SheafOfModules.LocalTrivializations.isoOver` restricts one chosen trivialization in an atlas
  along a morphism into its covering object;
* `SheafOfModules.LocalTrivializations.ofRefinement` transports an entire atlas to any cover
  equipped with refinement arrows into the original cover.

The common refinement of two atlases can therefore carry both sets of trivializations on the
same cover. Together with compatibility of tensor products with restriction, this is the final
local-triviality input for closure of invertible sheaves under tensor product. That closure is
needed for the Picard group in `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item
"Invertible sheaves on a scheme; the Picard group `Pic X` under `⊗`".

No formalization is vendored. The construction reuses Mathlib's `SheafOfModules.overMap`,
`SheafOfModules.overFunctorMap`, and `SheafOfModules.overMapUnitIso`, and the standard
free-rank-one/tensor-unit comparison already in Tau Ceti.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction along `f : Y ⟶ X` carries the standard free rank-one sheaf over `X` to the
standard free rank-one sheaf over `Y`.

For one generator this follows directly by identifying both free sheaves with their tensor
units and using Mathlib's canonical comparison for restriction of the unit. -/
def overMapFreePUnitIso {X Y : C} (f : Y ⟶ X) :
    (_root_.SheafOfModules.overMap R f).obj
        (_root_.SheafOfModules.free (R := R.over X) PUnit) ≅
      _root_.SheafOfModules.free (R := R.over Y) PUnit :=
  (_root_.SheafOfModules.overMap R f).mapIso
      (freePUnitIsoUnit (R.over X) :
        _root_.SheafOfModules.free (R := R.over X) PUnit ≅
          _root_.SheafOfModules.unit (R.over X)) ≪≫
    _root_.SheafOfModules.overMapUnitIso (R := R) f ≪≫
      (freePUnitIsoUnit (R.over Y) :
        _root_.SheafOfModules.free (R := R.over Y) PUnit ≅
          _root_.SheafOfModules.unit (R.over Y)).symm

namespace LocalTrivializations

variable {M : SheafOfModules.{u} R}

/-- Restrict one member of a local trivialization atlas along a morphism into its covering
object. The resulting isomorphism trivializes `M` over the source of that morphism. -/
def isoOver (t : LocalTrivializations M) (i : t.I) {Y : C} (f : Y ⟶ t.X i) :
    _root_.SheafOfModules.free (R := R.over Y) PUnit ≅ M.over Y :=
  (overMapFreePUnitIso (R := R) f).symm ≪≫
    (_root_.SheafOfModules.overMap R f).mapIso (t.iso i) ≪≫
      (_root_.SheafOfModules.overFunctorMap R f).app M

/-- Replace the cover of a local trivialization atlas by a refining cover.

Each object `Y j` of the new cover is equipped with a chosen arrow into an object of the old
cover. Restricting the corresponding old trivialization along that arrow supplies the new one. -/
def ofRefinement (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    LocalTrivializations M where
  I := I
  X := Y
  coversTop := coversTop
  iso j := t.isoOver (index j) (map j)

/-- Refining a local trivialization atlas uses the indexing type of the refining cover. -/
@[simp]
lemma ofRefinement_I (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    (t.ofRefinement Y coversTop index map).I = I :=
  (rfl)

/-- The covering objects of a refined local trivialization atlas are the specified refining
objects. -/
@[simp]
lemma ofRefinement_X (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j)) :
    (t.ofRefinement Y coversTop index map).X =
      fun j ↦ Y ((ofRefinement_I t Y coversTop index map).mp j) :=
  (rfl)

/-- The trivializations of a refined atlas are obtained by restricting the chosen old
trivializations along the refinement arrows. -/
@[simp]
lemma ofRefinement_iso (t : LocalTrivializations M) {I : Type u₁} (Y : I → C)
    (coversTop : J.CoversTop Y) (index : I → t.I) (map : ∀ j, Y j ⟶ t.X (index j))
    (j : (t.ofRefinement Y coversTop index map).I) :
    (t.ofRefinement Y coversTop index map).iso j =
      cast (by rw [ofRefinement_X])
        (t.isoOver (index ((ofRefinement_I t Y coversTop index map).mp j))
          (map ((ofRefinement_I t Y coversTop index map).mp j))) :=
  (rfl)

end LocalTrivializations

end SheafOfModules

end

end TauCeti
