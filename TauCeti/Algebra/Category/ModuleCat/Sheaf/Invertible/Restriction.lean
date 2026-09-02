/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.CategoryTheory.Sites.CoversTop
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
* `SheafOfModules.CommonRefinementPair.ofRefinement` transports two atlases to a supplied common
  refinement, and `SheafOfModules.CommonRefinementPair.of` uses the canonical one.

The common refinement of two atlases can therefore carry both sets of trivializations on the
same cover. Together with compatibility of tensor products with restriction, this is the final
local-triviality input for closure of invertible sheaves under tensor product. That closure is
needed for the Picard group in `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item
"Invertible sheaves on a scheme; the Picard group `Pic X` under `⊗`". The tensor/restriction
comparison itself is deliberately not asserted here: it belongs with the sheafified tensor
product API, where its construction and coherence can be reviewed independently.

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

variable {M N : SheafOfModules.{u} R}

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

variable {M N : SheafOfModules.{u} R}

/-- Two local-trivialization atlases on the same cover.

The two iso families are indexed by the same `I` and cover `X`, so the shared-cover data is part
of the result rather than an equality between two independently constructed atlases. -/
structure CommonRefinementPair (M N : SheafOfModules.{u} R) where
  /-- The indexing type of the common cover. -/
  I : Type u₁
  /-- The objects of the common cover. -/
  X : I → C
  /-- The common cover of the terminal object. -/
  coversTop : J.CoversTop X
  /-- The first sheaf's trivialization on each member of the common cover. -/
  fstIso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)
  /-- The second sheaf's trivialization on each member of the common cover. -/
  sndIso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ N.over (X i)

/-- The first atlas in a common-refinement pair. -/
abbrev CommonRefinementPair.fst (p : CommonRefinementPair M N) :
    LocalTrivializations M where
  I := p.I
  X := p.X
  coversTop := p.coversTop
  iso := p.fstIso

/-- The second atlas in a common-refinement pair. -/
abbrev CommonRefinementPair.snd (p : CommonRefinementPair M N) :
    LocalTrivializations N where
  I := p.I
  X := p.X
  coversTop := p.coversTop
  iso := p.sndIso

/-- The first atlas uses the pair's indexing type. -/
@[simp]
lemma CommonRefinementPair.fst_I (p : CommonRefinementPair M N) : p.fst.I = p.I := (rfl)

/-- The first atlas uses the pair's covering objects. -/
@[simp]
lemma CommonRefinementPair.fst_X (p : CommonRefinementPair M N) : p.fst.X = p.X := (rfl)

/-- The first atlas uses the pair's trivializing isomorphisms. -/
@[simp]
lemma CommonRefinementPair.fst_iso (p : CommonRefinementPair M N) (i : p.I) :
    p.fst.iso i = p.fstIso i := (rfl)

/-- The second atlas uses the pair's indexing type. -/
@[simp]
lemma CommonRefinementPair.snd_I (p : CommonRefinementPair M N) : p.snd.I = p.I := (rfl)

/-- The second atlas uses the pair's covering objects. -/
@[simp]
lemma CommonRefinementPair.snd_X (p : CommonRefinementPair M N) : p.snd.X = p.X := (rfl)

/-- The second atlas uses the pair's trivializing isomorphisms. -/
@[simp]
lemma CommonRefinementPair.snd_iso (p : CommonRefinementPair M N) (i : p.I) :
    p.snd.iso i = p.sndIso i := (rfl)

namespace CommonRefinementPair

/-- Transport two local-trivialization atlases to a supplied common refinement.

The two transported iso families are obtained from the existing `ofRefinement` construction. -/
def ofRefinement (t : LocalTrivializations M) (s : LocalTrivializations N)
    (r : GrothendieckTopology.CoversTop.CommonRefinement J t.X s.X) :
    CommonRefinementPair M N where
  I := r.I
  X := r.X
  coversTop := r.coversTop
  fstIso := (t.ofRefinement r.X r.coversTop r.leftIndex r.left).iso
  sndIso := (s.ofRefinement r.X r.coversTop r.rightIndex r.right).iso

/-- Transport two local-trivialization atlases to the canonical common refinement of their covers.

This uses `GrothendieckTopology.CoversTop.commonRefinement`; use `ofRefinement` when the
refinement data is supplied by another construction. -/
noncomputable def of (t : LocalTrivializations M) (s : LocalTrivializations N) :
    CommonRefinementPair M N :=
  ofRefinement t s
    (GrothendieckTopology.CoversTop.commonRefinement t.coversTop s.coversTop)

end CommonRefinementPair

namespace IsInvertible

/-- Two invertible sheaves admit local trivializations on one common cover. -/
theorem nonempty_commonRefinementPair (M N : SheafOfModules.{u} R) [IsInvertible M]
    [IsInvertible N] : Nonempty (CommonRefinementPair M N) := by
  exact ⟨CommonRefinementPair.of (LocalTrivializations.ofIsInvertible M)
    (LocalTrivializations.ofIsInvertible N)⟩

end IsInvertible

end SheafOfModules

end

end TauCeti
