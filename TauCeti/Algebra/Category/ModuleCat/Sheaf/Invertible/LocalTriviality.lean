/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.Basic

/-!
# Local trivializations of invertible sheaves

An invertible sheaf is locally free on a one-element basis. This file turns the
singleton-indexed free presentations in `SheafOfModules.IsInvertible` into the standard
geometric formulation: on every member of a cover, the sheaf is isomorphic to the free sheaf
on `PUnit`.

The structure `SheafOfModules.LocalTrivializations M` records such a cover and its
trivializing isomorphisms. The two formulations are equivalent:

* `LocalGeneratorsData.IsInvertible.trivializationIso` standardizes each rank-one free
  presentation;
* `LocalTrivializations.isInvertible` recovers the local-generator formulation;
* `LocalTrivializations.ofIsInvertible` constructs local trivializations from an invertible
  sheaf;
* `LocalTrivializations.nonempty_iff_isInvertible` characterizes invertibility by the existence
  of local trivializations.

This supplies the local-triviality interface for
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a scheme; the
Picard group `Pic X` under `⊗`". It is the form needed to prove that tensor products and duals
of invertible sheaves remain invertible. The construction reuses Mathlib's free-sheaf functor
and `LocalGeneratorsData`; no formalization is vendored.
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
  {M : SheafOfModules.{u} R}

/-- A local trivialization atlas for a sheaf of modules. It consists of a cover of the terminal
object and, over every member of the cover, an isomorphism from the standard free rank-one
sheaf to the restriction of `M`. -/
structure LocalTrivializations (M : SheafOfModules.{u} R) where
  /-- The indexing type of the trivializing cover. -/
  I : Type u₁
  /-- The objects of the trivializing cover. -/
  X : I → C
  /-- The chosen objects cover the terminal object. -/
  coversTop : J.CoversTop X
  /-- The isomorphism from the standard free rank-one sheaf to `M` on each member of the
  cover. -/
  iso (i : I) :
    _root_.SheafOfModules.free (R := R.over (X i)) PUnit ≅ M.over (X i)

namespace LocalGeneratorsData.IsInvertible

/-- The local free basis of an invertible sheaf is equivalent to the standard singleton type
`PUnit`. -/
def basisEquiv {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    PUnit ≃ (q.generators i).I where
  toFun _ := hq.basisNonempty i |>.some
  invFun _ := PUnit.unit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := hq.basisSubsingleton i |>.elim _ _

/-- The isomorphism supplied by a local free presentation of an invertible sheaf. -/
def presentationIso {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) (q.generators i).I ≅
      M.over (q.X i) :=
  @asIso _ _ _ _ (q.generators i).π (hq.isLocallyFreeData.isIso i)

/-- The forward map of the presentation isomorphism is the original local free
presentation. -/
@[simp]
lemma presentationIso_hom {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    (hq.presentationIso i).hom = (q.generators i).π :=
  (rfl)

/-- A rank-one free presentation on a member of a cover, standardized to an isomorphism from
the free sheaf on `PUnit`. -/
def trivializationIso {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    _root_.SheafOfModules.free (R := R.over (q.X i)) PUnit ≅ M.over (q.X i) :=
  ((_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).mapIso
    (hq.basisEquiv i).toIso).trans (hq.presentationIso i)

/-- The forward map of the standardized trivialization is the relabelling of the free basis,
followed by the original local free presentation. -/
@[simp]
lemma trivializationIso_hom {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (i : q.I) :
    (hq.trivializationIso i).hom =
      (_root_.SheafOfModules.freeFunctor (R := R.over (q.X i))).map
        (hq.basisEquiv i).toIso.hom ≫
        (q.generators i).π :=
  (rfl)

end LocalGeneratorsData.IsInvertible

namespace LocalTrivializations

/-- Local trivializations exhibit a sheaf as invertible. -/
theorem isInvertible (t : LocalTrivializations M) : IsInvertible M := by
  refine ⟨?_, ?_⟩
  · exact
      { I := t.I
        X := t.X
        coversTop := t.coversTop
        generators i :=
          (_root_.SheafOfModules.free.generatingSections
            (R := R.over (t.X i)) PUnit).ofEpi (t.iso i).hom }
  refine
    { isLocallyFreeData :=
        { isIso := fun i ↦ ?_ }
      basisNonempty := fun i ↦ ?_
      basisSubsingleton := fun i ↦ ?_ }
  · dsimp at i ⊢
    simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_π,
      _root_.SheafOfModules.free.generatingSections_I,
      _root_.SheafOfModules.free.generatingSections_π, Category.id_comp] using
      inferInstanceAs (IsIso (t.iso i).hom)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Nonempty PUnit)
  · simpa only [_root_.SheafOfModules.GeneratingSections.ofEpi_I,
      _root_.SheafOfModules.free.generatingSections_I] using
      inferInstanceAs (Subsingleton PUnit)

/-- Every invertible sheaf admits local trivializations by the standard free rank-one sheaf. -/
def ofIsInvertible (M : SheafOfModules.{u} R) [hM : IsInvertible M] :
    LocalTrivializations M := by
  let q := hM.exists_isInvertible.choose
  let hq := hM.exists_isInvertible.choose_spec
  exact
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      iso i := hq.trivializationIso i }

/-- A sheaf of modules is invertible exactly when it admits a local trivialization atlas by
the standard free rank-one sheaf. -/
theorem nonempty_iff_isInvertible :
    Nonempty (LocalTrivializations M) ↔ IsInvertible M := by
  constructor
  · rintro ⟨t⟩
    exact t.isInvertible
  · intro hM
    letI := hM
    exact ⟨ofIsInvertible M⟩

end LocalTrivializations

end SheafOfModules

end

end TauCeti
