/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible sheaves

This file begins the scheme-level line-bundle lane of the Jacobian challenge. An invertible
sheaf on a scheme `X` is an `𝒪_X`-module which is locally free of rank one.

Mathlib's `SheafOfModules.IsLocallyFree` remembers local generating families but deliberately
allows their ranks to vary. We refine its local data by requiring each local generating type to
have exactly one element:

* `SheafOfModules.LocalGeneratorsData.IsInvertible q` says that every presentation
  `free (q.generators i).I ⟶ M.over (q.X i)` is an isomorphism and that each indexing type is
  nonempty and a subsingleton;
* `SheafOfModules.IsInvertible M` says that such data exists for the `𝒪_X`-module `M`;
* `SheafOfModules.isInvertible X` is the corresponding `ObjectProperty`, and `InvertibleSheaf X`
  is the full subcategory of `X.Modules` that it cuts out.

The predicate implies Mathlib's local-freeness (and hence quasi-coherence). Local generator data
transports along an isomorphism of `𝒪_X`-modules by
`SheafOfModules.LocalGeneratorsData.ofIso` (which rests on
`SheafOfModules.GeneratingSections.isIso_ofEpi_π`, recording that pushing a free family of
generating sections along an isomorphism keeps it free), so invertibility is closed under
isomorphisms and `ObjectProperty.prop_of_iso` and `ObjectProperty.prop_iff_of_iso` apply to it.
Every free sheaf whose indexing type is nonempty and a subsingleton is invertible; in particular
`InvertibleSheaf.trivial X` supplies the globally free rank-one sheaf.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`". The tensor product and Picard group require a
monoidal structure on sheaves of modules and are left to subsequent files. No formalization is
vendored. The construction reuses Mathlib's `SheafOfModules.LocalGeneratorsData`,
`IsLocallyFreeData`, and `IsLocallyFree` API from
`Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

section

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pushing a free family of generating sections along an isomorphism again gives a free family
of generating sections. -/
instance GeneratingSections.isIso_ofEpi_π {P Q : SheafOfModules.{u} R}
    (σ : P.GeneratingSections) (p : P ⟶ Q) [IsIso p] [IsIso σ.π] :
    IsIso (σ.ofEpi p).π := by
  have h : IsIso (σ.π ≫ p) := inferInstance
  simp only [SheafOfModules.GeneratingSections.ofEpi_π]
  exact h

end

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Local generators exhibit a sheaf of modules as invertible when they freely generate it
on a cover and every local generating type has exactly one element. -/
structure LocalGeneratorsData.IsInvertible
    (q : SheafOfModules.LocalGeneratorsData.{u} M) : Prop where
  /-- The local generators freely generate the restricted sheaf. -/
  isLocallyFreeData : q.IsLocallyFreeData
  /-- Every local free basis has at least one element. -/
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  /-- Every local free basis has at most one element. -/
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

/-- An `𝒪_X`-module is an invertible sheaf if it is locally free of rank one. The witness is
local generator data whose free presentations are isomorphisms and whose basis types have
exactly one element. -/
class IsInvertible (M : X.Modules) : Prop where
  /-- A rank-one local trivialization of the sheaf. -/
  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, LocalGeneratorsData.IsInvertible q

/-- An invertible sheaf is locally free. -/
instance IsInvertible.isLocallyFree (M : X.Modules) [h : IsInvertible M] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  letI := hq.isLocallyFreeData
  exact q.isLocallyFree

variable (X) in
/-- The object property of being an invertible sheaf. -/
abbrev isInvertible : ObjectProperty X.Modules := IsInvertible

/-- Transport local generator data along an isomorphism of `𝒪_X`-modules: the same cover, with
each family of local generators pushed forward along the restricted isomorphism. -/
def LocalGeneratorsData.ofIso (q : SheafOfModules.LocalGeneratorsData.{u} M) (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData.{u} N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi
    ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e).hom

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    obtain ⟨q, hq⟩ := hM.exists_isInvertible
    refine ⟨⟨LocalGeneratorsData.ofIso q e, ?_, fun i => hq.basisNonempty i,
      fun i => hq.basisSubsingleton i⟩⟩
    refine { isIso := fun i => ?_ }
    haveI : IsIso (q.generators i).π := hq.isLocallyFreeData.isIso i
    exact GeneratingSections.isIso_ofEpi_π (q.generators i) _

/-- A free sheaf whose indexing type has exactly one element is an invertible sheaf. -/
instance free_isInvertible (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (SheafOfModules.free (R := X.ringCatSheaf) I) where
  exists_isInvertible :=
    ⟨(SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData,
      { isLocallyFreeData := inferInstance
        basisNonempty := fun _ => by simpa using ‹Nonempty I›
        basisSubsingleton := fun _ => by simpa using ‹Subsingleton I› }⟩

end SheafOfModules

variable {X : Scheme.{u}}

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.IsInvertible L.obj :=
  L.property

/-- The invertible sheaf given by the free sheaf on an indexing type with exactly one element. -/
@[expose]
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

@[simp]
lemma free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  rfl

/-- The globally free rank-one invertible sheaf. -/
@[expose]
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  rfl

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
