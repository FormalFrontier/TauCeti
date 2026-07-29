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
have exactly one element. Nothing in that refinement is specific to schemes, so it is stated for
a sheaf of modules over an arbitrary site:

* `SheafOfModules.LocalGeneratorsData.IsInvertible q` says that every presentation
  `free (q.generators i).I ⟶ M.over (q.X i)` is an isomorphism and that each indexing type is
  nonempty and a subsingleton;
* `SheafOfModules.IsInvertible M` says that such data exists for the sheaf of modules `M`;
* `SheafOfModules.LocalGeneratorsData.ofIso` transports local generator data along an isomorphism
  of sheaves of modules, and `SheafOfModules.IsInvertible.of_iso` transports invertibility along
  one.

Only the packaging is scheme-level: `SheafOfModules.isInvertible X` is the `ObjectProperty` on
`X.Modules` cut out by the predicate (closed under isomorphisms, by the transport theorem, so
`ObjectProperty.prop_of_iso` and `ObjectProperty.prop_iff_of_iso` apply to it), and
`InvertibleSheaf X` is the full subcategory it cuts out.

The predicate implies Mathlib's local-freeness (and hence quasi-coherence). Every free sheaf whose
indexing type is nonempty and a subsingleton is invertible; in particular
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

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ Y : C, HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

/-- Local generators exhibit a sheaf of modules as invertible when they freely generate it
on a cover and every local generating type has exactly one element. -/
structure LocalGeneratorsData.IsInvertible (q : SheafOfModules.LocalGeneratorsData M) : Prop where
  /-- The local generators freely generate the restricted sheaf. -/
  isLocallyFreeData : q.IsLocallyFreeData
  /-- Every local free basis has at least one element. -/
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  /-- Every local free basis has at most one element. -/
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

variable (M) in
/-- A sheaf of modules is invertible if it is locally free of rank one. The witness is
local generator data whose free presentations are isomorphisms and whose basis types have
exactly one element. -/
class IsInvertible : Prop where
  /-- A rank-one local trivialization of the sheaf. -/
  exists_isInvertible :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u₁} M, LocalGeneratorsData.IsInvertible q

/-- An invertible sheaf is locally free. -/
instance IsInvertible.isLocallyFree (M : SheafOfModules.{u} R) [h : IsInvertible M] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  letI := hq.isLocallyFreeData
  exact q.isLocallyFree

/-- Transport local generator data along an isomorphism of sheaves of modules: the same cover, with
each family of local generators pushed forward along the restricted isomorphism. -/
@[expose, simps]
def LocalGeneratorsData.ofIso (q : SheafOfModules.LocalGeneratorsData M) (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData N where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.generators i).ofEpi ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom

/-- Rank-one local generator data stays rank one after transport along an isomorphism. -/
theorem LocalGeneratorsData.IsInvertible.ofIso {q : SheafOfModules.LocalGeneratorsData M}
    (hq : LocalGeneratorsData.IsInvertible q) (e : M ≅ N) :
    LocalGeneratorsData.IsInvertible (LocalGeneratorsData.ofIso q e) where
  isLocallyFreeData :=
    { isIso := by
        -- `ofIso` leaves the index type of the cover untouched, so the index may be taken in
        -- `q.I`; each transported presentation is then a composite of two isomorphisms.
        change ∀ i : q.I, IsIso ((q.generators i).ofEpi
          ((SheafOfModules.overFunctor R (q.X i)).mapIso e).hom).π
        intro i
        rw [SheafOfModules.GeneratingSections.ofEpi_π]
        exact IsIso.comp_isIso' (hq.isLocallyFreeData.isIso i) inferInstance }
  basisNonempty i := by
    simpa only [LocalGeneratorsData.ofIso_generators,
      SheafOfModules.GeneratingSections.ofEpi_I] using hq.basisNonempty i
  basisSubsingleton i := by
    simpa only [LocalGeneratorsData.ofIso_generators,
      SheafOfModules.GeneratingSections.ofEpi_I] using hq.basisSubsingleton i

/-- Invertibility transports along an isomorphism of sheaves of modules. -/
theorem IsInvertible.of_iso (e : M ≅ N) [h : IsInvertible M] : IsInvertible N := by
  obtain ⟨q, hq⟩ := h.exists_isInvertible
  exact ⟨LocalGeneratorsData.ofIso q e, hq.ofIso e⟩

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}] [Limits.HasBinaryProducts C]
  [HasSheafify J AddCommGrpCat]

/-- A free sheaf whose indexing type has exactly one element is an invertible sheaf. -/
instance free_isInvertible (I : Type u) [Nonempty I] [Subsingleton I] :
    IsInvertible (SheafOfModules.free (R := R) I) where
  exists_isInvertible :=
    ⟨(SheafOfModules.free.generatingSections (R := R) I).localGeneratorsData,
      { isLocallyFreeData := inferInstance
        basisNonempty := fun _ => by
          simpa only [SheafOfModules.GeneratingSections.localGeneratorsData_generators,
            SheafOfModules.GeneratingSections.map_I,
            SheafOfModules.free.generatingSections_I] using ‹Nonempty I›
        basisSubsingleton := fun _ => by
          simpa only [SheafOfModules.GeneratingSections.localGeneratorsData_generators,
            SheafOfModules.GeneratingSections.map_I,
            SheafOfModules.free.generatingSections_I] using ‹Subsingleton I› }⟩

end

end

variable (X : Scheme.{u})

/-- The object property of being an invertible sheaf on a scheme. -/
abbrev isInvertible : ObjectProperty X.Modules := IsInvertible (R := X.ringCatSheaf)

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    haveI := hM
    exact IsInvertible.of_iso (R := X.ringCatSheaf) e

end SheafOfModules

variable {X : Scheme.{u}}

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  L.property

/-- The invertible sheaf given by the free sheaf on an indexing type with exactly one element. -/
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

@[simp]
lemma free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The globally free rank-one invertible sheaf. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
