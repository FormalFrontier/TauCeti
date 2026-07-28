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

* `IsInvertibleData q` says that every presentation
  `free (q.generators i).I ⟶ M.over (q.X i)` is an isomorphism and that each indexing type is
  unique;
* `IsInvertibleSheaf M` says that such data exists for the `𝒪_X`-module `M`;
* `InvertibleSheaf X` is the full subcategory of `X.Modules` on the invertible sheaves.

The predicate implies Mathlib's local-freeness (and hence quasi-coherence), and contains every
free sheaf on a unique indexing type. In particular, `InvertibleSheaf.trivial X` supplies the
globally free rank-one sheaf.

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

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Local generators exhibit a sheaf of modules as invertible when they freely generate it
on a cover and every local generating type has exactly one element. -/
structure IsInvertibleData
    (q : SheafOfModules.LocalGeneratorsData.{u} M) : Prop where
  /-- The local generators freely generate the restricted sheaf. -/
  isLocallyFreeData : q.IsLocallyFreeData
  /-- Every local free basis has at least one element. -/
  basisNonempty (i : q.I) : Nonempty (q.generators i).I
  /-- Every local free basis has at most one element. -/
  basisSubsingleton (i : q.I) : Subsingleton (q.generators i).I

/-- An `𝒪_X`-module is an invertible sheaf if it is locally free of rank one. The witness is
local generator data whose free presentations are isomorphisms and whose basis types are unique. -/
class IsInvertibleSheaf (M : X.Modules) : Prop where
  /-- A rank-one local trivialization of the sheaf. -/
  exists_isInvertibleData :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, IsInvertibleData q

namespace IsInvertibleSheaf

/-- Invertibility is equivalent to the existence of rank-one locally free data. -/
lemma iff_exists_isInvertibleData (M : X.Modules) :
    IsInvertibleSheaf M ↔
      ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, IsInvertibleData q :=
  ⟨fun h => h.exists_isInvertibleData, fun h => ⟨h⟩⟩

/-- An invertible sheaf is locally free. -/
instance isLocallyFree (M : X.Modules) [h : IsInvertibleSheaf M] :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := h.exists_isInvertibleData
  letI := hq.isLocallyFreeData
  exact q.isLocallyFree

end IsInvertibleSheaf

/-- The object property of being an invertible sheaf. -/
def isInvertibleSheaf (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun M => IsInvertibleSheaf M

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (isInvertibleSheaf X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : IsInvertibleSheaf L.obj :=
  by exact L.property

/-- The underlying `𝒪_X`-module of an invertible sheaf. -/
noncomputable abbrev toModule (L : InvertibleSheaf X) : X.Modules :=
  L.obj

/-- A free sheaf on a unique indexing type is an invertible sheaf. -/
instance free_isInvertibleSheaf (X : Scheme.{u}) (I : Type u) [Unique I] :
    IsInvertibleSheaf (SheafOfModules.free (R := X.ringCatSheaf) I) where
  exists_isInvertibleData := by
    let q :=
      (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) I).localGeneratorsData
    refine ⟨q, ?_⟩
    exact
      { isLocallyFreeData := inferInstance
        basisNonempty := fun _ => by
          change Nonempty I
          exact inferInstance
        basisSubsingleton := fun _ => by
          change Subsingleton I
          exact inferInstance }

/-- The free invertible sheaf with a basis indexed by a unique type. -/
def freeOfUnique (X : Scheme.{u}) (I : Type u) [Unique I] : InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, by
    change IsInvertibleSheaf _
    infer_instance⟩

@[simp]
lemma freeOfUnique_obj (X : Scheme.{u}) (I : Type u) [Unique I] :
    (freeOfUnique X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The globally free rank-one invertible sheaf. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  freeOfUnique X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
