/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
public import TauCeti.AlgebraicGeometry.LineBundle.Basic

/-!
# Finitely presented sheaves on schemes

This file packages Mathlib's finite-presentation condition for sheaves of modules as a full
subcategory on an arbitrary scheme. On a locally Noetherian scheme this supplies the objects used
in the standard coherent-sheaf notion.

The main declarations are:

* `TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X`, the full subcategory of finitely
  presented objects in `X.Modules`;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.toFinitelyPresented`, the fully faithful inclusion
  of invertible sheaves into finitely presented sheaves.

The inclusion uses the site-level theorem that an invertible sheaf is finitely presented: its
rank-one local trivializations give finite generators and have no relations. Thus the existing
Layer A line-bundle objects can be consumed by the coherent-cohomology theory planned in Layer B.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, item "Coherent sheaves and
cohomology `Hⁱ(X, ℱ)`", while supplying the direct bridge from Layer A's invertible sheaves.
No formalization is vendored. The definition reuses Mathlib's
`SheafOfModules.IsFinitePresentation` and `ObjectProperty.FullSubcategory`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

/-- The full category of finitely presented sheaves of modules on a scheme. -/
abbrev FinitelyPresentedSheaf (X : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf)

namespace FinitelyPresentedSheaf

variable {X : Scheme.{u}}

/-- The underlying sheaf of a finitely presented sheaf is finitely presented. -/
instance (F : FinitelyPresentedSheaf X) : F.obj.IsFinitePresentation :=
  F.property

end FinitelyPresentedSheaf

namespace InvertibleSheaf

variable {X : Scheme.{u}}

/-- The fully faithful inclusion of invertible sheaves into finitely presented sheaves. -/
abbrev toFinitelyPresented (X : Scheme.{u}) :
    InvertibleSheaf X ⥤ FinitelyPresentedSheaf X :=
  ObjectProperty.ιOfLE fun M hM ↦ by
    let : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := hM
    exact TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := M)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
