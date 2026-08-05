/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.FinitePresentation
public import TauCeti.AlgebraicGeometry.LineBundle.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Coherent sheaves on schemes

This file introduces coherent sheaves on a locally Noetherian scheme using Mathlib's
finite-presentation condition for sheaves of modules. On a locally Noetherian scheme this is the
standard coherent-sheaf notion used for coherent cohomology.

The main declarations are:

* `TauCeti.AlgebraicGeometry.SheafOfModules.isCoherent X`, the object property of finite
  presentation on `X.Modules`;
* `TauCeti.AlgebraicGeometry.CoherentSheaf X`, its full subcategory;
* `TauCeti.AlgebraicGeometry.InvertibleSheaf.toCoherent`, the fully faithful inclusion of
  invertible sheaves into coherent sheaves.

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

namespace SheafOfModules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The object property of being a coherent sheaf on a locally Noetherian scheme. -/
abbrev isCoherent : ObjectProperty X.Modules :=
  _root_.SheafOfModules.isFinitePresentation X.ringCatSheaf

end SheafOfModules

/-- The full category of coherent sheaves on a locally Noetherian scheme. -/
abbrev CoherentSheaf (X : Scheme.{u}) [IsLocallyNoetherian X] :=
  ObjectProperty.FullSubcategory (SheafOfModules.isCoherent X)

namespace CoherentSheaf

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The underlying sheaf of a coherent sheaf is finitely presented. -/
instance (F : CoherentSheaf X) : F.obj.IsFinitePresentation :=
  F.property

end CoherentSheaf

namespace InvertibleSheaf

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- The fully faithful inclusion of invertible sheaves into coherent sheaves. -/
abbrev toCoherent (X : Scheme.{u}) [IsLocallyNoetherian X] :
    InvertibleSheaf X ⥤ CoherentSheaf X :=
  ObjectProperty.ιOfLE fun M hM ↦ by
    let : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) M := hM
    exact TauCeti.SheafOfModules.IsInvertible.isFinitePresentation (M := M)

end InvertibleSheaf

end

end AlgebraicGeometry

end TauCeti
