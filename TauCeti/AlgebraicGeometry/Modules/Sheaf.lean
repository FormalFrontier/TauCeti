/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The underlying abelian sheaf of a sheaf of modules on a scheme

Mathlib packages the forgetful functors out of the category `X.Modules` of `𝒪_X`-modules on a
scheme that land in presheaves: `AlgebraicGeometry.Scheme.Modules.toPresheafOfModules` and
`AlgebraicGeometry.Scheme.Modules.toPresheaf`. This file adds the one that lands in abelian
sheaves, and records that it is exact.

## Main declarations

* `TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf`, the functor sending an `𝒪_X`-module to its
  underlying sheaf of abelian groups, with instances saying that it is additive and preserves
  finite limits and finite colimits;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.shortExact_map_toSheaf`: a short exact sequence of
  `𝒪_X`-modules stays short exact after forgetting the module structures.

`TauCeti/AlgebraicGeometry/Cohomology/Basic.lean` defines the cohomology of an `𝒪_X`-module as
the sheaf cohomology of its underlying abelian sheaf, so this exactness is what puts that
cohomology into a long exact sequence; it is Layer B infrastructure for
`TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is vendored: the functor is
Mathlib's `SheafOfModules.toSheaf` for the sheaf of rings `X.ringCatSheaf`, and its exactness is
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Exactness.lean`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable (X : Scheme.{u})

/-- The forgetful functor from `𝒪_X`-modules to sheaves of abelian groups on `X`.

This is `SheafOfModules.toSheaf` for the sheaf of rings `X.ringCatSheaf`, packaged so that the
source is the category `X.Modules`; compare `AlgebraicGeometry.Scheme.Modules.toPresheaf`. -/
@[expose]
def toSheaf : X.Modules ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf

instance : (toSheaf X).Additive :=
  inferInstanceAs (_root_.SheafOfModules.toSheaf X.ringCatSheaf).Additive

instance : PreservesFiniteLimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteLimits (_root_.SheafOfModules.toSheaf X.ringCatSheaf))

instance : PreservesFiniteColimits (toSheaf X) :=
  inferInstanceAs (PreservesFiniteColimits (_root_.SheafOfModules.toSheaf X.ringCatSheaf))

variable {X}

/-- Forgetting the module structures of a short exact sequence of `𝒪_X`-modules leaves a short
exact sequence of sheaves of abelian groups. -/
theorem shortExact_map_toSheaf {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    (S.map (toSheaf X)).ShortExact :=
  hS.map_of_exact _

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
