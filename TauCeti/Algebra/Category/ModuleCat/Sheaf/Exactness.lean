/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Forgetting the module structure of a sheaf of modules is exact

Let `R` be a sheaf of rings on a site `(C, J)`. Mathlib's `SheafOfModules.toSheaf R` sends a
sheaf of `R`-modules to its underlying abelian sheaf, and knows that this functor preserves and
reflects finite limits. This file supplies the missing half: it preserves finite colimits as
well, hence carries short exact sequences of sheaves of modules to short exact sequences of
abelian sheaves.

## Main declarations

* `TauCeti.SheafOfModules.preservesFiniteColimits_toSheaf`: `SheafOfModules.toSheaf` preserves
  finite colimits;
* `TauCeti.SheafOfModules.shortExact_map_toSheaf`: a short exact sequence of sheaves of modules
  stays short exact after forgetting the module structures.

The proof is a transfer along the sheafification of presheaves of modules. That functor is a
left adjoint whose counit is an isomorphism, and composing it with `SheafOfModules.toSheaf`
gives `PresheafOfModules.toPresheaf ⋙ presheafToSheaf`, which preserves finite colimits because
colimits of presheaves of modules are computed sectionwise and `presheafToSheaf` is a left
adjoint.

Exactness of `SheafOfModules.toSheaf` is what makes the cohomology of a sheaf of modules, which
is defined through the underlying abelian sheaf, fit into a long exact sequence; see
`TauCeti/AlgebraicGeometry/Cohomology/LongExactSequence.lean`. It is therefore Layer B
infrastructure for `TauCetiRoadmap/JacobianChallenge/README.md`. No formalization is vendored:
the ingredients are Mathlib's `PresheafOfModules.sheafificationAdjunction`,
`PresheafOfModules.sheafificationCompToSheaf` and `ShortComplex.ShortExact.map_of_exact`.
-/

public section

open CategoryTheory Limits

universe v v' u u'

noncomputable section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace TauCeti

namespace SheafOfModules

open _root_.SheafOfModules

instance preservesFiniteColimits_toSheaf :
    PreservesFiniteColimits (toSheaf.{v} R) := by
  constructor
  intro D _ _
  have hLF : PreservesColimitsOfShape D
      (PresheafOfModules.sheafification.{v} (𝟙 R.obj) ⋙ toSheaf.{v} R) :=
    preservesColimitsOfShape_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf.{v} (𝟙 R.obj)).symm
  constructor
  intro K
  -- The counit isomorphism exhibits every diagram of sheaves of modules as the sheafification
  -- of a diagram of presheaves of modules, on which both `L` and `L ⋙ toSheaf R` preserve
  -- colimits.
  set L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
  set G := forget.{v} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  have e : (K ⋙ G) ⋙ L ≅ K :=
    Functor.isoWhiskerLeft K
        (asIso (PresheafOfModules.sheafificationAdjunction.{v} (𝟙 R.obj)).counit) ≪≫
      K.rightUnitor
  have h₁ := isColimitOfPreserves L (colimit.isColimit (K ⋙ G))
  have h₂ := isColimitOfPreserves (L ⋙ toSheaf.{v} R) (colimit.isColimit (K ⋙ G))
  have := preservesColimit_of_preserves_colimit_cocone (F := toSheaf.{v} R) h₁ h₂
  exact preservesColimit_of_iso_diagram _ e

/-- Forgetting the module structures of a short exact sequence of sheaves of modules leaves a
short exact sequence of abelian sheaves. -/
theorem shortExact_map_toSheaf {S : ShortComplex (_root_.SheafOfModules.{v} R)}
    (hS : S.ShortExact) : (S.map (toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _

end SheafOfModules

end TauCeti

end
