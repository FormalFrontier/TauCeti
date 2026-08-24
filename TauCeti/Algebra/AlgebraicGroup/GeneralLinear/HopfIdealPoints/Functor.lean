/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Basic

/-!
# Functorial matrix points cut out by a Hopf ideal

For a Hopf ideal `I` in the coordinate ring of `GLₙ` over a commutative ring `R`,
`TauCeti.GeneralLinear.hopfIdealPointsSubgroup n I A` is the group of `A`-valued points of the
corresponding closed subgroup scheme, in its matrix realization. This file assembles the existing
entrywise maps between these groups into a functor on commutative `R`-algebras.

The construction is independent of any particular Chevalley carrier. An eventual explicit pinned
simply connected carrier can instantiate it with its defining Hopf ideal. In the integral case,
`TauCeti.GeneralLinear.iterateFrobeniusHopfIdealPoints` supplies the `p ^ k`-power Frobenius
endomorphism and its fixed-point interface.

## Main declarations

* `TauCeti.GeneralLinear.hopfIdealPointsSubgroupFunctor`: the group-valued functor of matrix
  points cut out by a fixed Hopf ideal.

## Roadmap

This advances the carrier-independent infrastructure for "Points over an algebraically closed
field as a group, functorially in the field" in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`. The consumer is the explicit pinned simply connected
Chevalley--Demazure carrier required by milestone L0 of
`TauCetiRoadmap/CFSGStatement/README.md`; this file does not identify any provisional carrier with
that simply connected group.
-/

public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] (n : ℕ)
variable (I : HopfIdeal R (coordinateHopfAlgebra R n))

/-- The group-valued functor sending a commutative `R`-algebra to the matrix point group cut out by
a fixed Hopf ideal in the coordinate ring of `GLₙ`. -/
noncomputable def hopfIdealPointsSubgroupFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{w} where
  obj A := GrpCat.of (hopfIdealPointsSubgroup n I A)
  map f := GrpCat.ofHom (mapHopfIdealPointsSubgroup n I f.hom)
  map_id A := congrArg GrpCat.ofHom (mapHopfIdealPointsSubgroup_id n I A)
  map_comp f g := congrArg GrpCat.ofHom (mapHopfIdealPointsSubgroup_comp n I f.hom g.hom)

/-- The object part of the Hopf-ideal matrix-points functor is the subgroup cut out by the fixed
Hopf ideal. -/
@[simp]
theorem hopfIdealPointsSubgroupFunctor_obj (A : CommAlgCat.{w} R) :
    (hopfIdealPointsSubgroupFunctor n I).obj A =
      GrpCat.of (hopfIdealPointsSubgroup n I A) :=
  (rfl)

/-- The morphism part of the Hopf-ideal matrix-points functor is the restricted entrywise matrix
map. -/
@[simp]
theorem hopfIdealPointsSubgroupFunctor_map {A B : CommAlgCat.{w} R} (f : A ⟶ B) :
    (hopfIdealPointsSubgroupFunctor n I).map f =
      eqToHom (hopfIdealPointsSubgroupFunctor_obj n I A) ≫
        GrpCat.ofHom (mapHopfIdealPointsSubgroup n I f.hom) ≫
      eqToHom (hopfIdealPointsSubgroupFunctor_obj n I B).symm :=
  (rfl)

end

end TauCeti.GeneralLinear
