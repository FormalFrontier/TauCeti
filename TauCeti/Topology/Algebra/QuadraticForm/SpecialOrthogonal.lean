/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Topology on special orthogonal groups in coordinates

For a quadratic map `Q` on a finite coordinate space `n → R`, this file induces the
standard coordinate topology from the faithful map of `specialOrthogonalGroup Q` into `GL(n, R)`
defined in `TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup`. Over a topological ring the
resulting special orthogonal group is a topological group, and it is Hausdorff when `R` is
Hausdorff.

The construction applies to an arbitrary quadratic map on the coordinate space. It does not use a
Clifford algebra or a Spin group.

## Main results

* `TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear` records that it is a
  topological embedding.
-/

public section


namespace TauCeti

namespace QuadraticMap

noncomputable section

universe u v w


variable {n : Type u} [Fintype n] [DecidableEq n]
  {R : Type v} [CommRing R] [TopologicalSpace R]
  {N : Type w} [AddCommMonoid N] [Module R N]

/-- The canonical topology on a special orthogonal group in coordinates is induced by its
faithful representation in `GL(n, R)`. -/
instance _root_.TauCeti.QuadraticMap.instTopologicalSpaceSpecialOrthogonalGroupPi
    (Q : QuadraticMap R (n → R) N) :
    TopologicalSpace (specialOrthogonalGroup Q) :=
  TopologicalSpace.induced (specialOrthogonalToGeneralLinear Q) inferInstance

/-- The coordinate inclusion of a special orthogonal group is a topological embedding. -/
theorem _root_.TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear
    (Q : QuadraticMap R (n → R) N) :
    Topology.IsEmbedding (specialOrthogonalToGeneralLinear Q) :=
  (specialOrthogonalToGeneralLinear_injective Q).isEmbedding_induced

/-- A special orthogonal group in coordinates over a topological ring is a topological group. -/
instance _root_.TauCeti.QuadraticMap.instIsTopologicalGroupSpecialOrthogonalGroupPi
    [IsTopologicalRing R]
    (Q : QuadraticMap R (n → R) N) :
    IsTopologicalGroup (specialOrthogonalGroup Q) :=
  topologicalGroup_induced (specialOrthogonalToGeneralLinear Q)

/-- A special orthogonal group in Hausdorff coordinates is Hausdorff. -/
instance _root_.TauCeti.QuadraticMap.instT2SpaceSpecialOrthogonalGroupPi [T2Space R]
    (Q : QuadraticMap R (n → R) N) :
    T2Space (specialOrthogonalGroup Q) :=
  (isEmbedding_specialOrthogonalToGeneralLinear Q).t2Space

end


end QuadraticMap

end TauCeti
