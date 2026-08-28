/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Topology on real special orthogonal groups in coordinates

For a quadratic form `Q` on a finite real coordinate space `n → ℝ`, this file induces the
standard coordinate topology from the faithful map of `specialOrthogonalGroup Q` into `GL(n, ℝ)`
defined in `TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup`. The resulting special orthogonal
group is Hausdorff and a topological group.

The construction applies to an arbitrary quadratic form on the coordinate space. It does not use a
Clifford algebra or a Spin group.

## Main results

* `TauCeti.QuadraticMap.isEmbedding_specialOrthogonalToGeneralLinear` records that it is a
  topological embedding.
-/

public section


namespace TauCeti

namespace QuadraticMap

noncomputable section

universe u


variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The canonical topology on a real special orthogonal group in coordinates is induced by its
faithful representation in `GL(n, ℝ)`. -/
instance instTopologicalSpaceSpecialOrthogonalGroupRealPi (Q : QuadraticForm ℝ (n → ℝ)) :
    TopologicalSpace (specialOrthogonalGroup Q) :=
  TopologicalSpace.induced (specialOrthogonalToGeneralLinear Q) inferInstance

/-- The coordinate inclusion of a real special orthogonal group is a topological embedding. -/
theorem isEmbedding_specialOrthogonalToGeneralLinear (Q : QuadraticForm ℝ (n → ℝ)) :
    Topology.IsEmbedding (specialOrthogonalToGeneralLinear Q) :=
  (specialOrthogonalToGeneralLinear_injective Q).isEmbedding_induced

/-- A real special orthogonal group in coordinates is a topological group. -/
instance instIsTopologicalGroupSpecialOrthogonalGroupRealPi (Q : QuadraticForm ℝ (n → ℝ)) :
    IsTopologicalGroup (specialOrthogonalGroup Q) :=
  topologicalGroup_induced (specialOrthogonalToGeneralLinear Q)

/-- A real special orthogonal group in coordinates is Hausdorff. -/
instance instT2SpaceSpecialOrthogonalGroupRealPi (Q : QuadraticForm ℝ (n → ℝ)) :
    T2Space (specialOrthogonalGroup Q) :=
  (isEmbedding_specialOrthogonalToGeneralLinear Q).t2Space

end


end QuadraticMap

end TauCeti
