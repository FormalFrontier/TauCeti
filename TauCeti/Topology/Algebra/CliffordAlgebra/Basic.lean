/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Star

/-!
# Topology on real Clifford algebras

This file gives a real Clifford algebra its real module topology and topological additive-group
structure. The topology is Hausdorff, and Clifford reverse, involution, and star are continuous,
without a finite-dimensionality assumption. In finite dimension, multiplication is continuous.

The topology is intrinsic: it depends only on the real module structure of the Clifford algebra and
does not use a basis, Pin or Spin groups, or their actions. A basis appears only in the proof that
the topology is Hausdorff.

## Main results

* `CliffordAlgebra.instTopologicalSpaceRealCliffordAlgebra` installs the real module topology.
* `CliffordAlgebra.instIsTopologicalAddGroupRealCliffordAlgebra` makes addition continuous.
* `CliffordAlgebra.instIsTopologicalRingRealCliffordAlgebra` makes multiplication continuous.
* `CliffordAlgebra.instT2SpaceRealCliffordAlgebra` proves the topology is Hausdorff.
* `CliffordAlgebra.continuous_reverse_realCliffordAlgebra` and
  `CliffordAlgebra.continuous_involute_realCliffordAlgebra` prove continuity of the two canonical
  Clifford involutions.
* `CliffordAlgebra.instContinuousStarRealCliffordAlgebra` packages continuity of Clifford star.
-/

public section


namespace CliffordAlgebra

open TauCeti

noncomputable section

universe u


variable {V : Type u} [AddCommGroup V] [Module ℝ V]

/-- The canonical topology on a real Clifford algebra is its real module topology. -/
instance instTopologicalSpaceRealCliffordAlgebra (Q : QuadraticForm ℝ V) :
    TopologicalSpace (CliffordAlgebra Q) :=
  moduleTopology ℝ _

/-- A real Clifford algebra is a topological additive group for its real module topology. -/
instance instIsTopologicalAddGroupRealCliffordAlgebra (Q : QuadraticForm ℝ V) :
    IsTopologicalAddGroup (CliffordAlgebra Q) :=
  IsModuleTopology.isTopologicalAddGroup ℝ _

/-- Clifford reversal is continuous for the real module topology. -/
@[fun_prop]
theorem continuous_reverse_realCliffordAlgebra (Q : QuadraticForm ℝ V) :
    Continuous (reverse (Q := Q) : CliffordAlgebra Q → CliffordAlgebra Q) :=
  IsModuleTopology.continuous_of_linearMap (reverse (Q := Q))

/-- The Clifford grade involution is continuous for the real module topology. -/
@[fun_prop]
theorem continuous_involute_realCliffordAlgebra (Q : QuadraticForm ℝ V) :
    Continuous (involute (Q := Q) : CliffordAlgebra Q → CliffordAlgebra Q) :=
  IsModuleTopology.continuous_of_linearMap (involute (Q := Q)).toLinearMap

/-- Clifford star is continuous for the real module topology. -/
instance instContinuousStarRealCliffordAlgebra (Q : QuadraticForm ℝ V) :
    ContinuousStar (CliffordAlgebra Q) where
  continuous_star := by
    convert (continuous_reverse_realCliffordAlgebra Q).comp
      (continuous_involute_realCliffordAlgebra Q) using 1
    funext x
    exact star_def x

/-- The real module topology on a Clifford algebra is Hausdorff. -/
instance instT2SpaceRealCliffordAlgebra (Q : QuadraticForm ℝ V) :
    T2Space (CliffordAlgebra Q) := by
  let b := Module.Free.chooseBasis ℝ (CliffordAlgebra Q)
  let f : CliffordAlgebra Q → (Module.Free.ChooseBasisIndex ℝ (CliffordAlgebra Q) → ℝ) :=
    fun x i => b.repr x i
  exact T2Space.of_injective_continuous (f := f)
    (by
      intro x y h
      apply b.repr.injective
      ext i
      exact congrFun h i)
    (continuous_pi fun i => IsModuleTopology.continuous_of_linearMap (b.coord i))

variable [FiniteDimensional ℝ V]

/-- A finite-dimensional real Clifford algebra is a topological ring for its real module
topology. -/
instance instIsTopologicalRingRealCliffordAlgebra (Q : QuadraticForm ℝ V) :
    IsTopologicalRing (CliffordAlgebra Q) :=
  IsModuleTopology.isTopologicalRing ℝ _

end

end CliffordAlgebra
