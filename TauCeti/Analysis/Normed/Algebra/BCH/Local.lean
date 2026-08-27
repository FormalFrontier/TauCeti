/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Topology.Germ
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Inverse

/-!
# The local Baker--Campbell--Hausdorff map

This file defines the germ at `(0, 0)` represented by
`logOneAdd (exp x * exp y - 1)` in a complete real normed algebra. Using a
germ records that this expression is a local logarithm; its values away from
the origin have no mathematical role.

The exponential of this germ is the product of the two exponentials. Its
restrictions to either coordinate axis are the identity germ, and its chosen
representative is analytic at the origin.

## Main declarations

* `NormedSpace.localBCH` and `NormedSpace.localBCH_def`: the local
  Baker--Campbell--Hausdorff germ and its representative.
* `NormedSpace.localBCH_sliceLeft` and `NormedSpace.localBCH_sliceRight`: the
  endpoint equations.
* `NormedSpace.localBCH_map_exp`: the local exponential equation.
* `NormedSpace.exists_analyticAt_localBCH_representation`: an analytic
  representative of the germ.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff".
-/

public section

open Filter Topology

noncomputable section

namespace NormedSpace

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

/-- The germ at `(0, 0)` of the local Baker--Campbell--Hausdorff map. -/
def localBCH : Germ (𝓝 ((0, 0) : A × A)) A :=
  (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1) : A × A → A)

/-- The representative defining the local Baker--Campbell--Hausdorff germ. -/
theorem localBCH_def :
    localBCH A =
      (↑(fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1)) :
        Germ (𝓝 ((0, 0) : A × A)) A) :=
  by simp only [localBCH]

/-- The local Baker--Campbell--Hausdorff germ takes the value zero at the origin. -/
@[simp]
theorem localBCH_value : (localBCH A).value = 0 := by
  simp [localBCH]

variable [CompleteSpace A]

private theorem analyticAt_exp_mul_exp_sub_one :
    AnalyticAt ℝ (fun p : A × A ↦ exp p.1 * exp p.2 - 1) (0, 0) :=
  (((exp_analytic (𝕂 := ℝ) 0).comp (x := (0, 0)) analyticAt_fst).mul
    ((exp_analytic (𝕂 := ℝ) 0).comp (x := (0, 0)) analyticAt_snd)).sub analyticAt_const

/-- Restricting the local Baker--Campbell--Hausdorff germ to the first coordinate axis gives the
identity germ. -/
@[simp]
theorem localBCH_sliceLeft :
    (localBCH A).sliceLeft = (↑(fun x : A ↦ x) : Germ (𝓝 (0 : A)) A) := by
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_logOneAdd_exp_sub_one A] with x hx
  simpa [localBCH] using hx

/-- Restricting the local Baker--Campbell--Hausdorff germ to the second coordinate axis gives the
identity germ. -/
@[simp]
theorem localBCH_sliceRight :
    (localBCH A).sliceRight = (↑(fun y : A ↦ y) : Germ (𝓝 (0 : A)) A) := by
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_logOneAdd_exp_sub_one A] with y hy
  simpa [localBCH] using hy

private theorem tendsto_exp_mul_exp_sub_one :
    Tendsto (fun p : A × A ↦ exp p.1 * exp p.2 - 1)
      (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) := by
  simpa only [ContinuousAt, exp_zero, mul_one, sub_self] using
    (analyticAt_exp_mul_exp_sub_one A).continuousAt

/-- Applying exponential to the local Baker--Campbell--Hausdorff germ gives the germ of the product
of the two exponentials. -/
@[simp]
theorem localBCH_map_exp :
    (localBCH A).map exp =
      (↑(fun p : A × A ↦ exp p.1 * exp p.2) : Germ (𝓝 ((0, 0) : A × A)) A) := by
  apply Germ.coe_eq.mpr
  filter_upwards [(tendsto_exp_mul_exp_sub_one A).eventually
    (eventually_exp_logOneAdd A)] with p hp
  simpa [localBCH] using hp

/-- The local Baker--Campbell--Hausdorff germ has a representative analytic at the origin. -/
theorem exists_analyticAt_localBCH_representation :
    ∃ f : A × A → A,
      localBCH A = (↑f : Germ (𝓝 ((0, 0) : A × A)) A) ∧ AnalyticAt ℝ f (0, 0) := by
  refine ⟨fun p ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1), localBCH_def A, ?_⟩
  simpa [Function.comp_def] using (analyticAt_logOneAdd (𝕂 := ℝ) (A := A)).comp_of_eq
    (analyticAt_exp_mul_exp_sub_one A) (by simp)

end NormedSpace
