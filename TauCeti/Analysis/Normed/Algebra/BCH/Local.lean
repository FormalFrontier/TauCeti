/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Constructions
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Inverse
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Naturality

/-!
# The local Baker--Campbell--Hausdorff map

This file defines the germ at `(0, 0)` represented by
`logOneAdd (exp x * exp y - 1)` in a complete real normed algebra. Using a germ records
that this expression is a local logarithm; its values away from the origin
have no mathematical role.

The exponential of this germ is the product of the two exponentials. Its
restrictions to either coordinate axis are the identity germ, and its chosen
representative is analytic at the origin.

## Main declarations

* `NormedSpace.localBCH`: the local Baker--Campbell--Hausdorff germ.
* `NormedSpace.localBCH_def`: its defining representative equation.
* `NormedSpace.localBCH_sliceLeft` and `NormedSpace.localBCH_sliceRight`: the
  endpoint equations.
* `NormedSpace.localBCH_map_exp`: the local exponential equation.
* `NormedSpace.analyticAt_localBCH_representative`: the defining representative
  is analytic at the origin.
* `NormedSpace.localBCH_tendsto`: the germ tends to zero at the origin.
* `NormedSpace.eq_localBCH_of_tendsto_of_map_exp_eq`: uniqueness among germs
  tending to zero with the same exponential image.
* `NormedSpace.map_localBCH`: continuous ring homomorphisms commute with the
  local BCH germ.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff".
-/

public section

open Filter Topology

noncomputable section

namespace NormedSpace

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A]

/-- The germ at `(0, 0)` represented by the local logarithm
`fun p ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1)` of `exp p.1 * exp p.2`. -/
def localBCH [hA : CompleteSpace A] : Germ (𝓝 ((0, 0) : A × A)) A :=
  let _ := hA
  (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1) : A × A → A)

/-- `localBCH` is the germ of `fun p ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1)`. -/
theorem localBCH_def [CompleteSpace A] :
    localBCH A =
      (↑(fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1)) :
        Germ (𝓝 ((0, 0) : A × A)) A) :=
  by simp only [localBCH]

/-- The local Baker--Campbell--Hausdorff germ takes the value zero at the origin. -/
@[simp]
theorem localBCH_value [CompleteSpace A] : (localBCH A).value = 0 := by
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
  rw [localBCH_def, Germ.sliceLeft_coe, Germ.coe_eq]
  filter_upwards [eventually_logOneAdd_exp_sub_one A] with x hx
  simpa using hx

/-- Restricting the local Baker--Campbell--Hausdorff germ to the second coordinate axis gives the
identity germ. -/
@[simp]
theorem localBCH_sliceRight :
    (localBCH A).sliceRight = (↑(fun y : A ↦ y) : Germ (𝓝 (0 : A)) A) := by
  rw [localBCH_def, Germ.sliceRight_coe, Germ.coe_eq]
  filter_upwards [eventually_logOneAdd_exp_sub_one A] with y hy
  simpa using hy

private theorem tendsto_exp_mul_exp_sub_one :
    Tendsto (fun p : A × A ↦ exp p.1 * exp p.2 - 1)
      (𝓝 ((0, 0) : A × A)) (𝓝 (0 : A)) := by
  simpa only [exp_zero, mul_one, sub_self] using
    (analyticAt_exp_mul_exp_sub_one A).continuousAt.tendsto

/-- Applying exponential to the local Baker--Campbell--Hausdorff germ gives the germ of the product
of the two exponentials. -/
@[simp]
theorem localBCH_map_exp :
    (localBCH A).map exp =
      (↑(fun p : A × A ↦ exp p.1 * exp p.2) : Germ (𝓝 ((0, 0) : A × A)) A) := by
  rw [localBCH_def, Germ.map_coe, Germ.coe_eq]
  filter_upwards [(tendsto_exp_mul_exp_sub_one A).eventually
    (eventually_exp_logOneAdd A)] with p hp
  simpa [Function.comp_def] using hp

/-- The representative defining `localBCH` is analytic at the origin. -/
theorem analyticAt_localBCH_representative :
    AnalyticAt ℝ (fun p : A × A ↦ logOneAdd ℝ A (exp p.1 * exp p.2 - 1)) (0, 0) := by
  simpa [Function.comp_def] using (analyticAt_logOneAdd (𝕂 := ℝ) (A := A)).comp_of_eq
    (analyticAt_exp_mul_exp_sub_one A) (by simp)

/-- The local Baker--Campbell--Hausdorff germ tends to zero at the origin. -/
theorem localBCH_tendsto : (localBCH A).Tendsto (𝓝 0) := by
  rw [localBCH_def, Germ.coe_tendsto]
  simpa only [exp_zero, mul_one, sub_self, logOneAdd_zero] using
    (analyticAt_localBCH_representative A).continuousAt.tendsto

/-- A germ tending to zero with the same exponential image as `localBCH` equals `localBCH`. -/
theorem eq_localBCH_of_tendsto_of_map_exp_eq (f : Germ (𝓝 ((0, 0) : A × A)) A)
    (hf : f.Tendsto (𝓝 0)) (hmap : f.map exp = (localBCH A).map exp) : f = localBCH A := by
  induction f using Germ.inductionOn with
  | _ g =>
      rw [Germ.coe_tendsto] at hf
      rw [localBCH_def, Germ.coe_eq]
      have hmap' :
          (fun p : A × A => exp (g p)) =ᶠ[𝓝 ((0, 0) : A × A)]
            (fun p => exp p.1 * exp p.2) := by
        rw [Germ.map_coe, localBCH_map_exp, Germ.coe_eq] at hmap
        simpa only [Function.comp_def] using hmap
      filter_upwards [hf.eventually (eventually_logOneAdd_exp_sub_one A), hmap'] with p hp hmap_p
      rw [← hmap_p]
      exact hp.symm

section Naturality

variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [CompleteSpace B]

/-- Continuous ring homomorphisms commute with the local
Baker--Campbell--Hausdorff germ. -/
@[simp high]
theorem map_localBCH {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (hf : Continuous f) :
    (localBCH A).map f =
      (localBCH B).compTendsto (Prod.map f f) (by
        exact (hf.prodMap hf).tendsto'
          (0, 0) (0, 0) (by simp)) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  let _ : NormedAlgebra ℚ B := NormedAlgebra.restrictScalars ℚ ℝ B
  rw [localBCH_def, Germ.map_coe, localBCH_def, Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [(tendsto_exp_mul_exp_sub_one A).eventually
    (eventually_map_logOneAdd (𝕂 := ℝ) (𝕃 := ℝ) f hf)] with p hp
  dsimp only [Function.comp_apply, Prod.map]
  rw [hp]
  have hx : f (exp p.1) = exp (f p.1) := map_exp f hf p.1
  have hy : f (exp p.2) = exp (f p.2) := map_exp f hf p.2
  rw [map_sub, map_mul, map_one, hx, hy]

end Naturality

end NormedSpace
