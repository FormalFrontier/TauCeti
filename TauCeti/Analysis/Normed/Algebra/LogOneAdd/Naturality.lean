/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Germ
public import TauCeti.Analysis.Normed.Algebra.LogOneAdd.Basic

/-!
# Naturality of the local logarithm

This file proves that continuous algebra homomorphisms commute with the
power series for `log (1 + u)` wherever it converges. It also packages this
local identity as an equality of germs at the origin.

## Main results

* `NormedSpace.map_logOneAddSeries_apply`: naturality of each homogeneous term.
* `NormedSpace.map_logOneAdd`: naturality on the open unit ball.
* `NormedSpace.eventually_map_logOneAdd`: naturality near the origin.
* `NormedSpace.map_logOneAdd_germ`: naturality as an equality of germs.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff".
-/

public section

open Filter Topology

noncomputable section

namespace NormedSpace

section Algebra

variable {𝕂 A B : Type*} [Field 𝕂] [CharZero 𝕂]
variable [Ring A] [Algebra 𝕂 A] [TopologicalSpace A] [IsTopologicalRing A]
variable [Ring B] [Algebra 𝕂 B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Algebra homomorphisms commute with each homogeneous term of
`logOneAddSeries`. -/
theorem map_logOneAddSeries_apply (f : A →ₐ[𝕂] B) {n : ℕ} (v : Fin n → A) :
    f (logOneAddSeries 𝕂 A n v) = logOneAddSeries 𝕂 B n (f ∘ v) := by
  rw [logOneAddSeries_apply, logOneAddSeries_apply, map_smul, map_list_prod]
  simp only [List.map_ofFn]

end Algebra

section Normed

variable {𝕂 A B : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
variable [ContinuousSMul ℚ≥0 𝕂]
variable [NormedRing A] [NormedAlgebra 𝕂 A]
variable [NormedRing B] [NormedAlgebra 𝕂 B]
variable [CompleteSpace A]

/-- Continuous algebra homomorphisms commute with `logOneAdd` on the open unit ball. -/
theorem map_logOneAdd (f : A →A[𝕂] B) {u : A} (hu : ‖u‖ < 1) :
    f (logOneAdd 𝕂 A u) = logOneAdd 𝕂 B (f u) := by
  rw [logOneAdd_eq_tsum, logOneAdd_eq_tsum]
  calc
    f (∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • u ^ n) =
        ∑' n : ℕ, f (((-1 : 𝕂) ^ (n + 1) / n) • u ^ n) := by
      simpa only [ContinuousAlgHom.coe_toContinuousLinearMap] using
        f.toContinuousLinearMap.map_tsum (summable_logOneAdd 𝕂 A hu)
    _ = ∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • (f u) ^ n := by
      apply tsum_congr
      intro n
      simp only [map_smul, map_pow]

/-- A continuous algebra homomorphism commutes with `logOneAdd` near the origin. -/
theorem eventually_map_logOneAdd (f : A →A[𝕂] B) :
    ∀ᶠ u in 𝓝 (0 : A), f (logOneAdd 𝕂 A u) = logOneAdd 𝕂 B (f u) := by
  filter_upwards [Metric.ball_mem_nhds (0 : A) zero_lt_one] with u hu
  exact map_logOneAdd f (by simpa [Metric.mem_ball, dist_zero_right] using hu)

/-- Continuous algebra homomorphisms commute with the germ of `logOneAdd` at the origin. -/
theorem map_logOneAdd_germ (f : A →A[𝕂] B) :
    (↑(logOneAdd 𝕂 A) : Germ (𝓝 (0 : A)) A).map f =
      (↑(logOneAdd 𝕂 B) : Germ (𝓝 (0 : B)) B).compTendsto f (by
        exact f.continuous.tendsto' 0 0 (map_zero f)) := by
  rw [Germ.map_coe, Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [eventually_map_logOneAdd f] with u hu
  exact hu

end Normed

end NormedSpace
