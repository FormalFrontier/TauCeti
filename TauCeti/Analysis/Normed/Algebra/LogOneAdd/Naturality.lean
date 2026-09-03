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

This file proves that continuous ring homomorphisms commute with the
power series for `log (1 + u)` on the open unit ball. It also packages this
local identity as an equality of germs at the origin.

## Main results

* `NormedSpace.map_logOneAddSeries_apply`: naturality of each homogeneous term.
* `NormedSpace.map_logOneAdd_of_norm_lt_one`: naturality on the open unit ball.
* `NormedSpace.eventually_map_logOneAdd`: naturality near the origin.
* `NormedSpace.map_logOneAdd_germ`: naturality as an equality of germs.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Baker--Campbell--Hausdorff".
* `NormedSpace.map_exp_of_mem_ball` in Mathlib's exponential naturality development.
-/

public section

open Filter Topology

noncomputable section

namespace NormedSpace

section Algebra

variable {𝕂 𝕃 A B : Type*} [Field 𝕂] [CharZero 𝕂] [Field 𝕃] [CharZero 𝕃]
variable [Ring A] [Algebra 𝕂 A] [TopologicalSpace A] [IsTopologicalRing A]
variable [Ring B] [Algebra 𝕃 B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Ring homomorphisms commute with each homogeneous term of
`logOneAddSeries`. -/
theorem map_logOneAddSeries_apply {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) {n : ℕ} (v : Fin n → A) :
    f (logOneAddSeries 𝕂 A n v) = logOneAddSeries 𝕃 B n (f ∘ v) := by
  rw [logOneAddSeries_apply, logOneAddSeries_apply]
  calc
    f (((-1 : 𝕂) ^ (n + 1) / n) • (List.ofFn v).prod) =
        ((-1 : 𝕃) ^ (n + 1) / n) • f (List.ofFn v).prod := by
      simpa [Rat.cast_div, Rat.cast_pow] using
        (map_ratCast_smul f 𝕂 𝕃 ((-1 : ℚ) ^ (n + 1) / n)
          ((List.ofFn v).prod))
    _ = ((-1 : 𝕃) ^ (n + 1) / n) • (List.map f (List.ofFn v)).prod := by
      rw [map_list_prod]
    _ = ((-1 : 𝕃) ^ (n + 1) / n) • (List.ofFn (f ∘ v)).prod := by
      simp only [List.map_ofFn]

end Algebra

section Normed

variable {𝕂 𝕃 A B : Type*} [NontriviallyNormedField 𝕂] [CharZero 𝕂]
variable [Field 𝕃] [CharZero 𝕃]
variable [ContinuousSMul ℚ≥0 𝕂]
variable [NormedRing A] [NormedAlgebra 𝕂 A]
variable [Ring B] [Algebra 𝕃 B] [TopologicalSpace B] [IsTopologicalRing B]
variable [CompleteSpace A]

/-- Continuous ring homomorphisms commute with `logOneAdd` on the open unit ball. -/
theorem map_logOneAdd_of_norm_lt_one {F : Type*} [FunLike F A B] [RingHomClass F A B]
    [T2Space B] (f : F) (hf : Continuous f) {u : A} (hu : ‖u‖ < 1) :
    f (logOneAdd 𝕂 A u) = logOneAdd 𝕃 B (f u) := by
  rw [logOneAdd_eq_tsum, logOneAdd_eq_tsum]
  calc
    f (∑' n : ℕ, ((-1 : 𝕂) ^ (n + 1) / n) • u ^ n) =
        ∑' n : ℕ, f (((-1 : 𝕂) ^ (n + 1) / n) • u ^ n) := by
      exact ((summable_logOneAdd 𝕂 A hu).hasSum.map f hf).tsum_eq.symm
    _ = ∑' n : ℕ, ((-1 : 𝕃) ^ (n + 1) / n) • (f u) ^ n := by
      apply tsum_congr
      intro n
      simpa only [logOneAddSeries_apply, List.ofFn_const, List.prod_replicate,
        Function.comp_def] using
        map_logOneAddSeries_apply (𝕂 := 𝕂) (𝕃 := 𝕃) f (fun _ : Fin n ↦ u)

/-- A continuous ring homomorphism commutes with `logOneAdd` near the origin. -/
theorem eventually_map_logOneAdd {F : Type*} [FunLike F A B] [RingHomClass F A B]
    [T2Space B] (f : F) (hf : Continuous f) :
    ∀ᶠ u in 𝓝 (0 : A), f (logOneAdd 𝕂 A u) = logOneAdd 𝕃 B (f u) := by
  filter_upwards [Metric.ball_mem_nhds (0 : A) zero_lt_one] with u hu
  exact map_logOneAdd_of_norm_lt_one (𝕂 := 𝕂) (𝕃 := 𝕃) f hf
    (by simpa [Metric.mem_ball, dist_zero_right] using hu)

/-- Continuous ring homomorphisms commute with the germ of `logOneAdd` at the origin. -/
theorem map_logOneAdd_germ {F : Type*} [FunLike F A B] [RingHomClass F A B]
    [T2Space B] (f : F) (hf : Continuous f) :
    (↑(f ∘ logOneAdd 𝕂 A) : Germ (𝓝 (0 : A)) B) =
      (↑(logOneAdd 𝕃 B) : Germ (𝓝 (0 : B)) B).compTendsto f (by
        exact hf.tendsto' 0 0 (map_zero f)) := by
  rw [Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [eventually_map_logOneAdd (𝕂 := 𝕂) (𝕃 := 𝕃) f hf] with u hu
  exact hu

/- The same-field logarithm germ equation is the simplifier boundary.  The
generic theorem above intentionally remains explicit because its target field
does not occur in the left-hand side. -/
@[simp high]
private theorem map_logOneAdd_germ_sameField {F : Type*} [FunLike F A B]
    [ContinuousMapClass F A B] [RingHomClass F A B] [T2Space B] (f : F)
    [Algebra 𝕂 B] :
    (↑(f ∘ logOneAdd 𝕂 A) : Germ (𝓝 (0 : A)) B) =
      (↑(logOneAdd 𝕂 B) : Germ (𝓝 (0 : B)) B).compTendsto f (by
        exact (map_continuous f).tendsto' 0 0 (map_zero f)) :=
  map_logOneAdd_germ (𝕂 := 𝕂) (𝕃 := 𝕂) f (map_continuous f)

end Normed

end NormedSpace
