/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Extending bounded-operator convergence from dense subsets

This file records two standard density arguments for uniformly bounded families of continuous
linear maps. Pointwise convergence on a dense subset extends to pointwise convergence everywhere,
and uniform Cauchy convergence on a parameter set does likewise.
-/

public section

namespace TauCeti

open Filter

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

namespace ContinuousLinearMap

/-- A uniformly bounded family of continuous linear maps that converges pointwise on a dense
subset converges pointwise everywhere. -/
theorem tendsto_apply_of_dense {ι : Type*} {l : Filter ι} {D : Set X}
    (hD : Dense D) {f : ι → X →L[𝕜] Y} {g : X →L[𝕜] Y} {C : ℝ}
    (hbound : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (htendsto : ∀ x ∈ D, Tendsto (fun i => f i x) l (nhds (g x))) (x : X) :
    Tendsto (fun i => f i x) l (nhds (g x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let K : ℝ := |C| + ‖g‖ + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hC_le : C ≤ K := by
    dsimp only [K]
    linarith [le_abs_self C, norm_nonneg g]
  have hg_le : ‖g‖ ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg C]
  have hscale : K * (epsilon / (3 * K)) = epsilon / 3 := by
    field_simp
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < epsilon / (3 * K))
  have hxy_norm : ‖x - y‖ < epsilon / (3 * K) := by
    simpa only [dist_eq_norm] using hxy
  have hy := (Metric.tendsto_nhds.mp (htendsto y hyD)) (epsilon / 3) (by positivity)
  filter_upwards [hbound, hy] with i hi hiy
  rw [dist_eq_norm] at hiy ⊢
  have hfi : ‖f i‖ ≤ K := hi.trans hC_le
  have hleft : ‖f i (x - y)‖ < epsilon / 3 := by
    calc
      ‖f i (x - y)‖ ≤ ‖f i‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖x - y‖ := mul_le_mul_of_nonneg_right hfi (norm_nonneg _)
      _ < K * (epsilon / (3 * K)) := mul_lt_mul_of_pos_left hxy_norm hK
      _ = epsilon / 3 := hscale
  have hyx_norm : ‖y - x‖ < epsilon / (3 * K) := by rwa [norm_sub_rev]
  have hright : ‖g (y - x)‖ < epsilon / 3 := by
    calc
      ‖g (y - x)‖ ≤ ‖g‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖y - x‖ := mul_le_mul_of_nonneg_right hg_le (norm_nonneg _)
      _ < K * (epsilon / (3 * K)) := mul_lt_mul_of_pos_left hyx_norm hK
      _ = epsilon / 3 := hscale
  have hdecomp : f i x - g x = f i (x - y) + (f i y - g y) + g (y - x) := by
    rw [map_sub, map_sub]
    abel
  rw [hdecomp]
  calc
    ‖f i (x - y) + (f i y - g y) + g (y - x)‖
        ≤ ‖f i (x - y)‖ + ‖f i y - g y‖ + ‖g (y - x)‖ := norm_add₃_le
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by linarith
    _ = epsilon := by ring

/-- A uniformly bounded family of continuous linear maps that is uniformly Cauchy on a parameter
set at every vector in a dense subset is uniformly Cauchy there at every vector. -/
theorem uniformCauchySeqOn_apply_of_dense {ι Z : Type*} [Nonempty ι] [SemilatticeSup ι]
    {D : Set X} (hD : Dense D) {f : ι → Z → X →L[𝕜] Y} {s : Set Z} {C : ℝ}
    (hbound : ∀ᶠ i in atTop, ∀ z ∈ s, ‖f i z‖ ≤ C)
    (hcauchy : ∀ x ∈ D, UniformCauchySeqOn (fun i z => f i z x) atTop s) (x : X) :
    UniformCauchySeqOn (fun i z => f i z x) atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro epsilon hepsilon
  let K : ℝ := |C| + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hC_le : C ≤ K := by
    dsimp only [K]
    linarith [le_abs_self C]
  have hscale : K * (epsilon / (3 * K)) = epsilon / 3 := by
    field_simp
  obtain ⟨y, hyD, hxy⟩ := hD.exists_dist_lt x (by positivity : 0 < epsilon / (3 * K))
  have hxy_norm : ‖x - y‖ < epsilon / (3 * K) := by
    simpa only [dist_eq_norm] using hxy
  obtain ⟨Nbound, hNbound⟩ := Filter.eventually_atTop.mp hbound
  have hy_cauchy := hcauchy y hyD
  rw [Metric.uniformCauchySeqOn_iff] at hy_cauchy
  obtain ⟨Ncauchy, hNcauchy⟩ := hy_cauchy (epsilon / 3) (by positivity)
  refine ⟨Nbound ⊔ Ncauchy, fun i hi j hj z hz => ?_⟩
  rw [dist_eq_norm]
  have hi_bound : ‖f i z‖ ≤ K :=
    (hNbound i (le_trans le_sup_left hi) z hz).trans hC_le
  have hj_bound : ‖f j z‖ ≤ K :=
    (hNbound j (le_trans le_sup_left hj) z hz).trans hC_le
  have hleft : ‖f i z (x - y)‖ < epsilon / 3 := by
    calc
      ‖f i z (x - y)‖ ≤ ‖f i z‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖x - y‖ := mul_le_mul_of_nonneg_right hi_bound (norm_nonneg _)
      _ < K * (epsilon / (3 * K)) := mul_lt_mul_of_pos_left hxy_norm hK
      _ = epsilon / 3 := hscale
  have hyx_norm : ‖y - x‖ < epsilon / (3 * K) := by rwa [norm_sub_rev]
  have hright : ‖f j z (y - x)‖ < epsilon / 3 := by
    calc
      ‖f j z (y - x)‖ ≤ ‖f j z‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖y - x‖ := mul_le_mul_of_nonneg_right hj_bound (norm_nonneg _)
      _ < K * (epsilon / (3 * K)) := mul_lt_mul_of_pos_left hyx_norm hK
      _ = epsilon / 3 := hscale
  have hmiddle : ‖f i z y - f j z y‖ < epsilon / 3 := by
    simpa only [dist_eq_norm] using
      hNcauchy i (le_trans le_sup_right hi) j (le_trans le_sup_right hj) z hz
  have hdecomp : f i z x - f j z x =
      f i z (x - y) + (f i z y - f j z y) + f j z (y - x) := by
    rw [map_sub, map_sub]
    abel
  rw [hdecomp]
  calc
    ‖f i z (x - y) + (f i z y - f j z y) + f j z (y - x)‖
        ≤ ‖f i z (x - y)‖ + ‖f i z y - f j z y‖ + ‖f j z (y - x)‖ := norm_add₃_le
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by linarith
    _ = epsilon := by ring

end ContinuousLinearMap

end TauCeti
