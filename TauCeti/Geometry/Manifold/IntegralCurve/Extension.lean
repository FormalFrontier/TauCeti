/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.Transform
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import TauCeti.Analysis.ODE.UniformTime
public import TauCeti.Geometry.Manifold.IntegralCurve.Basic

/-!
# Extending an integral curve past a finite endpoint

Mathlib's integral-curve API produces a local integral curve through a point and shows that two
integral curves on a common open interval agree. It says nothing about what happens at a finite
endpoint of the interval of definition. This file supplies the missing extension criterion:
an integral curve on `Ioo a b` with `b < ∞` extends past `b` as soon as it accumulates at a point
of the manifold as `t → b⁻`. Equivalently, a curve that cannot be extended must eventually leave
every compact set.

The proof needs a *uniform* time of existence: the same `ε > 0` must work for every initial point
in a neighbourhood of the accumulation point `y`, so that a time `t₁ < b` with `b - t₁ < ε` and
`γ t₁` near `y` produces a solution defined past `b`. Uniqueness on the overlap then glues it to
`γ`. The uniform time comes from
`ODE.exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem`,
read through the extended chart at `y`.

## Main results

* `exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo`: a uniform time of existence for the
  integral curves of a `C^1` vector field near a point.
* `IsMIntegralCurveOn.exists_gt_isMIntegralCurveOn_Ioo`: the extension criterion at a finite right
  endpoint, and `IsMIntegralCurveOn.exists_lt_isMIntegralCurveOn_Ioo` at a finite left endpoint.
* `IsMIntegralCurveOn.exists_gt_isMIntegralCurveOn_Ioo_of_tendsto` and
  `IsMIntegralCurveOn.exists_lt_isMIntegralCurveOn_Ioo_of_tendsto`: their sequential forms.
* `IsMIntegralCurveOn.eventually_notMem_nhdsLT` and
  `IsMIntegralCurveOn.eventually_notMem_nhdsGT`: a nonextendable integral curve eventually leaves
  every compact set.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Finite-endpoint extension criterion".
* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012], Chapter 9.
-/

public section

open Filter Function Manifold Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b : ℝ} {y : M}

/-- **A uniform time of existence** for the integral curves of a `C^1` vector field: there is a
neighbourhood `w` of `x₀` and a single `ε > 0` such that, at any prescribed initial time `t₀`,
every point of `w` is the value at `t₀` of an integral curve defined on all of
`Ioo (t₀ - ε) (t₀ + ε)`.

Mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` gives an interval of existence
that depends on the initial point; the content here is that it can be chosen uniformly. The field
is autonomous, so the initial time is immaterial and `ε` is uniform in it too. -/
theorem exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo [CompleteSpace E] [IsManifold I 1 M]
    [BoundarylessManifold I M] {x₀ : M}
    (hv : CMDiffAt 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ w ∈ 𝓝 x₀, ∃ ε > (0 : ℝ), ∀ t₀ : ℝ, ∀ x ∈ w, ∃ γ : ℝ → M,
      γ t₀ = x ∧ IsMIntegralCurveOn γ v (Ioo (t₀ - ε) (t₀ + ε)) := by
  -- the vector field read in the extended chart at `x₀`
  set g : E → E := fun z ↦ tangentCoordChange I ((extChartAt I x₀).symm z) x₀
    ((extChartAt I x₀).symm z) (v ((extChartAt I x₀).symm z))
  have hgc : ContDiffAt ℝ 1 g (extChartAt I x₀ x₀) :=
    ((contMDiffAt_iff.mp hv).2.contDiffAt (range_mem_nhds_isInteriorPoint
      BoundarylessManifold.isInteriorPoint)).snd
  have hnhds : interior (extChartAt I x₀).target ∈ 𝓝 (extChartAt I x₀ x₀) :=
    isOpen_interior.mem_nhds (I.isInteriorPoint_iff.mp BoundarylessManifold.isInteriorPoint)
  obtain ⟨r, hr, ε, hε, hsol⟩ :=
    ODE.exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem hgc hnhds 0
  refine ⟨extChartAt I x₀ ⁻¹' Metric.ball (extChartAt I x₀ x₀) r ∩ (extChartAt I x₀).source,
    Filter.inter_mem ((continuousAt_extChartAt x₀).preimage_mem_nhds
      (Metric.ball_mem_nhds _ hr)) (extChartAt_source_mem_nhds x₀), ε, hε, fun t₀ x hx ↦ ?_⟩
  obtain ⟨f, hf0, hf⟩ := hsol (extChartAt I x₀ x) hx.1
  -- the coordinate solution starts at time `0`; translate it to start at time `t₀`
  have hf' : IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ f) v (Ioo (0 - ε) (0 + ε)) :=
    IsMIntegralCurveAt.isMIntegralCurveOn fun t ht ↦ by
      refine IsMIntegralCurveAt.of_extChartAt_symm ?_ ?_
      · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using (hf s hs).2
      · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs using (hf s hs).1
  refine ⟨((extChartAt I x₀).symm ∘ f) ∘ (· - t₀), ?_,
    (isMIntegralCurveOn_comp_sub.2 hf').mono fun t ht ↦ ?_⟩
  · simp only [comp_apply, sub_self]
    rw [hf0, (extChartAt I x₀).left_inv hx.2]
  · simp only [mem_ofPred_eq, mem_Ioo, zero_sub, zero_add] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]

namespace IsMIntegralCurveOn

variable [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]

/-- **The finite-endpoint extension criterion.** An integral curve on `Ioo a b` which accumulates
at a point `y` of the manifold as `t → b⁻` extends to an integral curve on a strictly longer
interval `Ioo a c`.

The hypothesis is a cluster point rather than a limit: it suffices that `γ t` be arbitrarily close
to `y` at times arbitrarily close to `b`. -/
theorem exists_gt_isMIntegralCurveOn_Ioo
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hy : MapClusterPt y (𝓝[<] b) γ) :
    ∃ c > b, ∃ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo a c) ∧ EqOn δ γ (Ioo a b) := by
  obtain ⟨w, hw, ε, hε, hloc⟩ :=
    exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo (x₀ := y) hv.contMDiffAt
  -- a time `t₁` close enough to `b`, at which the curve is already close to `y`
  have hmem : Ioo (max a (b - ε / 2)) b ∈ 𝓝[<] b :=
    Ioo_mem_nhdsLT (max_lt hab (by linarith))
  obtain ⟨t₁, ht₁w, ht₁⟩ :=
    ((mapClusterPt_iff_frequently.mp hy w hw).and_eventually hmem).exists
  have ht₁a : a < t₁ := lt_of_le_of_lt (le_max_left _ _) ht₁.1
  have ht₁ε : b - ε / 2 < t₁ := lt_of_le_of_lt (le_max_right _ _) ht₁.1
  have ht₁b : t₁ < b := ht₁.2
  -- the local solution through `γ t₁` starting at time `t₁`
  obtain ⟨β, hβ0, hβ⟩ := hloc t₁ (γ t₁) ht₁w
  have hbc : b < t₁ + ε := by linarith
  -- glue the two curves at time `t₁`
  refine ⟨t₁ + ε, hbc, piecewise (Ioo a b) γ β, ?_, piecewise_eqOn _ _ _⟩
  exact (isMIntegralCurveOn_piecewise hv hγ hβ
    ⟨⟨ht₁a, ht₁b⟩, ⟨by linarith, by linarith⟩⟩ hβ0.symm).mono
      (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) le_rfl)

/-- **The finite-endpoint extension criterion**, sequential form. If `u n → b`, the sequence
is eventually below `b`, and `γ (u n) → y`, then `γ` extends past `b`. -/
theorem exists_gt_isMIntegralCurveOn_Ioo_of_tendsto
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u n < b) (hub : Tendsto u atTop (𝓝 b))
    (hy : Tendsto (γ ∘ u) atTop (𝓝 y)) :
    ∃ c > b, ∃ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo a c) ∧ EqOn δ γ (Ioo a b) := by
  refine hγ.exists_gt_isMIntegralCurveOn_Ioo hab hv (ClusterPt.mono hy.mapClusterPt ?_)
  exact map_mono (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hub hu)

/-- **The escape lemma.** An integral curve on `Ioo a b` that admits no extension past its finite
right endpoint eventually leaves every compact set as `t → b⁻`. -/
theorem eventually_notMem_nhdsLT
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hmax : ∀ c > b, ∀ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo a c) → ¬EqOn δ γ (Ioo a b))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, γ t ∉ K := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_not] at h
  obtain ⟨z, _, hz⟩ := hK.exists_mapClusterPt_of_frequently h
  obtain ⟨c, hc, δ, hδ, hδeq⟩ := hγ.exists_gt_isMIntegralCurveOn_Ioo hab hv hz
  exact hmax c hc δ hδ hδeq

/-- **The finite-endpoint extension criterion at the left endpoint.** An integral curve on
`Ioo a b` which accumulates at a point `y` of the manifold as `t → a⁺` extends to an integral
curve on a strictly longer interval `Ioo c b`. -/
theorem exists_lt_isMIntegralCurveOn_Ioo
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hy : MapClusterPt y (𝓝[>] a) γ) :
    ∃ c < a, ∃ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo c b) ∧ EqOn δ γ (Ioo a b) := by
  obtain ⟨w, hw, ε, hε, hloc⟩ :=
    exists_mem_nhds_forall_exists_isMIntegralCurveOn_Ioo (x₀ := y) hv.contMDiffAt
  have hmem : Ioo a (min b (a + ε / 2)) ∈ 𝓝[>] a :=
    Ioo_mem_nhdsGT (lt_min hab (by linarith))
  obtain ⟨t₁, ht₁w, ht₁⟩ :=
    ((mapClusterPt_iff_frequently.mp hy w hw).and_eventually hmem).exists
  have ht₁a : a < t₁ := ht₁.1
  have ht₁b : t₁ < b := lt_of_lt_of_le ht₁.2 (min_le_left _ _)
  have ht₁ε : t₁ < a + ε / 2 := lt_of_lt_of_le ht₁.2 (min_le_right _ _)
  obtain ⟨β, hβ0, hβ⟩ := hloc t₁ (γ t₁) ht₁w
  have hca : t₁ - ε < a := by linarith
  refine ⟨t₁ - ε, hca, piecewise (Ioo a b) γ β, ?_, piecewise_eqOn _ _ _⟩
  exact (isMIntegralCurveOn_piecewise hv hγ hβ
    ⟨⟨ht₁a, ht₁b⟩, ⟨by linarith, by linarith⟩⟩ hβ0.symm).mono
      (union_comm _ _ ▸ Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) le_rfl)

/-- **The finite-endpoint extension criterion at the left endpoint**, sequential form. If
`u n → a`, the sequence is eventually above `a`, and `γ (u n) → y`, then `γ` extends before `a`. -/
theorem exists_lt_isMIntegralCurveOn_Ioo_of_tendsto
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, a < u n) (hub : Tendsto u atTop (𝓝 a))
    (hy : Tendsto (γ ∘ u) atTop (𝓝 y)) :
    ∃ c < a, ∃ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo c b) ∧ EqOn δ γ (Ioo a b) := by
  refine hγ.exists_lt_isMIntegralCurveOn_Ioo hab hv (ClusterPt.mono hy.mapClusterPt ?_)
  exact map_mono (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hub hu)

/-- **The escape lemma at the left endpoint.** An integral curve on `Ioo a b` that admits no
extension before its finite left endpoint eventually leaves every compact set as `t → a⁺`. -/
theorem eventually_notMem_nhdsGT
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (hab : a < b)
    (hv : CMDiff 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hmax : ∀ c < a, ∀ δ : ℝ → M, IsMIntegralCurveOn δ v (Ioo c b) → ¬EqOn δ γ (Ioo a b))
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[>] a, γ t ∉ K := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_not] at h
  obtain ⟨z, _, hz⟩ := hK.exists_mapClusterPt_of_frequently h
  obtain ⟨c, hc, δ, hδ, hδeq⟩ := hγ.exists_lt_isMIntegralCurveOn_Ioo hab hv hz
  exact hmax c hc δ hδ hδeq

end IsMIntegralCurveOn
