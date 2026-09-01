/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Topology.OmegaLimit
-- Private: the mean value inequality, Heine--Cantor, monotone convergence and the comparison of
-- interval integrals are used only inside proofs; no declaration below exposes their APIs.
import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Transform
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Convergence of a negative gradient trajectory

A negative gradient trajectory `γ` of `f`, followed forward in time and never leaving a compact
set `K`, **converges** to a critical point of `f` provided that `f` has only finitely many critical
points in `K`:

`∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p)`.

This is the statement that makes the moduli spaces of the Morse complex — the trajectories running
from one critical point to another — well defined objects at all, and it is where Lane M of the
analytic Heegaard Floer roadmap turns the dynamical facts of
`TauCeti/Analysis/Calculus/Morse/GradientFlow.lean` into the beginnings of a chain complex.

Some hypothesis beyond compactness is needed to pin the limit down. For a merely smooth `f` a
negative gradient trajectory can spiral forever towards a circle of critical points, its ω-limit
set being the whole circle and the trajectory having no limit at all; for an analytic `f` this is
ruled out by Łojasiewicz's gradient inequality, and here it is ruled out by the Morse condition.
The theorem below therefore assumes that `f` has only **finitely many critical points** in `K`,
which is exactly what a Morse function on a compact set provides, by
`TauCeti.HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero`.

## The argument

The three steps are the classical ones (Audin--Damian, Chapter 2).

*The energy converges.* Along the trajectory `f` is antitone
(`TauCeti.IsIntegralCurveOn.antitoneOn_comp_neg_gradient`) and is bounded below on `K`, so
`f ∘ γ` has a limit.

*The gradient dies.* The trajectory is Lipschitz, with the bound on `‖∇ f‖` over `K` as its
constant, and `∇ f` is uniformly continuous on `K`; so if `‖∇ f (γ t)‖ ≥ ε` at some time `t`, the
same holds with `ε / 2` throughout a time interval `[t, t + δ]` whose length `δ` does not depend on
`t`. The energy identity `TauCeti.IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` then makes
`f` drop by at least `δ (ε / 2) ^ 2` across that interval — impossible infinitely often, since the
energy converges. Hence `∇ f (γ t) → 0`.

*The ω-limit set is a point.* Every cluster point of `γ` along `atTop` is therefore a critical
point in `K`, so the ω-limit set is finite; and it is preconnected, by
`TauCeti.isPreconnected_setOf_mapClusterPt_atTop`. A finite preconnected set is a single point, and
a map into a compact set with a unique cluster point converges to it.

## Main results

* `TauCeti.IsIntegralCurveOn.exists_tendsto_comp_atTop`: the energy `f ∘ γ` converges.
* `TauCeti.IsIntegralCurveOn.tendsto_gradient_atTop`: the gradient along the trajectory tends
  to `0`.
* `TauCeti.IsIntegralCurveOn.gradient_eq_zero_of_mapClusterPt`: every point of the ω-limit set is
  a critical point.
* `TauCeti.IsIntegralCurveOn.exists_tendsto_atTop`: **a confined negative gradient trajectory
  converges to a critical point**, when the critical points in the confining compact set are
  finite in number.
* `TauCeti.IsIntegralCurveOn.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn`: the Morse
  form of the same statement, where the finiteness comes from nondegeneracy.
* `TauCeti.IsIntegralCurveOn.exists_tendsto_atBot`: the corresponding backward-time statement.
* `TauCeti.IsIntegralCurveOn.exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn`: its Morse
  form, where finiteness follows from nondegeneracy.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* S. Łojasiewicz, *Ensembles semi-analytiques*, IHÉS, 1965, for the gradient inequality that
  replaces the finiteness hypothesis used here when `f` is analytic.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace MeasureTheory Metric Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {K : Set E} {x : E}

namespace IsIntegralCurveOn

/-! ### The trajectory is Lipschitz -/

/-- **A negative gradient trajectory confined to a compact set is Lipschitz**, with any bound for
the gradient on that set as its constant: the velocity is the negative gradient and therefore has
the same norm as the gradient. -/
theorem norm_sub_le_of_norm_gradient_le {C : ℝ}
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hmaps : MapsTo γ (Ici 0) K)
    (hC : ∀ y ∈ K, ‖∇ f y‖ ≤ C) {s t : ℝ} (hs : s ∈ Ici (0 : ℝ)) (ht : t ∈ Ici (0 : ℝ)) :
    ‖γ t - γ s‖ ≤ C * ‖t - s‖ :=
  (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr ↦ hγ r hr)
    (fun r hr ↦ by simpa using hC _ (hmaps hr)) hs ht

/-! ### The energy converges -/

/-- **The value of `f` along a confined negative gradient trajectory converges.** It is antitone
along the trajectory and bounded below on the compact set the trajectory never leaves. -/
theorem exists_tendsto_comp_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y) :
    ∃ c, Tendsto (fun t ↦ f (γ t)) atTop (𝓝 c) := by
  have hanti : AntitoneOn (f ∘ γ) (Ici 0) :=
    antitoneOn_comp_neg_gradient hγ (convex_Ici 0) fun t ht ↦ hdiff _ (hmaps ht)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    fun y hy ↦ (hdiff y hy).continuousAt.continuousWithinAt
  -- Extend the trajectory backwards by its initial value, so that the antitonicity is global.
  have hgA : Antitone fun t ↦ f (γ (max t 0)) := fun a b hab ↦
    hanti (mem_Ici.mpr (le_max_right a 0)) (mem_Ici.mpr (le_max_right b 0))
      (max_le_max hab le_rfl)
  have hgB : BddBelow (Set.range fun t ↦ f (γ (max t 0))) := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h := hM _ (hmaps (mem_Ici.mpr (le_max_right t 0)))
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (f (γ (max t 0)))]
  refine ⟨⨅ t, f (γ (max t 0)), Tendsto.congr' ?_ (tendsto_atTop_ciInf hgA hgB)⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [max_eq_left ht]

/-! ### The gradient dies along the trajectory -/

/-- **The gradient tends to zero along a confined negative gradient trajectory.**

The trajectory is Lipschitz and `∇ f` is uniformly continuous on the compact set it stays in, so a
time at which `‖∇ f (γ t)‖` is at least `ε` is the start of a time interval of a fixed length `δ`
on which it is at least `ε / 2`. Across such an interval the energy identity makes `f` drop by at
least `δ (ε / 2) ^ 2`; but the drops of `f` across intervals of fixed length tend to `0`, because
`f` converges along the trajectory. So the times at which `‖∇ f (γ t)‖ ≥ ε` are bounded. -/
theorem tendsto_gradient_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) :
    Tendsto (fun t ↦ ∇ f (γ t)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_tendsto_comp_atTop hγ hK hmaps hdiff
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgrad
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC _ (hmaps (mem_Ici.mpr le_rfl)))
  have hcontg : ContinuousOn (fun t ↦ ∇ f (γ t)) (Ici 0) := hgrad.comp hγ.continuousOn hmaps
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hgrad) (ε / 2) (by positivity)
  set δ : ℝ := η / (C + 1) with hδdef
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hCδ : C * δ < η := by
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 < δ * (ε / 2) ^ 2 := by positivity
  -- Across a time interval of length `δ` starting at a time where the gradient is large, the
  -- energy drops by a definite amount.
  have key : ∀ t : ℝ, 0 ≤ t → ε ≤ ‖∇ f (γ t)‖ → δ * (ε / 2) ^ 2 ≤ f (γ t) - f (γ (t + δ)) := by
    intro t ht hbig
    have htδ : t ≤ t + δ := by linarith
    have hIcc : Icc t (t + δ) ⊆ Ici (0 : ℝ) := fun s hs ↦ mem_Ici.mpr (ht.trans hs.1)
    have huIcc : [[t, t + δ]] = Icc t (t + δ) := uIcc_of_le htδ
    have hlow : ∀ s ∈ Icc t (t + δ), ε / 2 ≤ ‖∇ f (γ s)‖ := by
      intro s hs
      have hs0 : s ∈ Ici (0 : ℝ) := hIcc hs
      have hnorm : ‖s - t‖ ≤ δ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.1])]
        linarith [hs.2]
      have hdist : dist (γ s) (γ t) < η := by
        rw [dist_eq_norm]
        calc ‖γ s - γ t‖ ≤ C * ‖s - t‖ :=
              norm_sub_le_of_norm_gradient_le hγ hmaps hC (mem_Ici.mpr ht) hs0
          _ ≤ C * δ := by nlinarith
          _ < η := hCδ
      have h := hUC _ (hmaps hs0) _ (hmaps (mem_Ici.mpr ht)) hdist
      rw [dist_eq_norm] at h
      have h' : ‖∇ f (γ t)‖ - ‖∇ f (γ s)‖ ≤ ‖∇ f (γ s) - ∇ f (γ t)‖ := by
        rw [norm_sub_rev]
        exact norm_sub_norm_le _ _
      linarith
    have hint : IntervalIntegrable (fun s ↦ ‖∇ f (γ s)‖ ^ 2) volume t (t + δ) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [huIcc]
      exact ((hcontg.mono hIcc).norm).pow 2
    have heq : ∫ s in t..(t + δ), ‖∇ f (γ s)‖ ^ 2 = f (γ t) - f (γ (t + δ)) :=
      integral_norm_gradient_sq_eq_sub hγ (huIcc ▸ hIcc)
        (fun s hs ↦ hdiff _ (hmaps (hIcc (huIcc ▸ hs)))) hint
    rw [← heq]
    have hmono : ∫ _s in t..(t + δ), (ε / 2) ^ 2 ≤ ∫ s in t..(t + δ), ‖∇ f (γ s)‖ ^ 2 :=
      intervalIntegral.integral_mono_on htδ intervalIntegrable_const hint fun s hs ↦
        pow_le_pow_left₀ (by positivity) (hlow s hs) 2
    simpa using hmono
  -- The drops of the energy across intervals of length `δ` tend to `0`.
  have hdrop : Tendsto (fun t ↦ f (γ t) - f (γ (t + δ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t ↦ f (γ (t + δ))) atTop (𝓝 c) :=
      hc.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    simpa using hc.sub h2
  obtain ⟨t, hbig, ht0, hlt⟩ :=
    (hcon.and_eventually ((eventually_ge_atTop (0 : ℝ)).and
      (hdrop.eventually (gt_mem_nhds hpos)))).exists
  exact absurd (key t ht0 (not_lt.mp hbig)) (not_le.mpr hlt)

/-! ### The ω-limit set -/

/-- **Every cluster point of a confined negative gradient trajectory is a critical point.** The
gradient tends to `0` along the trajectory, so the trajectory eventually lies in the closed set
where `‖∇ f‖ ≤ ε`, and hence so does every one of its cluster points. -/
theorem gradient_eq_zero_of_mapClusterPt
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hx : MapClusterPt x atTop γ) :
    ∇ f x = 0 := by
  have hzero := tendsto_gradient_atTop hγ hK hmaps hdiff hgrad
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (norm_nonneg _))
  have hcl : IsClosed (K ∩ (∇ f) ⁻¹' closedBall 0 ε) :=
    hgrad.preimage_isClosed_of_isClosed hK.isClosed isClosed_closedBall
  have hmem : K ∩ (∇ f) ⁻¹' closedBall 0 ε ∈ map γ atTop := by
    rw [mem_map]
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      NormedAddGroup.tendsto_nhds_zero.mp hzero ε hε] with t ht hlt
    exact ⟨hmaps (mem_Ici.mpr ht), mem_closedBall_zero_iff.mpr hlt.le⟩
  have hmemx := hcl.mem_of_mapClusterPt hx hmem
  rw [Set.mem_inter_iff, Set.mem_preimage, mem_closedBall_zero_iff] at hmemx
  linarith [hmemx.2]

/-! ### Convergence -/

/-- **A negative gradient trajectory that never leaves a compact set converges to a critical point
of `f` in it**, provided `f` has only finitely many critical points there.

Some such hypothesis is needed: a negative gradient trajectory can spiral forever towards a circle
of critical points and then have no limit, its ω-limit set being the whole circle. The finiteness
holds for a Morse function, which is
`TauCeti.IsIntegralCurveOn.exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn` below.

Nothing is claimed about the *rate* of convergence, nor about the backward limit: the reversed
curve `fun t ↦ γ (-t)` is a negative gradient trajectory of `-f`, so the backward limit is this
same theorem applied to `-f`, whose hypotheses have to be checked separately. -/
theorem exists_tendsto_atTop
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hfin : {y ∈ K | ∇ f y = 0}.Finite) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p) := by
  obtain ⟨p, hpK, hp⟩ := hK.exists_mapClusterPt
    (le_principal_iff.mpr (mem_map.mpr (mem_of_superset (Ici_mem_atTop 0) hmaps)))
  -- The ω-limit set consists of critical points, so it is finite; and it is preconnected.
  have hsub : {y | MapClusterPt y atTop γ} ⊆ {y ∈ K | ∇ f y = 0} := fun y hy ↦
    ⟨hK.isClosed.mem_of_mapClusterPt hy
        (mem_map.mpr (mem_of_superset (Ici_mem_atTop 0) hmaps)),
      gradient_eq_zero_of_mapClusterPt hγ hK hmaps hdiff hgrad hy⟩
  have hconn : IsPreconnected {y | MapClusterPt y atTop γ} :=
    isPreconnected_setOf_mapClusterPt_atTop hK hγ.continuousOn hmaps
  -- A finite preconnected set is a single point.
  have hone : ∀ y ∈ K, MapClusterPt y atTop γ → y = p := by
    intro y _ hy
    by_contra hne
    obtain ⟨z, -, hz1, hz2⟩ := isPreconnected_closed_iff.mp hconn {p}
      ({y | MapClusterPt y atTop γ} \ {p}) isClosed_singleton
      (((hfin.subset hsub).sdiff).isClosed)
      (fun w hw ↦ (em (w = p)).imp id fun hwp ↦ ⟨hw, hwp⟩)
      ⟨p, hp, rfl⟩ ⟨y, hy, hy, hne⟩
    exact hz2.2 hz1
  exact ⟨p, hpK, (hsub hp).2,
    hK.tendsto_nhds_of_unique_mapClusterPt
      (by filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht using hmaps (mem_Ici.mpr ht))
      hone⟩

/-- **The Morse form of the convergence theorem.** A negative gradient trajectory confined to a
compact set on which `fderiv ℝ f` is continuous and every critical point of `f` is nondegenerate
converges to a critical point of `f` in that set.

Nondegeneracy enters only through the finiteness of the critical locus, which is
`TauCeti.HasNondegenerateCriticalPointsOn.finite_setOfPred_fderiv_eq_zero`; the differentiability
and the continuity of the gradient are read off the continuity of `fderiv ℝ f` on `K`, the
gradient being the differential transported by the Riesz isometry. -/
theorem exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Ici 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Ici 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hfderiv : ContinuousOn (fderiv ℝ f) K) (hM : HasNondegenerateCriticalPointsOn f K) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atTop (𝓝 p) := by
  have hgradeq : ∇ f = fun y ↦ (toDual ℝ E).symm (fderiv ℝ f y) := by
    funext y
    rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := y), LinearIsometryEquiv.symm_apply_apply]
  have hzero : ∀ y : E, ∇ f y = 0 ↔ fderiv ℝ f y = 0 := fun y ↦ by
    rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := y), map_eq_zero_iff _ (toDual ℝ E).injective]
  refine exists_tendsto_atTop hγ hK hmaps hdiff ?_ ?_
  · rw [hgradeq]
    exact (toDual ℝ E).symm.continuous.comp_continuousOn hfderiv
  · exact (hM.finite_setOfPred_fderiv_eq_zero hK hfderiv).subset
      fun y hy ↦ ⟨hy.1, (hzero y).mp hy.2⟩

/-- **A negative gradient trajectory confined to a compact set converges backwards to a critical
point**, provided the critical locus in that set is finite.  Under these compactness, regularity,
and finiteness hypotheses, this is the backward-time counterpart of `exists_tendsto_atTop` and
gives a critical endpoint as `t` tends to `-∞`.
-/
theorem exists_tendsto_atBot
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Iic 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hgrad : ContinuousOn (∇ f) K) (hfin : {y ∈ K | ∇ f y = 0}.Finite) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atBot (𝓝 p) := by
  have hgrad_neg : ∀ y : E, ∇ (-f) y = -∇ f y := by
    intro y
    simpa using (gradient_const_smul (𝕜 := ℝ) (F := E) (f := f) (x := y) (-1))
  have hγ_rev := hγ.comp_mul (-1)
  have hdomain : {t : ℝ | t * (-1) ∈ Iic (0 : ℝ)} = Ici 0 := by
    ext t
    simp only [mem_Iic, mem_Ici]
    constructor
    · intro ht
      exact neg_nonpos.mp (by simpa using ht)
    · intro ht
      simpa using (neg_nonpos.mpr ht)
  have hfield :
      ((-1 : ℝ) • (fun _ x ↦ -∇ f x)) ∘ (fun t : ℝ ↦ t * (-1)) =
    (fun _ x ↦ -∇ (-f) x) := by
    funext t y
    simp only [Function.comp_apply, neg_one_smul, Pi.neg_apply, hgrad_neg, neg_neg]
  have hγ_rev' :
      IsIntegralCurveOn (γ ∘ (fun t : ℝ ↦ t * (-1)))
        (fun _ x ↦ -∇ (-f) x) (Ici 0) := by
    rw [← hdomain, ← hfield]
    exact hγ_rev
  have hmaps_rev : MapsTo (γ ∘ (fun t : ℝ ↦ t * (-1))) (Ici 0) K := by
    intro t ht
    apply hmaps
    simp only [mem_Iic]
    simpa using (neg_nonpos.mpr (mem_Ici.mp ht))
  have hdiff_neg : ∀ y ∈ K, DifferentiableAt ℝ (-f) y := by
    intro y hy
    simpa only [Pi.neg_apply] using (hdiff y hy).neg
  have hgrad_neg_fun : ∇ (-f) = -∇ f := funext hgrad_neg
  have hgrad_neg_cont : ContinuousOn (∇ (-f)) K := by
    rw [hgrad_neg_fun]
    exact hgrad.neg
  have hfin_neg : {y ∈ K | ∇ (-f) y = 0}.Finite := by
    simpa only [hgrad_neg, neg_eq_zero] using hfin
  obtain ⟨p, hpK, hp, hp_lim⟩ := exists_tendsto_atTop hγ_rev' hK hmaps_rev hdiff_neg
    hgrad_neg_cont hfin_neg
  refine ⟨p, hpK, ?_, ?_⟩
  · simpa only [hgrad_neg, neg_eq_zero] using hp
  · simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using
      hp_lim.comp tendsto_neg_atBot_atTop

/-- **The Morse form of backward convergence.** A negative gradient trajectory confined to a
compact set on which `fderiv ℝ f` is continuous and every critical point is nondegenerate converges
backwards to a critical point in that set.

As in `exists_tendsto_atTop_of_hasNondegenerateCriticalPointsOn`, nondegeneracy is used only to
obtain finiteness of the critical locus. -/
theorem exists_tendsto_atBot_of_hasNondegenerateCriticalPointsOn
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) (Iic 0)) (hK : IsCompact K)
    (hmaps : MapsTo γ (Iic 0) K) (hdiff : ∀ y ∈ K, DifferentiableAt ℝ f y)
    (hfderiv : ContinuousOn (fderiv ℝ f) K) (hM : HasNondegenerateCriticalPointsOn f K) :
    ∃ p ∈ K, ∇ f p = 0 ∧ Tendsto γ atBot (𝓝 p) := by
  have hzero : ∀ y : E, ∇ f y = 0 ↔ fderiv ℝ f y = 0 := fun y ↦ by
    rw [← toDual_gradient (𝕜 := ℝ) (f := f) (x := y),
      map_eq_zero_iff _ (toDual ℝ E).injective]
  apply exists_tendsto_atBot hγ hK hmaps hdiff
    ((toDual ℝ E).symm.continuous.comp_continuousOn hfderiv)
  exact (hM.finite_setOfPred_fderiv_eq_zero hK hfderiv).subset
    fun y hy ↦ ⟨hy.1, (hzero y).mp hy.2⟩

end IsIntegralCurveOn

end TauCeti
