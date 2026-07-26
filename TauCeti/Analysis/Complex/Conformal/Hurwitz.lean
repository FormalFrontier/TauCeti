/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import TauCeti.Analysis.Complex.Conformal.Rouche
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Hurwitz's theorem

A locally uniform limit of nowhere-vanishing holomorphic functions on a connected open set is
either nowhere vanishing or identically zero. This is the second target of layer
**L0 (the local-mapping engine)** of the conformal-mapping roadmap, and the perturbation backbone
for the injectivity step of the Riemann mapping theorem.

The proof is the classical Rouché argument. If the limit `g` is not identically zero but vanishes
at `z₀`, then `g` does not vanish identically near `z₀` — otherwise the identity theorem would
force `g = 0` on all of `Ω` — so `g` is zero-free on some punctured ball about `z₀`. Pick a circle
inside that ball; `‖g‖` attains a positive minimum `δ` on it by compactness, and locally uniform
convergence supplies an `n` with `‖g - F n‖ < δ ≤ ‖g‖` there. That is exactly Rouché's hypothesis,
so `g` and `F n` have equal zero counts inside the circle. But `F n` has none, while `g` has a zero
of positive order at `z₀` — a contradiction.

## Main results

* `TauCeti.hurwitz` — a locally uniform limit of nowhere-vanishing holomorphic functions on a
  connected open set is nowhere vanishing or identically zero.

## Coordination with upstream Mathlib

Mathlib has no Hurwitz theorem. However, per the *Coordination with upstream Mathlib* section of
`ConformalMapping/README.md`, this layer overlaps
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which proves this material internally as the private
lemma `eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`. **This file is therefore a
temporary shim**: once the corresponding Mathlib lemma lands, this statement should be backed by it
— or deleted and its consumers refactored — rather than maintained as an independent re-proof. What
Tau Ceti adds at L0 is named, discoverable API, not first proof.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII.
-/

public section

open Complex Metric Filter Topology

namespace TauCeti

variable {c : ℂ} {R : ℝ}

/-- A function holomorphic and zero-free on the open disc has zero count `0` there. -/
private lemma count_eq_zero {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ ball c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 := by
  refine finsum_mem_of_eqOn_zero (fun z hz => ?_)
  simp [analyticOrderNatAt,
    (hf z (ball_subset_closedBall hz)).analyticOrderAt_eq_zero.2 (hne z hz)]

/-- The order of vanishing at a single point of the open disc is at most the total zero count.
Both sides read `0` at a point of infinite order, so the bound is trivially true there too. -/
private lemma le_count {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (closedBall c R))
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) :
    analyticOrderNatAt g z₀ ≤ ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z := by
  classical
  set S := (MeromorphicOn.divisor_ball_support_finite hg.meromorphicOn).toFinset with hS
  have hgb : AnalyticOnNhd ℂ g (ball c R) := hg.mono ball_subset_closedBall
  have hmemS : ∀ z ∈ ball c R, analyticOrderNatAt g z ≠ 0 → z ∈ S := by
    intro z hz hne
    have : MeromorphicOn.divisor g (ball c R) z ≠ 0 := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hgb hz]
      cases h : analyticOrderAt g z with
      | top => simp [analyticOrderNatAt, h] at hne
      | coe n => simpa [analyticOrderNatAt, h] using hne
    simpa [hS, Set.Finite.mem_toFinset] using this
  have hsub : (S : Set ℂ) ⊆ ball c R := fun z hz =>
    (MeromorphicOn.divisor g (ball c R)).supportWithinDomain
      (by simpa [hS, Set.Finite.mem_toFinset] using hz)
  have h2 : (∑ᶠ z ∈ ball c R, analyticOrderNatAt g z) = ∑ z ∈ S, analyticOrderNatAt g z := by
    refine finsum_mem_eq_sum_of_subset _ (fun z hz => ?_) hsub
    obtain ⟨hzb, hzs⟩ := hz
    simp only [Function.mem_support, ne_eq] at hzs
    exact hmemS z hzb hzs
  rw [h2]
  by_cases h0 : analyticOrderNatAt g z₀ = 0
  · simp [h0]
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (hmemS z₀ hz₀ h0)

/-- **Hurwitz's theorem.** On a connected open set, a locally uniform limit of holomorphic
functions that are nowhere zero is itself either nowhere zero or identically zero.

The dichotomy is genuine: the constant sequence `F n = 1 / (n + 1)` on any `Ω` converges locally
uniformly to `0`, so the second alternative cannot be dropped. -/
theorem hurwitz {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsConnected Ω) {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hg : DifferentiableOn ℂ g Ω)
    (hconv : TendstoLocallyUniformlyOn F g atTop Ω)
    (hne : ∀ n, ∀ z ∈ Ω, F n z ≠ 0) :
    (∀ z ∈ Ω, g z ≠ 0) ∨ (∀ z ∈ Ω, g z = 0) := by
  have hgA : AnalyticOnNhd ℂ g Ω := hg.analyticOnNhd hΩ
  by_cases hzero : Set.EqOn g 0 Ω
  · exact Or.inr fun z hz => hzero hz
  refine Or.inl fun z₀ hz₀Ω hgz₀ => ?_
  -- `g` does not vanish identically near `z₀`, else the identity theorem kills it on all of `Ω`
  have htop : analyticOrderAt g z₀ ≠ ⊤ := fun h =>
    hzero (hgA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn.isPreconnected hz₀Ω
      (by
        have := analyticOrderAt_eq_top.mp h
        filter_upwards [this] with z hz using hz))
  -- so `g` is zero-free on some punctured ball about `z₀`
  have hpunct : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 := by
    rcases (hgA z₀ hz₀Ω).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) htop
    · exact h
  obtain ⟨ε₁, hε₁, hne₁⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀Ω
  set r := min (ε₁ / 2) (ε₂ / 2) with hr_def
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hcb : closedBall z₀ r ⊆ Ω := fun z hz =>
    hball₂ (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz)
      (lt_of_le_of_lt (min_le_right _ _) (by linarith))))
  have hsph : sphere z₀ r ⊆ closedBall z₀ r := sphere_subset_closedBall
  have hgne : ∀ z ∈ sphere z₀ r, g z ≠ 0 := by
    intro z hz
    have hdz : dist z z₀ = r := mem_sphere.mp hz
    refine hne₁ ?_ ?_
    · rw [hdz]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      rw [h] at hdz
      simp only [dist_self] at hdz
      linarith
  -- `‖g‖` attains a positive minimum on the circle
  have hcpt : IsCompact (sphere z₀ r) := isCompact_sphere _ _
  have hsne : (sphere z₀ r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
  have hgcont : ContinuousOn (fun z => ‖g z‖) (sphere z₀ r) :=
    ((hgA.continuousOn).mono (hsph.trans hcb)).norm
  obtain ⟨w, hw, hwmin⟩ := hcpt.exists_isMinOn hsne hgcont
  have hδ : 0 < ‖g w‖ := norm_pos_iff.mpr (hgne w hw)
  -- locally uniform convergence gives an `n` with `‖g - F n‖ < ‖g‖` on the circle
  have hconvS : TendstoUniformlyOn F g atTop (sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcpt).mp
      (hconv.mono (hsph.trans hcb))
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hconvS _ hδ).exists
  have hgA' : AnalyticOnNhd ℂ g (closedBall z₀ r) := hgA.mono hcb
  have hFA' : AnalyticOnNhd ℂ (F n) (closedBall z₀ r) := ((hF n).analyticOnNhd hΩ).mono hcb
  have hs : ∀ z ∈ sphere z₀ r, ‖g z - F n z‖ < ‖g z‖ := fun z hz =>
    lt_of_lt_of_le (by simpa [dist_eq_norm] using hn z hz) (hwmin hz)
  -- Rouché: the counts agree, yet `F n` has no zeros and `g` has one at `z₀`
  have hcount := rouche hr hgA' hFA' hs
  rw [count_eq_zero hFA' (fun z hz => hne n z (hcb (ball_subset_closedBall hz)))] at hcount
  have hle := le_count hgA' (mem_ball_self hr)
  rw [hcount] at hle
  have h0 : analyticOrderAt g z₀ = 0 :=
    (ENat.toNat_eq_zero.mp (by simpa [analyticOrderNatAt] using Nat.le_zero.mp hle)).resolve_right
      htop
  exact (hgA z₀ hz₀Ω).analyticOrderAt_eq_zero.mp h0 hgz₀

end TauCeti
