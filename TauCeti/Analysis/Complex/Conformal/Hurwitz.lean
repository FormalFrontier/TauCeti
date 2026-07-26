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

The corollary usually quoted alongside it is the injectivity form: a locally uniform limit of
*injective* holomorphic functions is injective or constant. That is the version the Riemann mapping
theorem consumes. It is proved here directly rather than by applying `hurwitz` to the differences
`F n - F n b` on the punctured domain `Ω \ {b}`, since that route needs the punctured set to be
connected — a fact Mathlib does not currently supply for an open connected subset of `ℂ`.

## Main results

* `TauCeti.hurwitz` — a locally uniform limit of nowhere-vanishing holomorphic functions on a
  connected open set is nowhere vanishing or identically zero.
* `TauCeti.hurwitz_injOn` — a locally uniform limit of injective holomorphic functions is injective
  or constant.

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

/-- If `g - v` has an isolated zero at `a` inside a disc, then for all large `n` the approximant
`F n` also attains the value `v` in that disc. This is the Rouché step behind `hurwitz_injOn`. -/
private lemma eventually_exists_eq {Ω : Set ℂ} {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hΩ : IsOpen Ω) (hg : AnalyticOnNhd ℂ g Ω)
    (hconv : TendstoLocallyUniformlyOn F g atTop Ω)
    {a v : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall a ρ ⊆ Ω)
    (hga : g a = v) (hzf : ∀ z ∈ closedBall a ρ, z ≠ a → g z ≠ v) :
    ∀ᶠ n in atTop, ∃ z ∈ ball a ρ, F n z = v := by
  have hA : AnalyticOnNhd ℂ (fun ζ => g ζ - v) (closedBall a ρ) :=
    (hg.mono hball).sub analyticOnNhd_const
  have hzne : ∀ z ∈ sphere a ρ, z ≠ a := by
    intro z hz h
    rw [h] at hz
    simp only [mem_sphere, dist_self] at hz
    linarith
  have hsphne : ∀ z ∈ sphere a ρ, g z - v ≠ 0 := fun z hz =>
    sub_ne_zero.mpr (hzf z (sphere_subset_closedBall hz) (hzne z hz))
  have hcpt : IsCompact (sphere a ρ) := isCompact_sphere _ _
  have hsne : (sphere a ρ).Nonempty := NormedSpace.sphere_nonempty.mpr hρ.le
  have hcont : ContinuousOn (fun z => ‖g z - v‖) (sphere a ρ) :=
    (((hA.continuousOn).mono sphere_subset_closedBall)).norm
  obtain ⟨u, hu, humin⟩ := hcpt.exists_isMinOn hsne hcont
  have hδ : 0 < ‖g u - v‖ := norm_pos_iff.mpr (hsphne u hu)
  have hconvS : TendstoUniformlyOn F g atTop (sphere a ρ) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hcpt).mp
      (hconv.mono ((sphere_subset_closedBall).trans hball))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconvS _ hδ] with n hn
  have hB : AnalyticOnNhd ℂ (fun ζ => F n ζ - v) (closedBall a ρ) :=
    (((hF n).analyticOnNhd hΩ).mono hball).sub analyticOnNhd_const
  have hs : ∀ z ∈ sphere a ρ, ‖(g z - v) - (F n z - v)‖ < ‖g z - v‖ := by
    intro z hz
    have he : (g z - v) - (F n z - v) = g z - F n z := by ring
    rw [he]
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hn z hz) (humin hz)
  have hcount := rouche hρ hA hB hs
  have htop : analyticOrderAt (fun ζ => g ζ - v) a ≠ ⊤ := by
    intro hev
    rw [analyticOrderAt_eq_top] at hev
    obtain ⟨ε, hε, hbl⟩ := Metric.eventually_nhds_iff.mp hev
    set t : ℝ := min ε ρ / 2 with ht_def
    have ht0 : 0 < t := by rw [ht_def]; exact half_pos (lt_min hε hρ)
    have htε : t < ε := by have h := min_le_left ε ρ; rw [ht_def]; linarith
    have htρ : t ≤ ρ := by have h := min_le_right ε ρ; rw [ht_def]; linarith
    have hdist : dist (a + (t : ℂ)) a = t := by simp [dist_eq_norm, abs_of_pos ht0]
    refine hzf (a + (t : ℂ)) ?_ ?_ (sub_eq_zero.mp (hbl ?_))
    · simp only [mem_closedBall, hdist]; exact htρ
    · simp only [ne_eq, add_eq_left, Complex.ofReal_eq_zero]; exact ht0.ne'
    · rw [hdist]; exact htε
  have hord : analyticOrderNatAt (fun ζ => g ζ - v) a ≠ 0 := by
    have h0 : analyticOrderAt (fun ζ => g ζ - v) a ≠ 0 := fun h =>
      ((hA a (mem_closedBall_self hρ.le)).analyticOrderAt_eq_zero.mp h) (by simp [hga])
    simpa [analyticOrderNatAt] using fun h => h0 ((ENat.toNat_eq_zero.mp h).resolve_right htop)
  have hne0 : (∑ᶠ z ∈ ball a ρ, analyticOrderNatAt (fun ζ => F n ζ - v) z) ≠ 0 := by
    rw [← hcount]
    exact fun h => hord (Nat.le_zero.mp (h ▸ le_count hA (mem_ball_self hρ)))
  by_contra hcon
  push Not at hcon
  exact hne0 (count_eq_zero hB (fun z hz => sub_ne_zero.mpr (hcon z hz)))

/-- **Hurwitz's theorem for injectivity.** On a connected open set, a locally uniform limit of
*injective* holomorphic functions is either injective or constant.

This is the form the Riemann mapping theorem consumes: it is what keeps the extremal map injective
in the limit. Both alternatives genuinely occur — the injective maps `z ↦ z / (n + 1)` converge
locally uniformly to the constant `0`.

The proof does not route through `hurwitz` on the punctured domain `Ω \ {b}`, which would need
that set to be connected — a fact Mathlib does not currently provide for an open connected subset
of `ℂ`. Instead, if `g` were non-constant with `g a = g b` for `a ≠ b`, we place disjoint discs
about `a` and `b` and use `eventually_exists_eq` on each: for large `n` the injective `F n` would
attain the single value `g a` in both discs, hence at two distinct points. -/
theorem hurwitz_injOn {Ω : Set ℂ} (hΩ : IsOpen Ω) (hconn : IsConnected Ω) {F : ℕ → ℂ → ℂ}
    {g : ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) Ω) (hg : DifferentiableOn ℂ g Ω)
    (hconv : TendstoLocallyUniformlyOn F g atTop Ω)
    (hinj : ∀ n, Set.InjOn (F n) Ω) :
    Set.InjOn g Ω ∨ ∃ v, ∀ z ∈ Ω, g z = v := by
  have hgA : AnalyticOnNhd ℂ g Ω := hg.analyticOnNhd hΩ
  by_cases hconst : ∃ v, ∀ z ∈ Ω, g z = v
  · exact Or.inr hconst
  refine Or.inl fun a ha b hb hab => ?_
  by_contra hne
  -- around any point where `g` takes the value `g a`, that value is taken only there
  have hiso : ∀ x ∈ Ω, g x = g a → ∀ σ > 0, ∃ ρ > 0, ρ ≤ σ ∧ closedBall x ρ ⊆ Ω ∧
      ∀ z ∈ closedBall x ρ, z ≠ x → g z ≠ g a := by
    intro x hx _ σ hσ
    have hpunct : ∀ᶠ z in 𝓝[≠] x, g z ≠ g a := by
      rcases ((hgA.sub analyticOnNhd_const) x hx).eventually_eq_zero_or_eventually_ne_zero with
        h | h
      · exfalso
        have heq := (hgA.sub analyticOnNhd_const).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          hconn.isPreconnected hx (by filter_upwards [h] with z hz using hz)
        exact hconst ⟨g a, fun z hz => sub_eq_zero.mp (heq hz)⟩
      · filter_upwards [h] with z hz using sub_ne_zero.mp hz
    obtain ⟨ε₁, hε₁, h₁⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hpunct)
    obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp hΩ x hx
    refine ⟨min (min (ε₁ / 2) (ε₂ / 2)) σ, lt_min (lt_min (by linarith) (by linarith)) hσ,
      min_le_right _ _, fun z hz => ?_, fun z hz hzx => ?_⟩
    · refine h₂ (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) ?_))
      exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith)
    · refine h₁ (lt_of_le_of_lt (mem_closedBall.mp hz) ?_) (by simpa using hzx)
      exact lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hd : 0 < dist a b := dist_pos.mpr hne
  obtain ⟨ρa, hρa, hρa3, hballa, hzfa⟩ := hiso a ha rfl (dist a b / 3) (by linarith)
  obtain ⟨ρb, hρb, hρb3, hballb, hzfb⟩ := hiso b hb hab.symm (dist a b / 3) (by linarith)
  obtain ⟨n, ⟨z₁, hz₁, hFz₁⟩, ⟨z₂, hz₂, hFz₂⟩⟩ :=
    ((eventually_exists_eq hF hΩ hgA hconv hρa hballa rfl hzfa).and
      (eventually_exists_eq hF hΩ hgA hconv hρb hballb hab.symm hzfb)).exists
  have hz₁₂ : z₁ ≠ z₂ := by
    rintro rfl
    have h1 : dist a z₁ < ρa := by rw [dist_comm]; exact mem_ball.mp hz₁
    have h2 : dist z₁ b < ρb := mem_ball.mp hz₂
    have h3 := dist_triangle a z₁ b
    linarith
  exact hz₁₂ (hinj n (hballa (ball_subset_closedBall hz₁)) (hballb (ball_subset_closedBall hz₂))
    (hFz₁.trans hFz₂.symm))

end TauCeti
