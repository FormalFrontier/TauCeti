/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import TauCeti.Analysis.Complex.Conformal.Rouche
public import TauCeti.Analysis.Complex.IsolatedZero
public import TauCeti.Analysis.Complex.ZeroCount
import Mathlib.Analysis.Complex.LocallyUniformLimit

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

/-- **A circle on which `g` does not vanish.** If `g` is zero-free on some punctured
neighbourhood of `z₀ ∈ Ω` with `Ω` open — `z₀` itself may be a zero, or not — there is a radius
whose *closed* ball lies in `Ω` and on whose bounding circle `g` does not vanish. That circle is
what Rouché's theorem is applied to. -/
private lemma exists_radius_sphere_ne_zero {Ω : Set ℂ} (hΩ : IsOpen Ω) {g : ℂ → ℂ} {z₀ : ℂ}
    (hz₀Ω : z₀ ∈ Ω) (hpunct : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0) :
    ∃ r > 0, closedBall z₀ r ⊆ Ω ∧ ∀ z ∈ sphere z₀ r, g z ≠ 0 := by
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ Ω ∧ (z ≠ z₀ → g z ≠ 0) :=
    (hΩ.eventually_mem hz₀Ω).and (eventually_nhdsWithin_iff.mp hpunct)
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  exact ⟨r, hr, fun z hz => (hball hz).1, fun z hz =>
    (hball (sphere_subset_closedBall hz)).2 (Metric.ne_of_mem_sphere hz hr.ne')⟩

/-- **An analytic function on a preconnected set attains a value it does not attain identically
only in isolation.** If `g` is analytic on `Ω` and is not constantly `v` there, then `g z ≠ v` on
a punctured neighbourhood of any `x ∈ Ω`. -/
private theorem eventually_ne_of_not_forall_eq {Ω : Set ℂ} (hconn : IsPreconnected Ω)
    {g : ℂ → ℂ} (hgA : AnalyticOnNhd ℂ g Ω) {v : ℂ} (hnc : ¬ ∀ z ∈ Ω, g z = v)
    {x : ℂ} (hx : x ∈ Ω) : ∀ᶠ z in 𝓝[≠] x, g z ≠ v := by
  rcases (hgA x hx).eventually_eq_or_eventually_ne (analyticAt_const (v := v)) with h | h
  · exact absurd (fun z hz =>
      hgA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn hx h hz) hnc
  · exact h

/-- **Hurwitz's theorem.** On a connected open set, a locally uniform limit of holomorphic
functions that are nowhere zero is itself either nowhere zero or identically zero.

The dichotomy is genuine: the constant sequence `F n = 1 / (n + 1)` on any `Ω` converges locally
uniformly to `0`, so the second alternative cannot be dropped. -/
theorem hurwitz {ι : Type*} {l : Filter ι} [l.NeBot] {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hne : ∀ᶠ i in l, ∀ z ∈ Ω, F i z ≠ 0) :
    (∀ z ∈ Ω, g z ≠ 0) ∨ (∀ z ∈ Ω, g z = 0) := by
  have hg : DifferentiableOn ℂ g Ω :=
    _root_.TendstoLocallyUniformlyOn.differentiableOn hconv hF hΩ
  have hgA : AnalyticOnNhd ℂ g Ω := hg.analyticOnNhd hΩ
  by_cases hzero : Set.EqOn g 0 Ω
  · exact Or.inr fun z hz => hzero hz
  refine Or.inl fun z₀ hz₀Ω hgz₀ => ?_
  -- `g` does not vanish identically near `z₀`, else the identity theorem kills it on all of `Ω`
  -- `g` is zero-free on some punctured ball about `z₀`, else the identity theorem kills it on `Ω`
  have hpunct : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
    eventually_ne_of_not_forall_eq hconn hgA (fun hv => hzero fun z hz => by simpa using hv z hz)
      hz₀Ω
  have htop : analyticOrderAt g z₀ ≠ ⊤ := fun h => by
    obtain ⟨z, hz1, hz2⟩ :=
      (hpunct.and ((analyticOrderAt_eq_top.mp h).filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  obtain ⟨r, hr, hcb, hgne⟩ := exists_radius_sphere_ne_zero hΩ hz₀Ω hpunct
  have hsph : sphere z₀ r ⊆ closedBall z₀ r := sphere_subset_closedBall
  -- `‖g‖` attains a positive minimum on the circle
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_mem_sphere
    (hgA.continuousOn.mono (hsph.trans hcb)) hgne
  -- locally uniform convergence gives an `n` with `‖g - F n‖ < ‖g‖` on the circle
  have hconvS : TendstoUniformlyOn F g l (sphere z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z₀ r)).mp
      (hconv.mono (hsph.trans hcb))
  obtain ⟨n, hn, hFn, hnen⟩ :=
    ((Metric.tendstoUniformlyOn_iff.mp hconvS _ hδ).and (hF.and hne)).exists
  have hgA' : AnalyticOnNhd ℂ g (closedBall z₀ r) := hgA.mono hcb
  have hFA' : AnalyticOnNhd ℂ (F n) (closedBall z₀ r) := (hFn.analyticOnNhd hΩ).mono hcb
  have hs : ∀ z ∈ sphere z₀ r, ‖g z - F n z‖ < ‖g z‖ := fun z hz =>
    lt_of_lt_of_le (by simpa [dist_eq_norm] using hn z hz) (hδle z hz)
  -- Rouché: the counts agree, yet `F n` has no zeros and `g` has one at `z₀`
  have hcount := rouche hr hgA' hFA' hs
  rw [finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero
    (hFA'.mono ball_subset_closedBall) (fun z hz => hnen z (hcb (ball_subset_closedBall hz)))]
    at hcount
  have hle := analyticOrderNatAt_le_finsum_ball hgA' (mem_ball_self hr)
  rw [hcount] at hle
  have h0 : analyticOrderAt g z₀ = 0 :=
    (ENat.toNat_eq_zero.mp (by simpa [analyticOrderNatAt] using Nat.le_zero.mp hle)).resolve_right
      htop
  exact (hgA z₀ hz₀Ω).analyticOrderAt_eq_zero.mp h0 hgz₀

/-- If `g - v` has an isolated zero at `a` inside a disc, then for all large `n` the approximant
`F n` also attains the value `v` in that disc. This is the Rouché step behind `hurwitz_injOn`. -/
private lemma eventually_exists_eq {ι : Type*} {l : Filter ι} {Ω : Set ℂ} {F : ι → ℂ → ℂ}
    {g : ℂ → ℂ} (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω) (hΩ : IsOpen Ω)
    (hg : AnalyticOnNhd ℂ g Ω) (hconv : TendstoLocallyUniformlyOn F g l Ω)
    {a v : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hball : closedBall a ρ ⊆ Ω)
    (hga : g a = v) (hzf : ∀ z ∈ closedBall a ρ, z ≠ a → g z ≠ v) :
    ∀ᶠ i in l, ∃ z ∈ ball a ρ, F i z = v := by
  have hA : AnalyticOnNhd ℂ (fun ζ => g ζ - v) (closedBall a ρ) :=
    (hg.mono hball).sub analyticOnNhd_const
  have hsphne : ∀ z ∈ sphere a ρ, g z - v ≠ 0 := fun z hz =>
    sub_ne_zero.mpr (hzf z (sphere_subset_closedBall hz) (Metric.ne_of_mem_sphere hz hρ.ne'))
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_of_mem_sphere
    (hA.continuousOn.mono sphere_subset_closedBall) hsphne
  have hconvS : TendstoUniformlyOn F g l (sphere a ρ) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere a ρ)).mp
      (hconv.mono ((sphere_subset_closedBall).trans hball))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconvS _ hδ, hF] with n hn hFn
  have hB : AnalyticOnNhd ℂ (fun ζ => F n ζ - v) (closedBall a ρ) :=
    ((hFn.analyticOnNhd hΩ).mono hball).sub analyticOnNhd_const
  have hs : ∀ z ∈ sphere a ρ, ‖(g z - v) - (F n z - v)‖ < ‖g z - v‖ := by
    intro z hz
    have he : (g z - v) - (F n z - v) = g z - F n z := by ring
    rw [he]
    exact lt_of_lt_of_le (by simpa [dist_eq_norm] using hn z hz) (hδle z hz)
  have hcount := rouche hρ hA hB hs
  have htop : analyticOrderAt (fun ζ => g ζ - v) a ≠ ⊤ :=
    analyticOrderAt_ne_top_of_forall_ne_zero hρ fun z hz hne =>
      sub_ne_zero.mpr (hzf z (ball_subset_closedBall hz) hne)
  have hord : analyticOrderNatAt (fun ζ => g ζ - v) a ≠ 0 := by
    have h0 : analyticOrderAt (fun ζ => g ζ - v) a ≠ 0 := fun h =>
      ((hA a (mem_closedBall_self hρ.le)).analyticOrderAt_eq_zero.mp h) (by simp [hga])
    simpa [analyticOrderNatAt] using fun h => h0 ((ENat.toNat_eq_zero.mp h).resolve_right htop)
  have hne0 : (∑ᶠ z ∈ ball a ρ, analyticOrderNatAt (fun ζ => F n ζ - v) z) ≠ 0 := by
    rw [← hcount]
    exact fun h => hord (Nat.le_zero.mp (h ▸ analyticOrderNatAt_le_finsum_ball hA
      (mem_ball_self hρ)))
  by_contra hcon
  push Not at hcon
  exact hne0 (finsum_analyticOrderNatAt_ball_eq_zero_of_forall_ne_zero
    (hB.mono ball_subset_closedBall) (fun z hz => sub_ne_zero.mpr (hcon z hz)))

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
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {F : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F g l Ω)
    (hinj : ∀ᶠ i in l, Set.InjOn (F i) Ω) :
    Set.InjOn g Ω ∨ ∃ v, ∀ z ∈ Ω, g z = v := by
  have hg : DifferentiableOn ℂ g Ω :=
    _root_.TendstoLocallyUniformlyOn.differentiableOn hconv hF hΩ
  have hgA : AnalyticOnNhd ℂ g Ω := hg.analyticOnNhd hΩ
  by_cases hconst : ∃ v, ∀ z ∈ Ω, g z = v
  · exact Or.inr hconst
  refine Or.inl fun a ha b hb hab => ?_
  by_contra hne
  -- around any point where `g` takes the value `g a`, that value is taken only there
  have hiso : ∀ x ∈ Ω, g x = g a → ∀ σ > 0, ∃ ρ > 0, ρ ≤ σ ∧ closedBall x ρ ⊆ Ω ∧
      ∀ z ∈ closedBall x ρ, z ≠ x → g z ≠ g a := by
    intro x hx _ σ hσ
    have hpunct : ∀ᶠ z in 𝓝[≠] x, g z ≠ g a :=
      eventually_ne_of_not_forall_eq hconn hgA (fun hv => hconst ⟨g a, hv⟩) hx
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
  obtain ⟨n, ⟨⟨z₁, hz₁, hFz₁⟩, ⟨z₂, hz₂, hFz₂⟩⟩, hinjn⟩ :=
    (((eventually_exists_eq hF hΩ hgA hconv hρa hballa rfl hzfa).and
      (eventually_exists_eq hF hΩ hgA hconv hρb hballb hab.symm hzfb)).and hinj).exists
  have hz₁₂ : z₁ ≠ z₂ := by
    rintro rfl
    have h1 : dist a z₁ < ρa := by rw [dist_comm]; exact mem_ball.mp hz₁
    have h2 : dist z₁ b < ρb := mem_ball.mp hz₂
    have h3 := dist_triangle a z₁ b
    linarith
  exact hz₁₂ (hinjn (hballa (ball_subset_closedBall hz₁)) (hballb (ball_subset_closedBall hz₂))
    (hFz₁.trans hFz₂.symm))

end TauCeti
