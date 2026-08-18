/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic branches of `log` and of `n`-th roots on a simply connected domain

Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` produces a **continuous** branch of `log ∘ g`
on a simply connected open set. The Riemann-mapping argument needs a **holomorphic** one. This file
supplies that upgrade for the logarithm, consuming Mathlib's branch rather than rebuilding it, and
then obtains the `n`-th root from it directly as `exp (L / n)`.

Note that the root branch is *not* an upgrade of Mathlib's `Complex.exists_continuousOn_pow_eq`,
which this file does not use: once the logarithm branch is holomorphic, `exp (L / n)` is holomorphic
by composition and satisfies `(exp (L / n)) ^ n = exp L = g` outright, so routing through a separate
continuous root branch would add a second continuity-to-holomorphy argument for no gain.

The upgrade is local and purely formal. Near a point `z₀`, the continuous branch `L` agrees with
`logBranch w₀ ∘ g` where `w₀ = L z₀`, the branch of the logarithm based at `w₀`: that composite is
holomorphic (the argument sits near `1`, inside the slit plane, where `Complex.log` is), and it
agrees with `L` because continuity of `L` confines `L z - w₀` to the strip `|im| < π` on which that
branch inverts `Complex.exp`. So no new analysis is involved — only the observation that a
continuous logarithm of a holomorphic nonvanishing function is automatically holomorphic.

## Attribution and upstream coordination

The mathematics here is an upgrade of prior Mathlib work, not a first proof. The logarithm and
zero-free root branches rest on two efforts of Yury Kudryashov's; the germ statement rests in
addition on Mathlib's order-of-vanishing formalization.

*The branch itself* is Mathlib's: `Complex.exists_continuousOn_eqOn_exp_comp` in
`Mathlib.Analysis.Complex.BranchLogRoot` (© Yury Kudryashov) supplies the continuous logarithm
branch on a simply connected domain, which this file consumes rather than rebuilds. What
`TauCeti.exists_differentiableOn_eqOn_exp_comp` and `TauCeti.exists_differentiableOn_pow_eq` add to
it is the continuity-to-holomorphy upgrade. The `n`-th root is *not* obtained from Mathlib's
continuous root API (`Complex.exists_continuousOn_pow_eq` is never used here): it is derived as
`exp (L / n)` from the upgraded holomorphic logarithm branch `L`.

*The order of vanishing* is Mathlib's too: `Mathlib.Analysis.Analytic.Order` (© Vincent Beffara;
authors Vincent Beffara and Stefan Kebekus) formalizes `analyticOrderAt` and the factorization
theory around it, on which `TauCeti.exists_eventuallyEq_pow_iff_dvd` rests throughout.
`AnalyticAt.analyticOrderAt_eq_natCast` supplies the factorization of a germ of finite order,
`analyticOrderAt_eq_top` identifies the germ of order `⊤` as the one vanishing near `z₀`, and
`analyticOrderAt_pow` gives the converse direction outright. What is added here is only the
assembly of those with the root branch above.

*The consumer* is the Riemann mapping construction in `Mathlib.Analysis.Complex.RiemannMapping`
(© Yury Kudryashov), whose `Complex.exists_mapsTo_unitBall_injOn_deriv_ne_zero` performs the same
square-root step that the sibling file `DiscInjection.lean` re-derives on top of this API; see its
docstring for why that lemma cannot be named by an importer.

The Riemann mapping theorem is being formalized upstream at
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), which proves
holomorphic log / `n`-th-root statements (`exists_branch_log`, `exists_branch_nthRoot`)
**internally, as private lemmas**, alongside the argument principle, Hurwitz and Montel. The
`ConformalMapping` roadmap's stated contribution at these layers is therefore *named, reusable API*
rather than first proof. Accordingly the two branch declarations here are a **temporary shim**: when
the human-curated Mathlib versions land, those should be deleted and every downstream consumer
refactored onto them. That does not extend to `TauCeti.exists_eventuallyEq_pow_iff_dvd`: the
upstream statements are zero-free, like the ones they replace, so they do not subsume a germ that
vanishes.

## Roots of a germ that vanishes

The root branch needs `g` to be zero-free, so on its own it says nothing about a germ that
vanishes. Locally that gap closes by factoring the zero out: `A z = (z - z₀) ^ m • g z` with
`g z₀ ≠ 0`, so an `n`-th root of the germ exists exactly when `n` divides its order of vanishing
(`TauCeti.exists_eventuallyEq_pow_iff_dvd`), namely `(z - z₀) ^ (m / n)` times the branch above
applied to `g`. This weakens the zero-free hypothesis — the case of order `0` — to the
divisibility condition, and the converse direction shows the condition is sharp. The germ that
vanishes identically near `z₀`, of order `⊤`, is its own `n`-th root.

## Main statements

* `TauCeti.exists_differentiableOn_eqOn_exp_comp` — a holomorphic branch of `log ∘ g`.
* `TauCeti.exists_differentiableOn_pow_eq` — a holomorphic branch of `ⁿ√g`.
* `TauCeti.exists_eventuallyEq_pow_iff_dvd` — a holomorphic germ has a holomorphic `n`-th root iff
  `n` divides its order of vanishing.
-/

public section

namespace TauCeti

open Complex Set

/-- The branch of the logarithm **based at `a`**: the translate of Mathlib's principal branch that
takes the value `a` at the point `Complex.exp a`, its branch cut rotated away from there. -/
private noncomputable def logBranch (a v : ℂ) : ℂ := a + Complex.log (v / Complex.exp a)

/-- The branch based at `a` is complex differentiable wherever the translated point misses the
branch cut. -/
private theorem differentiableAt_logBranch {a v : ℂ} (h : v / Complex.exp a ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (logBranch a) v :=
  ((differentiableAt_id.div_const _).clog h).const_add _

/-- **The branch based at `a` inverts `Complex.exp`** on the strip of height `2 π` centred at `a`,
because `Complex.log_exp` inverts it on `-π < im ≤ π`. -/
private theorem logBranch_exp {a w : ℂ} (h₁ : -Real.pi < (w - a).im) (h₂ : (w - a).im ≤ Real.pi) :
    logBranch a (Complex.exp w) = w := by
  rw [logBranch, ← Complex.exp_sub, Complex.log_exp h₁ h₂]
  ring

/-- **The local upgrade.** A continuous branch `L` of `log ∘ g` on an open set is complex
differentiable wherever `g` is, because near any point it coincides with an honest local branch of
`log` composed with `g`. -/
private theorem differentiableAt_of_continuousOn_exp_comp {U : Set ℂ} (hU : IsOpen U)
    {L g : ℂ → ℂ} (hL : ContinuousOn L U) (hEq : EqOn (Complex.exp ∘ L) g U)
    (hg : DifferentiableOn ℂ g U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    DifferentiableAt ℂ L z₀ := by
  set w₀ : ℂ := L z₀ with hw₀
  have hgz₀ : g z₀ = Complex.exp w₀ := (hEq hz₀).symm
  -- `L` is continuous at `z₀` in the ambient sense, `U` being open.
  have hLat : ContinuousAt L z₀ := (hL.continuousAt (hU.mem_nhds hz₀))
  -- Continuity confines `L z - w₀` to the strip where the branch based at `w₀` inverts `exp`.
  have hstrip : ∀ᶠ z in nhds z₀, |(L z - w₀).im| < Real.pi := by
    have hcont : ContinuousAt (fun z => |(L z - w₀).im|) z₀ := by
      exact (continuous_abs.comp Complex.continuous_im).continuousAt.comp
        (hLat.sub continuousAt_const)
    have hz : |(L z₀ - w₀).im| < Real.pi := by
      simp [hw₀, Real.pi_pos]
    exact hcont (Iio_mem_nhds hz)
  -- On that neighbourhood (intersected with `U`), `L` and `logBranch w₀ ∘ g` agree.
  have hloc : L =ᶠ[nhds z₀] logBranch w₀ ∘ g := by
    filter_upwards [hstrip, hU.mem_nhds hz₀] with z hz hzU
    have hgz : g z = Complex.exp (L z) := (hEq hzU).symm
    simp only [Function.comp_apply, hgz]
    exact (logBranch_exp (by linarith [abs_lt.mp hz |>.1]) (le_of_lt (abs_lt.mp hz).2)).symm
  -- `logBranch w₀ ∘ g` is differentiable at `z₀`: the translated argument is `1` there.
  have hdiffBranch : DifferentiableAt ℂ (logBranch w₀ ∘ g) z₀ := by
    have hgd : DifferentiableAt ℂ g z₀ := (hg z₀ hz₀).differentiableAt (hU.mem_nhds hz₀)
    have hslit : g z₀ / Complex.exp w₀ ∈ Complex.slitPlane := by
      rw [hgz₀, div_self (Complex.exp_ne_zero _)]
      exact Complex.one_mem_slitPlane
    exact (differentiableAt_logBranch hslit).comp z₀ hgd
  exact hdiffBranch.congr_of_eventuallyEq hloc

/-- **A holomorphic branch of `log ∘ g` on a simply connected domain.** If `g` is holomorphic and
nowhere zero on a simply connected open `U ⊆ ℂ`, there is a holomorphic `f` on `U` with
`exp ∘ f = g`. Mathlib's `Complex.exists_continuousOn_eqOn_exp_comp` supplies the branch; only its
holomorphy is added here. -/
theorem exists_differentiableOn_eqOn_exp_comp {U : Set ℂ} (hUc : IsSimplyConnected U)
    (hUo : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (Complex.exp ∘ f) g U := by
  obtain ⟨L, hLc, hLeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUc hUo hg.continuousOn hU₀
  refine ⟨L, fun z hz => ?_, hLeq⟩
  exact ((differentiableAt_of_continuousOn_exp_comp hUo hLc hLeq hg hz).differentiableWithinAt)

/-- **A holomorphic `n`-th root on a simply connected domain.** The Koebe square-root step of the
Riemann mapping theorem is the case `n = 2`. -/
theorem exists_differentiableOn_pow_eq {U : Set ℂ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧ EqOn (fun z => f z ^ n) g U := by
  obtain ⟨L, hLd, hLeq⟩ := exists_differentiableOn_eqOn_exp_comp hUc hUo hg hU₀
  refine ⟨fun z => Complex.exp (L z / n), fun z hz => ((hLd z hz).div_const _).cexp,
    fun z hz => ?_⟩
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmul : (n : ℂ) * (L z / n) = L z := by field_simp
  have hpow : Complex.exp (L z / n) ^ n = Complex.exp (L z) := by
    rw [← Complex.exp_nat_mul, hmul]
  simpa only [hpow, Function.comp_apply] using hLeq hz

/-- The germ form of `TauCeti.exists_differentiableOn_pow_eq`: a holomorphic germ that does not
vanish at `z₀` has a holomorphic `n`-th root near `z₀`. -/
private lemma exists_eventuallyEq_pow_of_ne_zero {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}
    (hA : AnalyticAt ℂ A z₀) (h0 : A z₀ ≠ 0) (hn : n ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ ∀ᶠ z in nhds z₀, h z ^ n = A z := by
  -- A small enough disc about `z₀` is holomorphic and zero-free, and simply connected because
  -- it is contractible, so the branch above applies on it.
  have hloc : ∀ᶠ z in nhds z₀, AnalyticAt ℂ A z ∧ A z ≠ 0 :=
    hA.eventually_analyticAt.and (hA.continuousAt.eventually_ne h0)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hloc
  have hsc : IsSimplyConnected (Metric.ball z₀ r) := by
    have : ContractibleSpace (Metric.ball z₀ r) := Metric.contractibleSpace_ball hr
    exact SimplyConnectedSpace.ofContractible _
  have hAd : DifferentiableOn ℂ A (Metric.ball z₀ r) := fun z hz =>
    ((hball (Metric.mem_ball.mp hz)).1.differentiableAt).differentiableWithinAt
  have hA0 : (0 : ℂ) ∉ A '' Metric.ball z₀ r := by
    rintro ⟨z, hz, hz0⟩
    exact (hball (Metric.mem_ball.mp hz)).2 hz0
  obtain ⟨h, hhd, hheq⟩ := exists_differentiableOn_pow_eq hsc Metric.isOpen_ball hAd hA0 hn
  have hnhds : Metric.ball z₀ r ∈ nhds z₀ := Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  exact ⟨h, DifferentiableOn.analyticAt hhd hnhds,
    by filter_upwards [hnhds] with z hz using hheq hz⟩

/-- **When a holomorphic germ has a holomorphic `n`-th root**: exactly when `n` divides its order
of vanishing. This weakens the zero-free hypothesis of `TauCeti.exists_differentiableOn_pow_eq`,
which is the case of order `0`, to the divisibility condition, and records that the condition is
sharp. A germ of order `⊤`, one vanishing identically near `z₀`, is included: `n ≠ 0` divides
`⊤`. -/
theorem exists_eventuallyEq_pow_iff_dvd {A : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hA : AnalyticAt ℂ A z₀)
    (hn : n ≠ 0) :
    (∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ ∀ᶠ z in nhds z₀, A z = ψ z ^ n) ↔
      (n : ℕ∞) ∣ analyticOrderAt A z₀ := by
  constructor
  · rintro ⟨ψ, hψ, hψeq⟩
    have hpi : A =ᶠ[nhds z₀] ψ ^ n := by
      filter_upwards [hψeq] with z hz
      simpa using hz
    exact ⟨analyticOrderAt ψ z₀, by
      rw [analyticOrderAt_congr hpi, analyticOrderAt_pow hψ, nsmul_eq_mul]⟩
  · intro hdvd
    rcases eq_or_ne (analyticOrderAt A z₀) ⊤ with htop | htop
    · -- Order `⊤`: the germ vanishes near `z₀`, and the zero germ is its own `n`-th root.
      refine ⟨0, analyticAt_const, ?_⟩
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simp [hz, zero_pow hn]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
      obtain ⟨k, hk⟩ : n ∣ m := by
        obtain ⟨c, hc⟩ := hdvd
        rcases eq_or_ne c ⊤ with rfl | hc'
        · rw [← hm, ENat.mul_top (by exact_mod_cast hn)] at hc
          exact absurd hc.symm (by simp)
        · obtain ⟨j, rfl⟩ := ENat.ne_top_iff_exists.mp hc'
          exact ⟨j, by exact_mod_cast hm.trans hc⟩
      -- Factor out the zero: `A z = (z - z₀) ^ (n * k) • g z` near `z₀`, with `g z₀ ≠ 0`.
      obtain ⟨g, hg, hg0, hgeq⟩ :=
        hA.analyticOrderAt_eq_natCast.mp (by rw [← hm, hk])
      obtain ⟨h, hh, hheq⟩ := exists_eventuallyEq_pow_of_ne_zero hg hg0 hn
      refine ⟨fun z => (z - z₀) ^ k * h z, ((analyticAt_id.sub analyticAt_const).pow k).mul hh, ?_⟩
      filter_upwards [hgeq, hheq] with z hz hz'
      rw [hz, smul_eq_mul, ← hz', mul_pow, ← pow_mul, mul_comm k n]

end TauCeti
