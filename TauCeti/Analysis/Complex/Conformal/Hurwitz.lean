/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import TauCeti.Analysis.Complex.Conformal.Rouche
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Hurwitz's theorem

Hurwitz's theorem says that a locally uniform limit of zero-free holomorphic functions on a
connected open subset of `ℂ` is either zero-free or identically zero. This is the zero-control
input used when normal-family arguments pass injectivity to a limit.

The proof uses `TauCeti.rouche`. If the limit has an isolated zero, choose a small circle around it
on which the limit is nonzero. Local uniform convergence makes a sufficiently late approximant
closer to the limit than the limit's modulus on that circle. Rouché then gives the approximant a
zero inside, contradicting its zero-free hypothesis. The identity principle handles the
alternative in which the zero is not isolated.

This advances layer L0 (Hurwitz) of the conformal-mapping roadmap. As required by that roadmap's
coordination clause, this is a temporary named API shim for the private Hurwitz argument in the
human-curated Mathlib Riemann-mapping work
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505). It should be replaced
by Mathlib's public theorem, and its consumers refactored, when that theorem lands.

## Main result

* `TauCeti.eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn`: Hurwitz's theorem on a
  connected open set.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5.
* J. B. Conway, *Functions of One Complex Variable I*, Ch. VII.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {U : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}

/-- Around an isolated zero of an analytic function on an open set, there is a closed disc in the
set whose bounding circle contains no zeros. -/
private theorem exists_closedBall_subset_and_forall_sphere_ne_zero (hU : IsOpen U)
    {z : ℂ} (hz : z ∈ U)
    (hiso : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0) :
    ∃ r > 0, closedBall z r ⊆ U ∧ ∀ w ∈ sphere z r, f w ≠ 0 := by
  have hmem : U ∈ 𝓝 z := hU.mem_nhds hz
  obtain ⟨V, hV, hVsub⟩ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1
      (show {w | f w ≠ 0} ∈ 𝓝[≠] z from hiso)
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (inter_mem hmem hV)
  refine ⟨r, hr, fun w hw => (hrsub hw).1, fun w hw => ?_⟩
  exact hVsub ⟨(hrsub (sphere_subset_closedBall hw)).2, by
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_mem_sphere hw hr.ne'⟩

/-- A continuous zero-free function on a nonempty compact set has a positive lower bound for its
norm. -/
private theorem exists_pos_le_norm_of_isCompact {K : Set ℂ} (hK : IsCompact K)
    (hKne : K.Nonempty) (hf : ContinuousOn f K) (hne : ∀ z ∈ K, f z ≠ 0) :
    ∃ ε > 0, ∀ z ∈ K, ε ≤ ‖f z‖ := by
  obtain ⟨z, hz, hzmin⟩ :=
    hK.exists_isMinOn hKne (continuous_norm.comp_continuousOn hf)
  exact ⟨‖f z‖, norm_pos_iff.2 (hne z hz), fun w hw => hzmin hw⟩

/-- A zero-free analytic function has zero Rouché count on every ball in its domain. -/
private theorem finsum_analyticOrderNatAt_eq_zero_of_forall_ne_zero
    (hf : AnalyticOnNhd ℂ f U) {z : ℂ} {r : ℝ} (hsub : ball z r ⊆ U)
    (hne : ∀ w ∈ ball z r, f w ≠ 0) :
    ∑ᶠ w ∈ ball z r, analyticOrderNatAt f w = 0 := by
  classical
  apply finsum_eq_zero_of_forall_eq_zero
  intro w
  by_cases hw : w ∈ ball z r
  · have hfw := (hf w (hsub hw)).analyticOrderAt_eq_zero.2 (hne w hw)
    simp [analyticOrderNatAt, hfw]
  · simp [hw]

/-- If an analytic function has finite order and vanishes at the centre of a ball, its Rouché
count on that ball is positive. -/
private theorem finsum_analyticOrderNatAt_pos_of_apply_eq_zero
    (hf : AnalyticOnNhd ℂ f U) {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ U)
    (hfinite : analyticOrderAt f z ≠ ⊤) (hfz : f z = 0)
    (hsupport : (ball z r ∩ Function.support (analyticOrderNatAt f)).Finite) :
    0 < ∑ᶠ w ∈ ball z r, analyticOrderNatAt f w := by
  classical
  apply finsum_pos
  · intro w
    positivity
  · refine ⟨z, ?_⟩
    have horder : 0 < analyticOrderNatAt f z :=
      ENat.toNat_pos ((hf z hz).analyticOrderAt_ne_zero.2 hfz) hfinite
    simpa [mem_ball_self hr] using horder
  · unfold Function.HasFiniteSupport
    rw [show Function.support (fun i => ∑ᶠ (_ : i ∈ ball z r), analyticOrderNatAt f i) =
        ball z r ∩ Function.support (analyticOrderNatAt f) by
      ext i
      simp [Function.support, finsum_eq_dif, dist_comm]]
    exact hsupport

/-- **Hurwitz's theorem.** A locally uniform limit of zero-free holomorphic functions on a
connected open set is either identically zero there or is itself zero-free there. -/
theorem eqOn_zero_or_forall_ne_zero_of_tendstoLocallyUniformlyOn
    (hU : IsOpen U) (hconn : IsConnected U)
    (hF : ∀ n, DifferentiableOn ℂ (F n) U)
    (hf : DifferentiableOn ℂ f U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hne : ∀ n, ∀ z ∈ U, F n z ≠ 0) :
    Set.EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  rw [or_iff_not_imp_left]
  intro hnotzero
  simp only [Set.EqOn, not_forall] at hnotzero
  obtain ⟨a, haU, hfa⟩ := hnotzero
  intro z hzU hfz
  have haf : f a ≠ 0 := by simpa using hfa
  have hiso : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
    refine (hf.analyticOnNhd hU z hzU).eventually_eq_zero_or_eventually_ne_zero.resolve_left ?_
    intro heq
    have hglobal := (hf.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hconn.isPreconnected hzU heq
    exact haf (hglobal haU)
  obtain ⟨r, hr, hclosed, hsphere⟩ :=
    exists_closedBall_subset_and_forall_sphere_ne_zero hU hzU hiso
  have hcont : ContinuousOn f (sphere z r) :=
    (hf.continuousOn.mono fun w hw => hclosed (sphere_subset_closedBall hw))
  obtain ⟨ε, hε, hεle⟩ :=
    exists_pos_le_norm_of_isCompact (isCompact_sphere z r)
      (NormedSpace.sphere_nonempty.2 hr.le) hcont hsphere
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hconv
    (sphere z r) (fun w hw => hclosed (sphere_subset_closedBall hw)) (isCompact_sphere z r)
  have hevent : ∀ᶠ n in atTop, ∀ w ∈ sphere z r, ‖f w - F n w‖ < ε := by
    simpa [dist_eq_norm] using (Metric.tendstoUniformlyOn_iff.1 hunif ε hε)
  obtain ⟨n, hn⟩ := hevent.exists
  have hrouche := rouche hr
    ((hf.analyticOnNhd hU).mono hclosed)
    ((hF n).analyticOnNhd hU |>.mono hclosed)
    (fun w hw => (hn w hw).trans_le (hεle w hw))
  have hleft : ∑ᶠ w ∈ ball z r, analyticOrderNatAt (F n) w = 0 :=
    finsum_analyticOrderNatAt_eq_zero_of_forall_ne_zero
      ((hF n).analyticOnNhd hU) (ball_subset_closedBall.trans hclosed)
      (fun w hw => hne n w (hclosed (ball_subset_closedBall hw)))
  have hfinite : analyticOrderAt f z ≠ ⊤ := by
    have haorder : analyticOrderAt f a ≠ ⊤ := by
      rw [(hf.analyticOnNhd hU a haU).analyticOrderAt_eq_zero.2 haf]
      exact ENat.zero_ne_top
    exact (hf.analyticOnNhd hU).analyticOrderAt_ne_top_of_isPreconnected
      hconn.isPreconnected haU hzU haorder
  have hsupp : (ball z r ∩ Function.support (analyticOrderNatAt f)).Finite := by
    classical
    have hfb : AnalyticOnNhd ℂ f (ball z r) :=
      (hf.analyticOnNhd hU).mono (ball_subset_closedBall.trans hclosed)
    refine (MeromorphicOn.divisor_ball_support_finite
      (((hf.analyticOnNhd hU).mono hclosed).meromorphicOn)).subset ?_
    intro w hw
    rcases hw with ⟨hwb, hw⟩
    simp only [Function.mem_support, ne_eq] at hw ⊢
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfb hwb]
    simp only [analyticOrderNatAt] at hw
    cases ho : analyticOrderAt f w with
    | top => simp [ho] at hw
    | coe n =>
        rw [ho] at hw
        have hwn : n ≠ 0 := by simpa only [ENat.toNat_coe] using hw
        simpa only [ENat.map_coe, WithTop.coe_natCast, WithTop.untop₀_natCast,
          Int.natCast_eq_zero] using hwn
  have hright := finsum_analyticOrderNatAt_pos_of_apply_eq_zero
    (hf.analyticOnNhd hU) hr hzU hfinite hfz hsupp
  rw [hleft] at hrouche
  exact (ne_of_gt hright) hrouche

end TauCeti
