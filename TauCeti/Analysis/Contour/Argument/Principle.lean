/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Contour.Cauchy.Goursat

/-!
# The argument principle

For `f : ℂ → ℂ` meromorphic on a closed disc `C(c, R)` whose nonzero-order points are contained in a
finite set `S` inside the open disc, on which `ord z = meromorphicOrderAt f z`, the contour integral
of the logarithmic derivative counts the zeros and poles with multiplicity:
`∮_{C(c,R)} f'/f = 2πi · ∑_{z ∈ S} ord z`.

The order `ord z = meromorphicOrderAt f z` is positive at a zero and negative at a pole, so the
integral is `2πi` times the number of zeros minus poles inside the circle. The one-point special
case — the centre `c` is the only point that may have nonzero order — is `argumentPrinciple_local`.

This is the argument-principle contour identity the valence formula evaluates over the interior
orbits: the residue of `f'/f` at a point is its meromorphic order there. Mathlib has `logDeriv` and
`meromorphicOrderAt` but not this identity.

Only the finite set `S` is required to lie in the *open* disc; away from `S` every point of the
closed disc has order `0`, hence is at worst a removable singularity of `f`. No pointwise regularity
of the raw function `f` is hypothesised — `f` may take isolated "wrong values" where `logDeriv f` is
meaningless — since the results are stated up to the meromorphic normal form of `f`.

## Main results

* `TauCeti.Contour.argumentPrinciple` — `∮_{C(c,R)} logDeriv f = 2πi · ∑_{z ∈ S} ord z` when all
  nonzero-order points are contained in a finite set `S` inside the open disc, with `ord` agreeing
  with `meromorphicOrderAt f` on `S`.
* `TauCeti.Contour.argumentPrinciple_local` — the special case `S = {c}`:
  `∮_{C(c,R)} logDeriv f = 2πi · n` when the centre `c`, of order `n`, is the only point of the
  closed disc that may have nonzero meromorphic order.

These are Layer 2 targets of the contour-integration roadmap, feeding the argument principle and,
ultimately, the valence formula.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the argument-principle specialisation of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`.../Residue/GeneralizedTheoremBase.lean`, where the residue theorem is applied to `logDeriv f`),
specialised to a circle and to the raw-function design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Metric Complex
open scoped Real

namespace TauCeti.Contour

/-- At a point where a function is analytic and non-vanishing, its logarithmic derivative
`logDeriv f = deriv f / f` is analytic. Exposed for the residue-form of the argument principle
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). -/
lemma analyticAt_logDeriv_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : AnalyticAt ℂ (logDeriv f) z := by
  rw [logDeriv]
  exact hf.deriv.div hf hz

/-- The logarithmic derivative depends only on the germ. -/
private lemma logDeriv_eq_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    logDeriv f z = logDeriv g z := by
  rw [logDeriv_apply, logDeriv_apply, h.deriv_eq, h.eq_of_nhds]

/-- Logarithmic derivative of a local factorisation `(· - c) ^ n · g`, away from the base point `c`.
Since `logDeriv` turns products into sums and `logDeriv ((· - c) ^ n) = n · (· - c)⁻¹`, we get
`logDeriv ((· - c) ^ n · g) = n · (· - c)⁻¹ + logDeriv g`. -/
private lemma logDeriv_zpow_sub_mul {g : ℂ → ℂ} {c z : ℂ} {n : ℤ} (hz : z ≠ c) (hg_ne : g z ≠ 0)
    (hg_diff : DifferentiableAt ℂ g z) :
    logDeriv (fun w => (w - c) ^ n * g w) z = (n : ℂ) * (z - c)⁻¹ + logDeriv g z := by
  have hz_sub : z - c ≠ 0 := sub_ne_zero.2 hz
  have hzpow : (z - c) ^ n ≠ 0 := zpow_ne_zero n hz_sub
  have hdz : DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
    (differentiableAt_id.sub_const c).zpow (Or.inl hz_sub)
  have hld_sub : logDeriv (fun w => w - c) z = (z - c)⁻¹ := by
    have hderiv : deriv (fun w => w - c) z = 1 := by simp
    rw [logDeriv_apply, hderiv, one_div]
  rw [logDeriv_mul z hzpow hg_ne hdz hg_diff,
    logDeriv_fun_zpow (f := fun w => w - c) (differentiableAt_id.sub_const c) n, hld_sub]

/-- **Simple-pole splitting of the logarithmic derivative.** Near a point `s` where `F` is
meromorphic of order `n`, the logarithmic derivative equals its simple-pole principal part
`n · (· - s)⁻¹` plus an analytic term: there is `g` analytic and non-vanishing at `s` (the local
factor of `F = (· - s) ^ n • g`) with `logDeriv F = n · (· - s)⁻¹ + logDeriv g` on a punctured
neighbourhood of `s`. Exposed for the residue-form of the argument principle
(`TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt`). -/
theorem logDeriv_eventuallyEq_principalPart {F : ℂ → ℂ} {s : ℂ} {n : ℤ}
    (hF : MeromorphicAt F s) (hn : meromorphicOrderAt F s = (n : WithTop ℤ)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      logDeriv F =ᶠ[𝓝[≠] s] fun z => (n : ℂ) * (z - s)⁻¹ + logDeriv g z := by
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  refine ⟨g, hg_an, hg_ne, ?_⟩
  -- Lift the punctured factorisation to germ-agreement at each nearby point.
  have hFH : ∀ᶠ z in 𝓝[≠] s, F =ᶠ[𝓝 z] fun w => (w - s) ^ n • g w := by
    obtain ⟨U, hU_open, hcU, hU_sub⟩ := mem_nhdsWithin.1 hg_eq
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU_open.mem_nhds hcU), self_mem_nhdsWithin]
      with z hzU hz_ne
    filter_upwards [(hU_open.inter isOpen_compl_singleton).mem_nhds ⟨hzU, hz_ne⟩] with w hw
      using hU_sub hw
  filter_upwards [hFH, hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz_FH hz_gan hz_gne hz_ne
  have hmul : (fun w => (w - s) ^ n • g w) = fun w => (w - s) ^ n * g w := by
    funext w; rw [smul_eq_mul]
  rw [logDeriv_eq_of_eventuallyEq hz_FH, hmul]
  exact logDeriv_zpow_sub_mul hz_ne hz_gne hz_gan.differentiableAt

/-- Passing to the meromorphic normal form leaves the log-derivative's circle integral unchanged:
the two functions agree off a discrete set, which the circle integral does not see. -/
private theorem circleIntegral_logDeriv_toMeromorphicNFOn {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.closedBall c R)) :
    circleIntegral (logDeriv f) c R
      = circleIntegral (logDeriv (toMeromorphicNFOn f (Metric.closedBall c R))) c R := by
  set F := toMeromorphicNFOn f (Metric.closedBall c R) with hF_def
  refine circleIntegral.circleIntegral_congr_codiscreteWithin ?_ hR.ne'
  have hspU : Metric.sphere c |R| ⊆ Metric.closedBall c R := by
    rw [abs_of_pos hR]; exact Metric.sphere_subset_closedBall
  filter_upwards [(toMeromorphicNFOn_eqOn_codiscrete hf).filter_mono
      (Filter.codiscreteWithin_mono hspU), self_mem_codiscreteWithin (Metric.sphere c |R|)]
    with z hz_eq hz_mem
  have hne : f =ᶠ[𝓝[≠] z] F := (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (hspU hz_mem)).symm
  exact logDeriv_eq_of_eventuallyEq (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne hz_eq)

/-- The circle integral of the principal part `∑_{s∈S} ord s · (z − s)⁻¹`, with all poles `s`
strictly inside the disc, is `2πi · ∑_{s∈S} ord s` (each simple pole contributes `2πi · ord s`). -/
private theorem circleIntegral_principalPart {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ)
    (ord : ℂ → ℤ) (hS : (S : Set ℂ) ⊆ Metric.ball c R) :
    circleIntegral (fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹) c R
      = 2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
  have hzs_ne : ∀ z ∈ Metric.sphere c R, ∀ s ∈ S, z ≠ s := by
    intro z hz s hsS h; subst h
    rw [Metric.mem_sphere] at hz
    exact absurd hz (ne_of_lt (Metric.mem_ball.1 (hS (Finset.mem_coe.2 hsS))))
  have hP_intble : ∀ s ∈ S, CircleIntegrable (fun z => (ord s : ℂ) * (z - s)⁻¹) c R := fun s hsS =>
    ContinuousOn.circleIntegrable hR.le (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS)))
  have hterm : ∀ s ∈ S, (∮ z in C(c, R), (ord s : ℂ) * (z - s)⁻¹)
      = (ord s : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := fun s hsS => by
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hS (Finset.mem_coe.2 hsS))]
  rw [circleIntegral.integral_fun_sum hP_intble, Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  ring

/-- Subtracting the principal part cancels every simple pole of `logDeriv F`: if `F` is meromorphic
on the disc with order `ord z` at each `z ∈ S` and is analytic and non-vanishing off `S`, then
`logDeriv F − ∑_{s∈S} ord s · (· − s)⁻¹` is pole-free, so its circle integral vanishes. -/
private theorem circleIntegral_logDeriv_sub_principalPart_eq_zero {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (S : Finset ℂ) (ord : ℂ → ℤ) (hF_mero : MeromorphicOn F (Metric.closedBall c R))
    (hord_F : ∀ z ∈ S, meromorphicOrderAt F z = (ord z : WithTop ℤ))
    (hoffF : ∀ z ∈ Metric.closedBall c R, z ∉ S → AnalyticAt ℂ F z ∧ F z ≠ 0) :
    circleIntegral (fun z => logDeriv F z - ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹) c R = 0 := by
  have hP_mero : MeromorphicOn (fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹)
      (Metric.closedBall c R) := by
    refine MeromorphicOn.fun_sum fun s z _ => ?_
    exact (MeromorphicAt.const (ord s : ℂ) z).mul
      (((MeromorphicAt.id z).sub (MeromorphicAt.const s z)).inv)
  refine circleIntegral_eq_zero_of_meromorphicOrderAt_nonneg hR.le (hF_mero.logDeriv.sub hP_mero) ?_
  intro z hz
  by_cases hzS : z ∈ S
  · have hz_ord : meromorphicOrderAt F z = (ord z : WithTop ℤ) := hord_F z hzS
    obtain ⟨g, hg_an, hg_ne, hg_germ⟩ :=
      logDeriv_eventuallyEq_principalPart (hF_mero z hz) hz_ord
    have hA_eq : (fun w => logDeriv F w - ∑ s ∈ S, (ord s : ℂ) * (w - s)⁻¹) =ᶠ[𝓝[≠] z]
        fun w => logDeriv g w - ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹ := by
      filter_upwards [hg_germ] with w hw
      simp only [← Finset.add_sum_erase S (fun s => (ord s : ℂ) * (w - s)⁻¹) hzS]
      rw [hw]; ring
    have hrest_an : AnalyticAt ℂ (fun w => ∑ s ∈ S.erase z, (ord s : ℂ) * (w - s)⁻¹) z :=
      Finset.analyticAt_fun_sum _ fun s hs =>
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv
          (sub_ne_zero.2 (Ne.symm (Finset.ne_of_mem_erase hs))))
    rw [meromorphicOrderAt_congr hA_eq]
    exact ((analyticAt_logDeriv_of_analyticAt hg_an hg_ne).sub hrest_an).meromorphicOrderAt_nonneg
  · have hz_off := hoffF z hz hzS
    have hP_an : AnalyticAt ℂ (fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹) z := by
      refine Finset.analyticAt_fun_sum _ fun s hsS =>
        analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.2 ?_))
      rintro rfl; exact hzS hsS
    exact ((analyticAt_logDeriv_of_analyticAt hz_off.1 hz_off.2).sub
      hP_an).meromorphicOrderAt_nonneg

/-- **The argument principle.** If `f` is meromorphic on the closed disc `C(c, R)` (`R > 0`) with
all its nonzero-order points contained in a finite set `S` inside the open disc, with orders `ord`,
then the contour integral of the logarithmic derivative counts the zeros minus the poles with
multiplicity:
`∮_{C(c,R)} f'/f = 2πi · ∑_{z ∈ S} ord z`. -/
theorem argumentPrinciple {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (S : Finset ℂ) (ord : ℂ → ℤ)
    (hf : MeromorphicOn f (Metric.closedBall c R)) (hS : (S : Set ℂ) ⊆ Metric.ball c R)
    (hsupp : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z ∈ S)
    (hord : ∀ z ∈ S, meromorphicOrderAt f z = (ord z : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R = 2 * (Real.pi : ℂ) * Complex.I * (∑ z ∈ S, (ord z : ℂ)) := by
  set F := toMeromorphicNFOn f (Metric.closedBall c R) with hF_def
  have hF_nf : MeromorphicNFOn F (Metric.closedBall c R) := meromorphicNFOn_toMeromorphicNFOn f _
  have hF_mero : MeromorphicOn F (Metric.closedBall c R) := hF_nf.meromorphicOn
  have hordF : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt F z = meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_toMeromorphicNFOn hf hz
  have hoffF : ∀ z ∈ Metric.closedBall c R, z ∉ S → AnalyticAt ℂ F z ∧ F z ≠ 0 := by
    intro z hz hzS
    have h0 : meromorphicOrderAt F z = 0 := by
      rw [hordF z hz]; by_contra h; exact hzS (hsupp z hz h)
    exact ⟨(hF_nf hz).meromorphicOrderAt_nonneg_iff_analyticAt.1 h0.symm.le,
      (hF_nf hz).meromorphicOrderAt_eq_zero_iff.1 h0⟩
  have hord_F : ∀ z ∈ S, meromorphicOrderAt F z = (ord z : WithTop ℤ) := fun z hzS =>
    (hordF z (Metric.ball_subset_closedBall (hS (Finset.mem_coe.2 hzS)))).trans (hord z hzS)
  have hsphere_notS : ∀ z ∈ Metric.sphere c R, z ∉ S := fun z hz hzS => by
    rw [Metric.mem_sphere] at hz
    exact absurd hz (ne_of_lt (Metric.mem_ball.1 (hS (Finset.mem_coe.2 hzS))))
  rw [circleIntegral_logDeriv_toMeromorphicNFOn hR hf, ← hF_def]
  have hlogF_cont : ContinuousOn (logDeriv F) (Metric.sphere c R) := fun z hz =>
    (analyticAt_logDeriv_of_analyticAt
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).1
      (hoffF z (sphere_subset_closedBall hz) (hsphere_notS z hz)).2).continuousAt.continuousWithinAt
  have hzs_ne : ∀ z ∈ Metric.sphere c R, ∀ s ∈ S, z ≠ s := by
    intro z hz s hsS h; subst h; exact absurd hsS (hsphere_notS z hz)
  have hP_cont : ContinuousOn (fun z => ∑ s ∈ S, (ord s : ℂ) * (z - s)⁻¹) (Metric.sphere c R) :=
    continuousOn_finsetSum S fun s hsS => continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => sub_ne_zero.2 (hzs_ne z hz s hsS))
  have hsub := (circleIntegral.integral_sub (hlogF_cont.circleIntegrable hR.le)
    (hP_cont.circleIntegrable hR.le)).symm
  rw [circleIntegral_logDeriv_sub_principalPart_eq_zero hR S ord hF_mero hord_F hoffF,
    sub_eq_zero] at hsub
  rw [hsub, circleIntegral_principalPart hR S ord hS]

/-- **Local argument principle.** If `f` is meromorphic on the closed disc `C(c, R)` (`R > 0`) and
the centre `c` is the only point of the disc that may have nonzero meromorphic order — every other
point is at worst a removable singularity — then the contour integral of the logarithmic derivative
recovers the order `n = meromorphicOrderAt f c` at the centre:
`∮_{C(c,R)} f'/f = 2πi · n`. Thus the integral counts the zero (`n > 0`) or pole (`n < 0`) at the
centre with multiplicity, and vanishes when `c` too has order `0`. This is the `S = {c}` case of
`argumentPrinciple`. -/
theorem argumentPrinciple_local {f : ℂ → ℂ} {c : ℂ} {R : ℝ} {n : ℤ} (hR : 0 < R)
    (hf : MeromorphicOn f (Metric.closedBall c R))
    (honly : ∀ z ∈ Metric.closedBall c R, meromorphicOrderAt f z ≠ 0 → z = c)
    (hn : meromorphicOrderAt f c = (n : WithTop ℤ)) :
    circleIntegral (logDeriv f) c R = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
  have key := argumentPrinciple hR {c} (fun _ => n) hf
    (by rw [Finset.coe_singleton, Set.singleton_subset_iff]; exact Metric.mem_ball_self hR)
    (fun z hz hz0 => Finset.mem_singleton.2 (honly z hz hz0))
    (fun z hz => by rw [Finset.mem_singleton.1 hz]; exact hn)
  simpa using key

end TauCeti.Contour
