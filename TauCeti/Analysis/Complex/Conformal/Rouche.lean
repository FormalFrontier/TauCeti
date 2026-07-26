/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Divisor
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Rouché's theorem

If `f` and `g` are holomorphic on a closed disc and `‖f - g‖ < ‖f‖` everywhere on the bounding
circle, then `f` and `g` have the same number of zeros inside, counted with multiplicity. This is
the first target of layer **L0 (the local-mapping engine)** of the conformal-mapping roadmap.

The proof is the classical argument-principle one. On the circle the hypothesis forces `f ≠ 0`, so
the quotient `h = g / f` is defined there, and `‖h - 1‖ < 1` puts `h` inside the disc of radius one
about `1`. That disc lies in the right half-plane, hence in `Complex.slitPlane`, where
`Complex.log` is holomorphic — so `Complex.log ∘ h` is a primitive of `logDeriv h` at every point
of the circle and `∮ logDeriv h = 0` by
`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`. Splitting `logDeriv h` as
`logDeriv g - logDeriv f` (`logDeriv_div`, valid pointwise on the circle since neither function
vanishes there) turns that into `∮ logDeriv g = ∮ logDeriv f`, and the argument principle
(`TauCeti.Contour.argumentPrinciple_divisor`) converts each side into a sum of zero orders.

Note that the primitive is only ever needed *on the circle*: the lemma consuming it asks for a
`HasDerivWithinAt` there, not on a neighbourhood of the disc. That is what keeps the proof free of
any simply-connectedness or branch-construction machinery — `h` may well have zeros and poles
inside the disc, and indeed the theorem is about exactly those.

The count is expressed with Mathlib's `analyticOrderNatAt`, summed over the open disc. Care is
needed about infinite order: `analyticOrderNatAt` sends a locally identically-zero function to `0`,
and such a point is likewise absent from the support of `MeromorphicOn.divisor`, so in general the
divisor support is the set of zeros *of finite order* rather than the zero set outright. Under the
Rouché hypotheses that distinction is vacuous: `‖f - g‖ < ‖f‖` forces `f` to be zero-free on the
circle, and `closedBall c R` is convex hence preconnected, so
`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates finite order from a boundary
point to the whole disc — neither `f` nor `g` vanishes identically near any point of it.

## Main results

* `TauCeti.rouche` — if `‖f z - g z‖ < ‖f z‖` on `sphere c R`, then `f` and `g` have equal zero
  counts in `ball c R`, each counted with multiplicity.
* `TauCeti.divisor_eq_analyticOrderNatAt` — the divisor of a holomorphic function is its order of
  vanishing; exposed so downstream zero-counting arguments can reuse it.

## Coordination with upstream Mathlib

Mathlib has no Rouché theorem. However, per the *Coordination with upstream Mathlib* section of
`ConformalMapping/README.md`, this layer overlaps
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which proves L0-level material (an argument
principle, Hurwitz) internally as private lemmas. **This file is therefore a temporary shim**: once
the corresponding Mathlib lemmas land, this statement should be backed by them — or deleted and its
consumers refactored — rather than maintained as an independent re-proof. What Tau Ceti adds at L0
is named, discoverable API, not first proof.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4.
* S. Lang, *Complex Analysis* (GTM 103), Ch. VI.
-/

public section

open Complex Metric

namespace TauCeti

variable {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}

/-- On the circle the Rouché hypothesis forces `f` to be zero-free: at a zero of `f` it would read
`‖g z‖ < 0`. -/
private lemma ne_zero_left {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖) : f z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h
  linarith [norm_nonneg (g z)]

/-- On the circle the Rouché hypothesis forces `g` to be zero-free too: at a zero of `g` it would
read `‖f z‖ < ‖f z‖`. -/
private lemma ne_zero_right {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖) : g z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h

/-- A holomorphic function has meromorphic order `0` exactly where it does not vanish. This is the
form the argument principle's circle hypothesis takes. -/
private lemma order_eq_zero (hf : AnalyticOnNhd ℂ f (closedBall c R)) {z : ℂ}
    (hz : z ∈ closedBall c R) (hne : f z ≠ 0) : meromorphicOrderAt f z = 0 := by
  rw [(hf z hz).meromorphicOrderAt_eq, (hf z hz).analyticOrderAt_eq_zero.2 hne]
  rfl

/-- The logarithmic derivative of a function holomorphic and zero-free on a circle is continuous
there, hence circle-integrable. -/
private lemma circleIntegrable_logDeriv (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hne : ∀ z ∈ sphere c R, f z ≠ 0) : CircleIntegrable (logDeriv f) c R := by
  refine ContinuousOn.circleIntegrable hR.le ?_
  have hsub : sphere c R ⊆ closedBall c R := sphere_subset_closedBall
  have hd : ContinuousOn (deriv f) (sphere c R) := (hf.deriv.continuousOn).mono hsub
  have hc : ContinuousOn f (sphere c R) := (hf.continuousOn).mono hsub
  exact hd.div hc hne

/-- For a holomorphic function the divisor records the order of vanishing. The identity also holds
at a point of infinite order, where both sides read `0`.

This is the bridge between `MeromorphicOn.divisor` — whose support is finite on a ball by
`MeromorphicOn.divisor_ball_support_finite` — and the `analyticOrderNatAt` vocabulary the zero
counts are stated in, so downstream files can reuse it instead of rebuilding the correspondence.
Note that the finiteness is of the divisor's *support*, equivalently of the zeros of finite order:
a point where `f` vanishes identically has divisor value `0` and is absent from it. -/
theorem divisor_eq_analyticOrderNatAt {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  -- `analyticOrderNatAt` is `(analyticOrderAt · ·).toNat`; this is the one place the proof needs
  -- that definitional equality, so unfold it here rather than in the statements.
  cases h : analyticOrderAt f z with
  | top => simp [analyticOrderNatAt, h]
  | coe n => simp [analyticOrderNatAt, h]

/-- The contour integral of `logDeriv (g / f)` around the circle vanishes: the hypothesis confines
`g / f` to the slit plane there, where `Complex.log` supplies a primitive. -/
private lemma circleIntegral_logDeriv_div_eq_zero (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv (fun w => g w / f w) z) = 0 := by
  refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt
    (f := fun w => Complex.log (g w / f w)) hR.le (fun z hz => ?_)
  have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
  have hlt := hs z hz
  have hfz : f z ≠ 0 := ne_zero_left hlt
  have hq1 : ‖g z / f z - 1‖ < 1 := by
    have e : g z / f z - 1 = -((f z - g z) / f z) := by field_simp; ring
    rw [e, norm_neg, norm_div]
    exact (div_lt_one (by positivity)).2 hlt
  have hslit : g z / f z ∈ slitPlane := by
    simpa using Complex.mem_slitPlane_of_norm_lt_one hq1
  have hf' : HasDerivAt f (deriv f z) z := (hf z hzc).differentiableAt.hasDerivAt
  have hg' : HasDerivAt g (deriv g z) z := (hg z hzc).differentiableAt.hasDerivAt
  have hq : HasDerivAt (fun w => g w / f w)
      ((deriv g z * f z - g z * deriv f z) / f z ^ 2) z := hg'.div hf' hfz
  have hcomp := (Complex.hasDerivAt_log hslit).comp z hq
  have hval : logDeriv (fun w => g w / f w) z
      = (g z / f z)⁻¹ * ((deriv g z * f z - g z * deriv f z) / f z ^ 2) := by
    rw [logDeriv_apply, hq.deriv]
    field_simp
  rw [hval]
  exact hcomp.hasDerivWithinAt

/-- The count produced by the argument principle, in the vocabulary of orders of vanishing: the
finitely supported sum of the divisor equals the cast of the finitely supported sum of
`analyticOrderNatAt` over the open disc. Both sides assign `0` at a point of infinite order, so
this counts zeros of finite order; the caller supplies the hypotheses that exclude the other
kind. -/
private lemma finsum_divisor_cast {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall c R)) :
    (∑ᶠ z, ((MeromorphicOn.divisor h (ball c R) z : ℤ) : ℂ))
      = ((∑ᶠ z ∈ ball c R, analyticOrderNatAt h z : ℕ) : ℂ) := by
  classical
  set S := (MeromorphicOn.divisor_ball_support_finite hh.meromorphicOn).toFinset with hS
  have hsub : (S : Set ℂ) ⊆ ball c R := fun z hz =>
    (MeromorphicOn.divisor h (ball c R)).supportWithinDomain
      (by simpa [hS, Set.Finite.mem_toFinset] using hz)
  have h1 : (∑ᶠ z, ((MeromorphicOn.divisor h (ball c R) z : ℤ) : ℂ))
      = ∑ z ∈ S, ((MeromorphicOn.divisor h (ball c R) z : ℤ) : ℂ) := by
    refine finsum_eq_finsetSum_of_support_subset _ (fun z hz => ?_)
    simp only [Function.mem_support, ne_eq, Int.cast_eq_zero] at hz
    simpa [hS, Set.Finite.mem_toFinset] using hz
  have h2 : (∑ᶠ z ∈ ball c R, analyticOrderNatAt h z)
      = ∑ z ∈ S, analyticOrderNatAt h z := by
    refine finsum_mem_eq_sum_of_subset _ (fun z hz => ?_) hsub
    obtain ⟨hzb, hzs⟩ := hz
    simp only [Function.mem_support, ne_eq] at hzs
    have hd : MeromorphicOn.divisor h (ball c R) z ≠ 0 := by
      rw [divisor_eq_analyticOrderNatAt (hh.mono ball_subset_closedBall) hzb]
      exact_mod_cast hzs
    simpa [hS, Set.Finite.mem_toFinset] using hd
  rw [h1, h2]
  push_cast
  refine Finset.sum_congr rfl (fun z hz => ?_)
  rw [divisor_eq_analyticOrderNatAt (hh.mono ball_subset_closedBall)
    (hsub (by simpa [hS] using hz))]
  push_cast
  ring

/-- **Rouché's theorem** for a disc. If `f` and `g` are holomorphic on the closed disc
`closedBall c R` and `‖f z - g z‖ < ‖f z‖` at every point `z` of the bounding circle, then `f` and
`g` have the same number of zeros in `ball c R`, each counted with multiplicity. The hypothesis
forces both functions to be zero-free on the circle, hence of finite order throughout the disc, so
every zero is genuinely counted.

The counts are the canonical finitely supported sums `∑ᶠ z ∈ ball c R, analyticOrderNatAt · z`;
no finiteness witness appears in the statement. -/
theorem rouche (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z)
      = ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z := by
  have hnef : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz => ne_zero_left (hs z hz)
  have hneg : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz => ne_zero_right (hs z hz)
  have hsplit : (∮ z in C(c, R), logDeriv g z) = (∮ z in C(c, R), logDeriv f z) := by
    have heq : Set.EqOn (logDeriv (fun w => g w / f w))
        (fun z => logDeriv g z - logDeriv f z) (sphere c R) := by
      intro z hz
      exact logDeriv_div z (hneg z hz) (hnef z hz)
        (hg z (sphere_subset_closedBall hz)).differentiableAt
        (hf z (sphere_subset_closedBall hz)).differentiableAt
    have h0 := circleIntegral_logDeriv_div_eq_zero hR hf hg hs
    rw [circleIntegral.integral_congr hR.le heq,
      circleIntegral.integral_sub (circleIntegrable_logDeriv hR hg hneg)
        (circleIntegrable_logDeriv hR hf hnef)] at h0
    linear_combination h0
  rw [TauCeti.Contour.argumentPrinciple_divisor hR hg.meromorphicOn
        (fun z hz => order_eq_zero hg (sphere_subset_closedBall hz) (hneg z hz)),
    TauCeti.Contour.argumentPrinciple_divisor hR hf.meromorphicOn
        (fun z hz => order_eq_zero hf (sphere_subset_closedBall hz) (hnef z hz))] at hsplit
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hsum := mul_left_cancel₀ hpi hsplit
  rw [finsum_divisor_cast hg, finsum_divisor_cast hf] at hsum
  exact_mod_cast hsum.symm

end TauCeti
