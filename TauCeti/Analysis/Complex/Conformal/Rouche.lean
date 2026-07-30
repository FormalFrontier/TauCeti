/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Contour.Argument.Divisor
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Rouché's theorem

If `f` and `g` are holomorphic on a closed disc and `‖f - g‖ < ‖f‖ + ‖g‖` everywhere on the
bounding circle, then `f` and `g` have the same number of zeros inside, counted with multiplicity.
This *symmetric* hypothesis — Estermann's form of Rouché's theorem — is the one proved here; the
familiar asymmetric hypothesis `‖f - g‖ < ‖f‖` implies it, so the classical statement is a
corollary. Rouché is the first target of layer **L0 (the local-mapping engine)** of the
conformal-mapping roadmap.

The proof is the classical argument-principle one. On the circle the hypothesis forces both `f ≠ 0`
and `g ≠ 0`, so the quotient `h = g / f` is defined and nonzero there; moreover `h` avoids the
closed ray `(-∞, 0]`, since at a nonpositive real value `t` of `h` the hypothesis would read
`(1 - t)‖f‖ < (1 - t)‖f‖`. Avoiding that ray is exactly membership in `Complex.slitPlane`, where
`Complex.log` is holomorphic — so `Complex.log ∘ h` is a primitive of `logDeriv h` at every point
of the circle and `∮ logDeriv h = 0` by
`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`. Splitting `logDeriv h` as
`logDeriv g - logDeriv f` (`logDeriv_div`, valid pointwise on the circle since neither function
vanishes there) turns that into `∮ logDeriv g = ∮ logDeriv f`, and the argument principle
(`TauCeti.Contour.argumentPrinciple_divisor`) converts each side into a sum of zero orders.

It is the passage to the slit plane, rather than to the disc `ball 1 1`, that buys the symmetric
hypothesis: `‖h - 1‖ < 1` says `h` lies in a disc that happens to miss the ray, whereas
`‖1 - h‖ < 1 + ‖h‖` says precisely that `h` misses the ray, and nothing more.

Note that the primitive is only ever needed *on the circle*: the lemma consuming it asks for a
`HasDerivWithinAt` there, not on a neighbourhood of the disc. That is what keeps the proof free of
any simply-connectedness or branch-construction machinery — `h` may well have zeros and poles
inside the disc, and indeed the theorem is about exactly those.

The count is expressed with Mathlib's `analyticOrderNatAt`, summed over the open disc. Care is
needed about infinite order: `analyticOrderNatAt` sends a locally identically-zero function to `0`,
and such a point is likewise absent from the support of `MeromorphicOn.divisor`, so in general the
divisor support is the set of zeros *of finite order* rather than the zero set outright. Under the
Rouché hypotheses that distinction is vacuous: the hypothesis forces `f` to be zero-free on the
circle, and `closedBall c R` is convex hence preconnected, so
`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` propagates finite order from a boundary
point to the whole disc — neither `f` nor `g` vanishes identically near any point of it.

That same observation is what makes the count *detect* zeros rather than merely count them:
`TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff` says the count vanishes exactly when the
function has no zero in the open disc, so Rouché transfers the *existence* of a zero from one
function to the other. That transfer, not the numerical equality, is how Rouché is normally used.

## Main results

* `TauCeti.rouche_symm` — the symmetric (Estermann) form: if `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on
  `sphere c R`, then `f` and `g` have equal zero counts in `ball c R`.
* `TauCeti.rouche` — if `‖f z - g z‖ < ‖f z‖` on `sphere c R`, then `f` and `g` have equal zero
  counts in `ball c R`, each counted with multiplicity.
* `TauCeti.rouche_add` — the classical additive phrasing: if `‖g z‖ < ‖f z‖` on `sphere c R`, then
  `f` and `f + g` have equal zero counts in `ball c R`.
* `TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff` — the zero count over `ball c R` vanishes
  exactly when the function has no zero there.
* `TauCeti.rouche_symm_exists_eq_zero_iff`, `TauCeti.rouche_exists_eq_zero_iff` — under the
  respective hypotheses, `f` has a zero in `ball c R` if and only if `g` does.

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

/-- The symmetric Rouché hypothesis forces `f` to be zero-free: at a zero of `f` it would read
`‖g z‖ < ‖g z‖`. -/
private lemma ne_zero_left {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) : f z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp only [zero_sub, norm_neg, norm_zero, zero_add] at h
  exact lt_irrefl _ h

/-- The symmetric Rouché hypothesis forces `g` to be zero-free too: at a zero of `g` it would read
`‖f z‖ < ‖f z‖`. -/
private lemma ne_zero_right {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) : g z ≠ 0 := by
  intro h0
  rw [h0] at h
  simp only [sub_zero, norm_zero, add_zero] at h
  exact lt_irrefl _ h

/-- If the triangle inequality `‖1 - w‖ ≤ 1 + ‖w‖` is strict at `w`, then `w` lies in the slit
plane. Indeed equality holds exactly on the nonpositive reals — there `‖1 - w‖` and `1 + ‖w‖` are
both `1 - w.re` — and those are exactly the points the slit plane omits. This is the geometric
content of the symmetric Rouché hypothesis. -/
private lemma mem_slitPlane_of_norm_one_sub_lt {w : ℂ} (h : ‖1 - w‖ < 1 + ‖w‖) :
    w ∈ slitPlane := by
  by_contra hw
  rw [mem_slitPlane_iff] at hw
  push Not at hw
  obtain ⟨hre, him⟩ := hw
  have hwe : w = (w.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hwe] at h
  have h1 : (1 : ℂ) - (w.re : ℂ) = ((1 - w.re : ℝ) : ℂ) := by push_cast; ring
  rw [h1, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - w.re), abs_of_nonpos hre] at h
  linarith

/-- The quotient `g / f` of the symmetric Rouché hypothesis lands in the slit plane: dividing the
hypothesis by `‖f z‖ > 0` turns it into the hypothesis of `mem_slitPlane_of_norm_one_sub_lt`. -/
private lemma div_mem_slitPlane {z : ℂ} (h : ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    g z / f z ∈ slitPlane := by
  have hfz : f z ≠ 0 := ne_zero_left h
  have hpos : (0 : ℝ) < ‖f z‖ := norm_pos_iff.2 hfz
  refine mem_slitPlane_of_norm_one_sub_lt ?_
  have e : (1 : ℂ) - g z / f z = (f z - g z) / f z := by field_simp
  rw [e, norm_div, norm_div, div_lt_iff₀ hpos]
  have e2 : (1 + ‖g z‖ / ‖f z‖) * ‖f z‖ = ‖f z‖ + ‖g z‖ := by
    field_simp
  rw [e2]
  exact h

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

/-- The contour integral of `logDeriv (g / f)` around the circle vanishes: the hypothesis confines
`g / f` to the slit plane there, where `Complex.log` supplies a primitive. -/
private lemma circleIntegral_logDeriv_div_eq_zero (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    (∮ z in C(c, R), logDeriv (fun w => g w / f w) z) = 0 := by
  refine circleIntegral.integral_eq_zero_of_hasDerivWithinAt
    (f := fun w => Complex.log (g w / f w)) hR.le (fun z hz => ?_)
  have hzc : z ∈ closedBall c R := sphere_subset_closedBall hz
  have hlt := hs z hz
  have hfz : f z ≠ 0 := ne_zero_left hlt
  have hslit : g z / f z ∈ slitPlane := div_mem_slitPlane hlt
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
      rw [Contour.divisor_eq_analyticOrderNatAt (hh.mono ball_subset_closedBall).meromorphicOn
        (hh _ (ball_subset_closedBall hzb)) hzb]
      exact_mod_cast hzs
    simpa [hS, Set.Finite.mem_toFinset] using hd
  rw [h1, h2]
  push_cast
  refine Finset.sum_congr rfl (fun z hz => ?_)
  have hzb' := hsub (by simpa [hS] using hz)
  rw [Contour.divisor_eq_analyticOrderNatAt (hh.mono ball_subset_closedBall).meromorphicOn
    (hh _ (ball_subset_closedBall hzb')) hzb']
  push_cast
  ring

/-- **Rouché's theorem, symmetric form** (Estermann). If `f` and `g` are holomorphic on the closed
disc `closedBall c R` and `‖f z - g z‖ < ‖f z‖ + ‖g z‖` at every point `z` of the bounding circle,
then `f` and `g` have the same number of zeros in `ball c R`, each counted with multiplicity. The
hypothesis forces both functions to be zero-free on the circle, hence of finite order throughout
the disc, so every zero is genuinely counted.

The hypothesis is the strict form of the triangle inequality `‖f z - g z‖ ≤ ‖f z‖ + ‖g z‖`, so it
says exactly that `f z` and `g z` never point in *opposite* directions on the circle. It is
symmetric in `f` and `g` and strictly weaker than the classical `‖f z - g z‖ < ‖f z‖` of
`TauCeti.rouche`.

The counts are the canonical finitely supported sums `∑ᶠ z ∈ ball c R, analyticOrderNatAt · z`;
no finiteness witness appears in the statement. -/
theorem rouche_symm (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
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

/-- **Rouché's theorem** for a disc, classical form. If `f` and `g` are holomorphic on the closed
disc `closedBall c R` and `‖f z - g z‖ < ‖f z‖` at every point `z` of the bounding circle, then `f`
and `g` have the same number of zeros in `ball c R`, each counted with multiplicity.

This is the special case of `TauCeti.rouche_symm` obtained by discarding the nonnegative summand
`‖g z‖` from the symmetric hypothesis. -/
theorem rouche (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z)
      = ∑ᶠ z ∈ ball c R, analyticOrderNatAt g z :=
  rouche_symm hR hf hg fun z hz => (hs z hz).trans_le (le_add_of_nonneg_right (norm_nonneg _))

/-- **Rouché's theorem**, in the additive phrasing of most textbooks: a holomorphic perturbation
`g` that is dominated by `f` on the bounding circle does not change the number of zeros inside. -/
theorem rouche_add (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z)
      = ∑ᶠ z ∈ ball c R, analyticOrderNatAt (fun w => f w + g w) z :=
  rouche hR hf (hf.add hg) fun z hz => by simpa using hs z hz

/-!
## Detecting zeros

Rouché is usually applied not to compare two counts but to transfer the *existence* of a zero. The
bridge is that the count vanishes exactly when there is no zero, which needs the finite-order
argument recorded in the module docstring.
-/

/-- Under the standing Rouché hypothesis that `f` is zero-free on the bounding circle, `f` does not
vanish identically near any point of the closed disc: the disc is preconnected, so a point of
infinite order would force `f ≡ 0`, contradicting nonvanishing at `c + R`. -/
private lemma analyticOrderAt_ne_top_of_sphere (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hs : ∀ z ∈ sphere c R, f z ≠ 0) {z₀ : ℂ} (hz₀ : z₀ ∈ closedBall c R) :
    analyticOrderAt f z₀ ≠ ⊤ := by
  intro htop
  have hzero : Set.EqOn f 0 (closedBall c R) :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall c R).isPreconnected hz₀
      (analyticOrderAt_eq_top.1 htop)
  have hmem : c + (R : ℂ) ∈ sphere c R := by
    rw [mem_sphere_iff_norm]
    simp [Complex.norm_real, abs_of_pos hR]
  exact hs _ hmem (by simpa using hzero (sphere_subset_closedBall hmem))

/-- **The Rouché count detects zeros.** For `f` holomorphic on `closedBall c R` and zero-free on the
bounding circle, the count `∑ᶠ z ∈ ball c R, analyticOrderNatAt f z` vanishes precisely when `f` has
no zero in the open disc.

The nontrivial direction is that a zero contributes a *nonzero* order: `analyticOrderNatAt` sends a
point of infinite order to `0`, and it is nonvanishing on the circle that rules that out. -/
theorem finsum_analyticOrderNatAt_ball_eq_zero_iff (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hs : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∑ᶠ z ∈ ball c R, analyticOrderNatAt f z) = 0 ↔ ∀ z ∈ ball c R, f z ≠ 0 := by
  constructor
  · intro hsum z₀ hz₀ h0
    have hana : AnalyticAt ℂ f z₀ := hf z₀ (ball_subset_closedBall hz₀)
    have hne : analyticOrderNatAt f z₀ ≠ 0 := by
      have h1 : analyticOrderAt f z₀ ≠ 0 := hana.analyticOrderAt_ne_zero.2 h0
      have h2 : analyticOrderAt f z₀ ≠ ⊤ :=
        analyticOrderAt_ne_top_of_sphere hR hf hs (ball_subset_closedBall hz₀)
      simp [analyticOrderNatAt, ENat.toNat_eq_zero, h1, h2]
    have hfin : Function.HasFiniteSupport
        ((ball c R).indicator fun z => analyticOrderNatAt f z) := by
      change (Function.support _).Finite
      refine Set.Finite.subset (MeromorphicOn.divisor_ball_support_finite hf.meromorphicOn) ?_
      intro z hz
      rw [Set.support_indicator] at hz
      obtain ⟨hzb, hzs⟩ := hz
      simp only [Function.mem_support, ne_eq] at hzs ⊢
      rw [Contour.divisor_eq_analyticOrderNatAt (hf.mono ball_subset_closedBall).meromorphicOn
        (hf _ (ball_subset_closedBall hzb)) hzb]
      exact_mod_cast hzs
    have hle := single_le_finsum z₀ hfin (fun _ => Nat.zero_le _)
    rw [← finsum_mem_def, hsum, Set.indicator_of_mem hz₀] at hle
    exact hne (Nat.le_zero.1 hle)
  · intro h
    have hz : ∀ z ∈ ball c R, analyticOrderNatAt f z = 0 := fun z hzb => by
      have := (hf z (ball_subset_closedBall hzb)).analyticOrderAt_eq_zero.2 (h z hzb)
      simp [analyticOrderNatAt, this]
    rw [finsum_mem_congr rfl hz]
    simp

/-- **Rouché's theorem as a zero-detection principle**, symmetric form. Under the hypothesis
`‖f z - g z‖ < ‖f z‖ + ‖g z‖` on the bounding circle, `f` has a zero in the open disc if and only
if `g` does. This is how Rouché is normally used: to import a zero of a comparison function. -/
theorem rouche_symm_exists_eq_zero_iff (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖ + ‖g z‖) :
    (∃ z ∈ ball c R, f z = 0) ↔ ∃ z ∈ ball c R, g z = 0 := by
  have hnef : ∀ z ∈ sphere c R, f z ≠ 0 := fun z hz => ne_zero_left (hs z hz)
  have hneg : ∀ z ∈ sphere c R, g z ≠ 0 := fun z hz => ne_zero_right (hs z hz)
  have hcount := rouche_symm hR hf hg hs
  have hef := finsum_analyticOrderNatAt_ball_eq_zero_iff hR hf hnef
  have heg := finsum_analyticOrderNatAt_ball_eq_zero_iff hR hg hneg
  constructor
  · rintro ⟨z, hz, h0⟩
    by_contra hcon
    push Not at hcon
    exact hef.1 (hcount.trans (heg.2 hcon)) z hz h0
  · rintro ⟨z, hz, h0⟩
    by_contra hcon
    push Not at hcon
    exact heg.1 (hcount.symm.trans (hef.2 hcon)) z hz h0

/-- **Rouché's theorem as a zero-detection principle**, classical form: under
`‖f z - g z‖ < ‖f z‖` on the bounding circle, `f` has a zero in the open disc if and only if `g`
does. -/
theorem rouche_exists_eq_zero_iff (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖f z - g z‖ < ‖f z‖) :
    (∃ z ∈ ball c R, f z = 0) ↔ ∃ z ∈ ball c R, g z = 0 :=
  rouche_symm_exists_eq_zero_iff hR hf hg fun z hz =>
    (hs z hz).trans_le (le_add_of_nonneg_right (norm_nonneg _))

end TauCeti
