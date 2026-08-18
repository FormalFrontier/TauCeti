/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Divisor
public import TauCeti.Analysis.Complex.ZeroCount
public import TauCeti.Analysis.Contour.Argument.Cycle
public import TauCeti.Analysis.Contour.Argument.Divisor
import TauCeti.Analysis.Contour.LogDerivFTC
import Mathlib.Analysis.Calculus.LogDeriv
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

The circle is not essential to the argument, only convenient: the second half of the file replays
it along an arbitrary closed piecewise-`C¹` curve that is null-homologous in an open set carrying
both functions, weighting each zero by the winding number of the curve about it — and there the
functions may be meromorphic, the preserved quantity becoming zeros minus poles. The homological
argument principle `TauCeti.Contour.argumentPrinciple_nullHomologous` replaces the circle one, and
the slit-plane primitive is pushed across the corners of the curve by
`TauCeti.Contour.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane`, the curve form of the
countable-exception logarithmic-derivative FTC.

That equality of logarithmic-derivative integrals also has a purely geometric reading, obtained by
running it through `TauCeti.Contour.windingNumber_comp_eq_integral_logDeriv`: the two *image* curves
`f ∘ γ` and `g ∘ γ` wind equally often about the origin. That is the classical "dog on a leash"
form, and it is stronger than the counting statement, needing only analyticity at each point of the
curve — no single ambient open set, no finite `S`, no null-homology — because the vanishing of the
slit-plane integral already holds there.

That same observation is what makes the count *detect* zeros rather than merely count them:
`TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff`, from `TauCeti.Analysis.Complex.ZeroCount`,
says the count vanishes exactly when the function has no zero in the open disc, so Rouché transfers
the *existence* of a zero from one function to the other. That transfer, not the numerical
equality, is how Rouché is normally used.

## Main results

* `TauCeti.rouche_symm` — the symmetric (Estermann) form: if `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on
  `sphere c R`, then `f` and `g` have equal zero counts in `ball c R`.
* `TauCeti.rouche` — if `‖f z - g z‖ < ‖f z‖` on `sphere c R`, then `f` and `g` have equal zero
  counts in `ball c R`, each counted with multiplicity.
* `TauCeti.rouche_add` — the classical additive phrasing: if `‖g z‖ < ‖f z‖` on `sphere c R`, then
  `f` and `f + g` have equal zero counts in `ball c R`.
* `TauCeti.exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero` — the witness those
  transfers need: a function that is zero-free on the bounding circle does not vanish identically
  on the closed disc.
* `TauCeti.rouche_symm_exists_eq_zero_iff`, `TauCeti.rouche_exists_eq_zero_iff`,
  `TauCeti.rouche_add_exists_eq_zero_iff` — under the respective hypotheses, `f` has a zero in
  `ball c R` if and only if the function compared to it does.
* `TauCeti.rouche_symm_nullHomologous` — the homology form, for meromorphic `f` and `g`: across an
  arbitrary closed piecewise-`C¹` curve, null-homologous in an open set carrying both functions,
  the enclosed zeros minus poles agree, counted by multiplicity *and* by the winding number of the
  curve about them.
* `TauCeti.rouche_symm_nullHomologous_of_analyticOnNhd`, `TauCeti.rouche_nullHomologous`,
  `TauCeti.rouche_add_nullHomologous` — its holomorphic specialization in the same three
  phrasings as the disc statements.
* `TauCeti.rouche_symm_windingNumber_comp`, `TauCeti.rouche_windingNumber_comp`,
  `TauCeti.rouche_add_windingNumber_comp` — the "dog on a leash" form, in the same three phrasings:
  under the symmetric, the classical, respectively the additive hypothesis along the curve, the
  image curves wind equally often about the origin.

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
bridge is `TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff`: the count vanishes exactly when
there is no zero, provided the function is nonzero somewhere on the closed disc. The Rouché
hypothesis supplies that witness on the bounding circle.
-/

/-- A function that is zero-free on the bounding circle of a disc does not vanish identically on
the closed disc — the boundary point `c + R` witnesses it. The radius may be `0`, where both discs
degenerate to `{c}`. This is the shape in which
`TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff` wants the Rouché hypothesis, and it is the
same shape every zero-detection argument on a disc needs. -/
theorem exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero (hR : 0 ≤ R)
    (hs : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ z ∈ closedBall c R, f z ≠ 0 := by
  have hmem : c + (R : ℂ) ∈ sphere c R := by
    rw [mem_sphere_iff_norm]
    simp [Complex.norm_real, abs_of_nonneg hR]
  exact ⟨_, sphere_subset_closedBall hmem, hs _ hmem⟩

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
  have hef := finsum_analyticOrderNatAt_ball_eq_zero_iff hf
    (exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hR.le hnef)
  have heg := finsum_analyticOrderNatAt_ball_eq_zero_iff hg
    (exists_mem_closedBall_ne_zero_of_forall_mem_sphere_ne_zero hR.le hneg)
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

/-- **Rouché's theorem as a zero-detection principle**, additive form: a holomorphic perturbation
`g` dominated by `f` on the bounding circle neither creates nor destroys zeros inside, so `f` has a
zero in the open disc if and only if `f + g` does. This is the phrasing that reads a zero of a
perturbed function off the unperturbed one, the existence counterpart of `TauCeti.rouche_add`. -/
theorem rouche_add_exists_eq_zero_iff (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hs : ∀ z ∈ sphere c R, ‖g z‖ < ‖f z‖) :
    (∃ z ∈ ball c R, f z = 0) ↔ ∃ z ∈ ball c R, f z + g z = 0 :=
  rouche_exists_eq_zero_iff hR hf (hf.add hg) fun z hz => by simpa using hs z hz

/-!
## Rouché's theorem for a null-homologous cycle

The disc statements above compare the zeros enclosed by a *circle*. The homology forms below
replace the circle by an arbitrary closed piecewise-`C¹` curve `γ`, null-homologous in an open set
`U` carrying both functions: they compare the winding-weighted counts `∑_{z ∈ S} n_z(γ) · ord z`
over a finite set `S` carrying the exceptional points. That is the form Rouché takes on a domain
that is not a disc, and the form in which the multiplicity of enclosure is visible.

At this generality the functions may be *meromorphic*, exactly as in the argument principle the
proof runs through: the quantity that is preserved is then zeros minus poles, each counted with
multiplicity and with winding number. `TauCeti.rouche_symm_nullHomologous` is that statement, with
the orders supplied by the caller; `TauCeti.rouche_symm_nullHomologous_of_analyticOnNhd` is the
holomorphic specialization, whose orders are read off by `analyticOrderNatAt`.

The proof is the disc one, run through `TauCeti.Contour.argumentPrinciple_nullHomologous` instead
of the circle argument principle. What changes is the vanishing step. On a circle the integral of
`logDeriv (g / f)` was killed by `circleIntegral.integral_eq_zero_of_hasDerivWithinAt`; along a
piecewise-`C¹` curve the primitive has to be pushed through the finitely many corners, which is
exactly what the countable exceptional set of `TauCeti.Contour.integral_deriv_div_eq_log_sub_log`
allows; that step is contour theory rather than Rouché, and lives with the FTC it specializes, as
`TauCeti.Contour.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane`. The geometry is unchanged:
the symmetric hypothesis confines `g / f` to `Complex.slitPlane`, where the principal `Complex.log`
is a single-valued primitive of the logarithmic derivative, so the integral is an endpoint
difference and the curve is closed.

The two are stated and proved separately because their interfaces differ, not because the disc case
is out of reach from here. It *is* reachable: analyticity on a neighbourhood of `closedBall c R`
gives, by compactness, analyticity on a slightly larger open ball `U`, in which every closed curve
is null-homologous; the zeros in `closedBall c R` are finite in number, so they can be collected
into an `S`; and the winding number of the bounding circle is `1` at each of them. What that route
costs is exactly that bookkeeping — producing `S`, evaluating the winding numbers, and converting
the resulting weighted `Finset` sum back into the `∑ᶠ` count of `TauCeti.rouche_symm`, which ranges
over the whole open disc with no finiteness hypothesis. In the other direction there is no route at
all: on a general open set the zeros may accumulate at the boundary, so no finite `S` exists and
the cycle form has nothing to say.

Unlike on a circle there is no zero-*detection* corollary here, and that is not an omission: what
fails for a general cycle is the *equivalence*, not detection outright. With winding numbers of
both signs the weighted counts can cancel, so a vanishing count no longer means the function is
zero-free — `TauCeti.finsum_analyticOrderNatAt_ball_eq_zero_iff`, which the disc forms use, has no
cycle analogue. The converse direction survives and needs no corollary: if the weighted count of
`f` is nonzero then by the theorem so is that of `g`, so some `z ∈ S` has nonzero winding number
and `analyticOrderNatAt g z ≠ 0`; null-homology places such a `z` in `U`, where a nonzero order
means `g z = 0`. It is the `iff` that requires a sign hypothesis on the cycle, which the disc case
supplies by winding once.
-/

section Cycle

open MeasureTheory

open scoped Interval

variable {U : Set ℂ} {S : Finset ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **The two argument-principle integrals of a Rouché pair agree.** This is the analytic heart of
every homology form of Rouché's theorem: along a closed piecewise-`C¹` curve on which `f` and `g`
are analytic and never point in opposite directions, the contour integrals of `logDeriv f` and
`logDeriv g` coincide, because their difference is the integral of `logDeriv (g / f)` and the
symmetric hypothesis puts `g / f` in the slit plane. Nothing is assumed off the curve, so the
statement is available to the meromorphic and the holomorphic form alike. -/
private lemma integral_deriv_smul_logDeriv_eq_of_norm_sub_lt
    (hγ : Contour.IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hfa : ∀ t ∈ [[a, b]], AnalyticAt ℂ f (γ t)) (hga : ∀ t ∈ [[a, b]], AnalyticAt ℂ g (γ t))
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖) :
    (∫ t in a..b, deriv γ t • logDeriv f (γ t))
      = ∫ t in a..b, deriv γ t • logDeriv g (γ t) := by
  have hfne : ∀ t ∈ [[a, b]], f (γ t) ≠ 0 := fun t ht => ne_zero_left (hs t ht)
  have hgne : ∀ t ∈ [[a, b]], g (γ t) ≠ 0 := fun t ht => ne_zero_right (hs t ht)
  have hzero := Contour.integral_deriv_smul_logDeriv_eq_zero_of_mem_slitPlane
    (h := fun w => g w / f w) hγ hclosed
    (fun t ht => (hga t ht).div (hfa t ht) (hfne t ht))
    (fun t ht => div_mem_slitPlane (hs t ht))
  have hcong : (∫ t in a..b, deriv γ t • logDeriv (fun w => g w / f w) (γ t))
      = ∫ t in a..b, (deriv γ t • logDeriv g (γ t) - deriv γ t • logDeriv f (γ t)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [logDeriv_fun_div _ (hgne t ht) (hfne t ht) (hga t ht).differentiableAt
      (hfa t ht).differentiableAt, smul_sub]
  rw [hcong, intervalIntegral.integral_sub
    (Contour.intervalIntegrable_deriv_smul_logDeriv hγ hga hgne)
    (Contour.intervalIntegrable_deriv_smul_logDeriv hγ hfa hfne)] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- **Rouché's theorem for a null-homologous cycle, symmetric form** (Estermann). Let `f` and `g`
be meromorphic on an open set `U`, analytic and non-vanishing off a finite set `S`, of orders
`ordf` and `ordg` on `S`, and let `γ` be a closed piecewise-`C¹` curve in `U`, null-homologous in
`U`, missing `S`, and satisfying `‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖` along its length.
Then `f` and `g` enclose the same number of zeros minus poles, each counted with its multiplicity
*and* with the winding number of `γ` about it.

The hypothesis is the strict form of the triangle inequality `‖f z - g z‖ ≤ ‖f z‖ + ‖g z‖`, so it
says exactly that `f` and `g` never point in *opposite* directions along the curve; it is symmetric
in the two functions and strictly weaker than the classical `‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖`.

Exactly as in `TauCeti.Contour.argumentPrinciple_nullHomologous`, points of `S` outside `U` are
harmless rather than excluded — null-homology makes their winding number, hence their contribution
on either side, vanish — so the meromorphy and order hypotheses are conditional on membership in
`U`, and `S` may list ordinary points, of order `0`.

`TauCeti.rouche_symm` is the circle case, proved separately: see the section introduction for how
the two interfaces differ and what recovering the disc statement from this one would take. -/
theorem rouche_symm_nullHomologous {ordf ordg : ℂ → ℤ} (hU : IsOpen U)
    (hfoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hgoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ g z ∧ g z ≠ 0)
    (hfmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hgmero : ∀ s ∈ S, s ∈ U → MeromorphicAt g s)
    (hford : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ordf s : WithTop ℤ))
    (hgord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt g s = (ordg s : WithTop ℤ))
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hγoff : ∀ t ∈ [[a, b]], γ t ∉ (↑S : Set ℂ)) (hnull : Contour.IsNullHomologous γ a b U)
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖) :
    (∑ z ∈ S, Contour.windingNumber γ a b z * (ordf z : ℂ))
      = ∑ z ∈ S, Contour.windingNumber γ a b z * (ordg z : ℂ) := by
  have key := integral_deriv_smul_logDeriv_eq_of_norm_sub_lt hγ hclosed
    (fun t ht => (hfoff _ (hγU t ht) (hγoff t ht)).1)
    (fun t ht => (hgoff _ (hγU t ht) (hγoff t ht)).1) hs
  rw [Contour.argumentPrinciple_nullHomologous hU hfoff hfmero hford hγ hγU hclosed hγoff hnull,
    Contour.argumentPrinciple_nullHomologous hU hgoff hgmero hgord hγ hγU hclosed hγoff
      hnull] at key
  exact mul_left_cancel₀ two_pi_I_ne_zero key

/-- **Rouché's theorem for a null-homologous cycle**, holomorphic form. Let `f` and `g` be analytic
on an open set `U` with all their zeros in a finite set `S`, and let `γ` be a closed piecewise-`C¹`
curve in `U`, null-homologous in `U`, along which `‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖`.
Then `f` and `g` have the same zero count enclosed by `γ`, each zero counted with its multiplicity
and with the winding number of `γ` about it.

The curve is not required to miss `S`: the hypothesis already forces both functions to be zero-free
along it, so it may run through the non-zeros that `S` happens to list. This is the holomorphic
specialization of `TauCeti.rouche_symm_nullHomologous`, with the orders read off by
`analyticOrderNatAt` instead of supplied by the caller. -/
theorem rouche_symm_nullHomologous_of_analyticOnNhd (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfS : ∀ z ∈ U, f z = 0 → z ∈ S) (hgS : ∀ z ∈ U, g z = 0 → z ∈ S)
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hnull : Contour.IsNullHomologous γ a b U)
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖) :
    (∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt f z : ℂ))
      = ∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt g z : ℂ) := by
  have key := integral_deriv_smul_logDeriv_eq_of_norm_sub_lt hγ hclosed
    (fun t ht => hf _ (hγU t ht)) (fun t ht => hg _ (hγU t ht)) hs
  rw [Contour.argumentPrinciple_nullHomologous_of_analyticOnNhd hU hf hfS hγ hγU hclosed
      (fun t ht => ne_zero_left (hs t ht)) hnull,
    Contour.argumentPrinciple_nullHomologous_of_analyticOnNhd hU hg hgS hγ hγU hclosed
      (fun t ht => ne_zero_right (hs t ht)) hnull] at key
  exact mul_left_cancel₀ two_pi_I_ne_zero key

/-- **Rouché's theorem for a null-homologous cycle**, classical form. Under
`‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖` along the curve, `f` and `g` enclose the same winding-weighted
number of zeros. This is the special case of
`TauCeti.rouche_symm_nullHomologous_of_analyticOnNhd` obtained by discarding the nonnegative
summand `‖g (γ t)‖`. -/
theorem rouche_nullHomologous (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfS : ∀ z ∈ U, f z = 0 → z ∈ S) (hgS : ∀ z ∈ U, g z = 0 → z ∈ S)
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hnull : Contour.IsNullHomologous γ a b U)
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖) :
    (∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt f z : ℂ))
      = ∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt g z : ℂ) :=
  rouche_symm_nullHomologous_of_analyticOnNhd hU hf hg hfS hgS hγ hγU hclosed hnull fun t ht =>
    (hs t ht).trans_le (le_add_of_nonneg_right (norm_nonneg _))

/-- **Rouché's theorem for a null-homologous cycle**, additive form: a holomorphic perturbation `g`
dominated by `f` along the curve does not change the winding-weighted number of zeros enclosed.
This is the phrasing of most textbooks, and the one that reads the zeros of a perturbed function
off the unperturbed one. -/
theorem rouche_add_nullHomologous (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hfS : ∀ z ∈ U, f z = 0 → z ∈ S) (hsumS : ∀ z ∈ U, f z + g z = 0 → z ∈ S)
    (hγ : Contour.IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ [[a, b]], γ t ∈ U) (hclosed : γ a = γ b)
    (hnull : Contour.IsNullHomologous γ a b U)
    (hs : ∀ t ∈ [[a, b]], ‖g (γ t)‖ < ‖f (γ t)‖) :
    (∑ z ∈ S, Contour.windingNumber γ a b z * (analyticOrderNatAt f z : ℂ))
      = ∑ z ∈ S, Contour.windingNumber γ a b z *
          (analyticOrderNatAt (fun w => f w + g w) z : ℂ) :=
  rouche_nullHomologous hU hf (hf.add hg) hfS hsumS hγ hγU hclosed hnull fun t ht => by
    simpa using hs t ht

/-- **Rouché's theorem as an equality of image winding numbers, symmetric form** — the "dog on a
leash" statement. If `f` and `g` are analytic along a closed piecewise-`C¹` curve `γ` and never
point in opposite directions there, the image curves `f ∘ γ` and `g ∘ γ` wind equally often about
the origin.

Read through `TauCeti.argumentPrinciple_windingNumber_of_analyticOnNhd`, this is the geometric face
of `TauCeti.rouche_symm_nullHomologous_of_analyticOnNhd`; on its own it is *stronger*, since apart
from analyticity at each point of the curve — `AnalyticAt`, hence on some neighbourhood of that
point — only the behaviour of the two functions **along the curve** enters: no single ambient open
set carrying both, no confinement of the zeros to a finite set, and no null-homology. That is
because the equality of the two logarithmic-derivative integrals is already forced by the
hypothesis: it
puts `g / f` in `Complex.slitPlane`, where `Complex.log` is a single-valued primitive. It is only
in *counting* the winding that those extra hypotheses are needed. -/
theorem rouche_symm_windingNumber_comp (hγ : Contour.IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hfa : ∀ t ∈ [[a, b]], AnalyticAt ℂ f (γ t)) (hga : ∀ t ∈ [[a, b]], AnalyticAt ℂ g (γ t))
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖ + ‖g (γ t)‖) :
    Contour.windingNumber (f ∘ γ) a b 0 = Contour.windingNumber (g ∘ γ) a b 0 := by
  rw [Contour.windingNumber_comp_eq_integral_logDeriv hγ hfa fun t ht => ne_zero_left (hs t ht),
    Contour.windingNumber_comp_eq_integral_logDeriv hγ hga fun t ht => ne_zero_right (hs t ht),
    integral_deriv_smul_logDeriv_eq_of_norm_sub_lt hγ hclosed hfa hga hs]

/-- **Rouché's theorem as an equality of image winding numbers**, classical form. Under
`‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖` along a closed piecewise-`C¹` curve, the image curves `f ∘ γ`
and `g ∘ γ` wind equally often about the origin. This is the special case of
`TauCeti.rouche_symm_windingNumber_comp` obtained by discarding the nonnegative summand
`‖g (γ t)‖`. -/
theorem rouche_windingNumber_comp (hγ : Contour.IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hfa : ∀ t ∈ [[a, b]], AnalyticAt ℂ f (γ t)) (hga : ∀ t ∈ [[a, b]], AnalyticAt ℂ g (γ t))
    (hs : ∀ t ∈ [[a, b]], ‖f (γ t) - g (γ t)‖ < ‖f (γ t)‖) :
    Contour.windingNumber (f ∘ γ) a b 0 = Contour.windingNumber (g ∘ γ) a b 0 :=
  rouche_symm_windingNumber_comp hγ hclosed hfa hga fun t ht =>
    (hs t ht).trans_le (le_add_of_nonneg_right (norm_nonneg _))

/-- **Rouché's theorem as an equality of image winding numbers, additive form.** A holomorphic
perturbation `g` dominated by `f` along a closed piecewise-`C¹` curve does not change how often the
image winds about the origin. This is the phrasing that names the "dog on a leash" picture: the
walker `f ∘ γ` and the dog `(f + g) ∘ γ`, on a leash shorter than the walker's distance from the
lamppost at the origin, circle it the same number of times.

It is the special case of `TauCeti.rouche_windingNumber_comp` for the pair `f`, `f + g`. -/
theorem rouche_add_windingNumber_comp (hγ : Contour.IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hfa : ∀ t ∈ [[a, b]], AnalyticAt ℂ f (γ t)) (hga : ∀ t ∈ [[a, b]], AnalyticAt ℂ g (γ t))
    (hs : ∀ t ∈ [[a, b]], ‖g (γ t)‖ < ‖f (γ t)‖) :
    Contour.windingNumber (f ∘ γ) a b 0
      = Contour.windingNumber ((fun w => f w + g w) ∘ γ) a b 0 :=
  rouche_windingNumber_comp hγ hclosed hfa (fun t ht => (hfa t ht).add (hga t ht)) fun t ht => by
    simpa using hs t ht

end Cycle

end TauCeti
