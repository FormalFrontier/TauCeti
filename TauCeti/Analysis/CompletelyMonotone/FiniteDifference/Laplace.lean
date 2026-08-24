/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Mollify
-- Non-public: Bernstein's theorem supplies the representing measures of the smoothings, its
-- closed-half-line strengthening turns the cluster point back into a statement about `f`, and
-- Prokhorov extracts that cluster point from the tight family.
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight

/-!
# The Hausdorff--Bernstein--Widder theorem in finite-difference form

Bernstein's theorem in the form
`TauCeti.exists_representsLaplace_of_isCompletelyMonotone` takes a completely monotone function,
that is a *smooth* one with alternating iterated derivatives, and produces a finite measure on
`ℝ≥0` whose Laplace transform it is. The hypothesis available in applications is the
finite-difference one of `TauCeti.IsDifferenceCompletelyMonotone`, which carries no smoothness:
what one can check about the mass of a family of measures, or about a function built from
positive-definiteness data, is that its mixed forward differences alternate in sign.

This file closes the gap between the two, in both directions.

Feeding the smoothing of
`TauCeti.IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_between_shift` into Bernstein's
theorem bridges them up to an arbitrarily small shift of the argument: a function on `[0, ∞)`
all of whose mixed forward differences alternate is squeezed, for every `ε > 0`, between
the shift `f (· + ε)` and `f` by the Laplace transform of a finite measure
(`TauCeti.IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift`).

Compactness alone does not remove the shift, because the finite-difference hypothesis says
nothing about the behaviour of `f` at the endpoint: the indicator `f 0 = 1`, `f t = 0` for
`t ≠ 0` has every mixed difference with nonnegative steps of the required sign on `[0, ∞)` —
with all steps positive, the only surviving term of `Δ_{h₁} ⋯ Δ_{hₙ} f` at a point of `[0, ∞)` is
`(-1)ⁿ f 0` at the origin — while no finite positive measure has it as its Laplace transform. With
continuity of `f` on `[0, ∞)` added, however, the approximating measures are uniformly tight (a
Markov bound on the coordinate `p ↦ 1 - e^{-xp}` against the Laplace gap
`f 0 - f x`, which continuity at `0` makes uniformly small), so Prokhorov produces a weak cluster
point, and the squeeze identifies its Laplace transform as `f`.

Right-continuity at `0` is the only continuity assumption needed: taking two equal steps in the
sign condition makes `f` midpoint convex on `[0, ∞)`, while the one-step condition makes it
antitone there. Iterating the midpoint inequality at dyadic points approaching any `t > 0`
therefore squeezes `f` to continuity at `t`.

The converse is a direct computation: for a finite measure `μ` the mixed difference
`Δ_{h₁} ⋯ Δ_{hₙ} (laplaceTransform μ)` at `t` is
`(-1)ⁿ ∫ ∏ᵢ (1 - e^{-hᵢp}) · e^{-tp} ∂μ`, an integral of a nonnegative integrand.

Together the two directions say that on functions continuous on `[0, ∞)` the finite-difference
notion is *equivalent* to the derivative notion of
`TauCeti.IsContinuousCompletelyMonotoneOnIoi` — no smoothness needs to be assumed, only
concluded. `TauCeti.IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi` is the
form in which applications use it, since the derivative predicate is what
`TauCeti.bernsteinMeasure` and `TauCeti.bernsteinMeasureKernel` consume.

## Main declarations

* `TauCeti.IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift`:
  the approximate Laplace representation of a finite-difference completely monotone function.
* `TauCeti.isDifferenceCompletelyMonotone_laplaceTransform` and
  `TauCeti.RepresentsLaplace.isDifferenceCompletelyMonotone`: the easy direction, that a Laplace
  transform of a finite measure has alternating mixed differences.
* `TauCeti.exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt`:
  **the representation theorem**, that a function right-continuous at zero with alternating mixed
  differences is the Laplace transform of a finite measure.
* `TauCeti.hausdorff_bernstein_widder_difference`: the resulting characterization of the
  Laplace transforms of finite measures on `ℝ≥0`.
* `TauCeti.isContinuousCompletelyMonotoneOnIoi_iff_isDifferenceCompletelyMonotone_and_continuousOn`
  and
  `TauCeti.IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi`: the two notions
  of complete monotonicity agree on functions continuous on `[0, ∞)`.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984).

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone) and Part C, Milestone 2 (BCR semigroup--Bochner).
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Approximate representation from the finite-difference hypothesis -/

/-- **Approximate Bernstein representation.** A function that is completely monotone in the
finite-difference sense is squeezed, for every `ε > 0`, between
`f (· + ε)` and `f` by the Laplace transform of a finite positive measure on `ℝ≥0`.

A Bernstein representation of `f` itself does not follow from these measures by compactness
alone: the hypothesis leaves the value at the endpoint free, so it needs right-continuity of `f`
at `0`, which is what
`TauCeti.exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt`
adds. -/
theorem IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift
    (hf : IsDifferenceCompletelyMonotone f) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t →
      f (t + ε) ≤ laplaceTransform μ t ∧ laplaceTransform μ t ≤ f t := by
  obtain ⟨g, hg, hgle⟩ := hf.exists_isCompletelyMonotone_between_shift hε
  obtain ⟨μ, hμ⟩ := exists_representsLaplace_of_isCompletelyMonotone hg
  refine ⟨μ, hμ.isFiniteMeasure, fun t ht => ?_⟩
  rw [← hμ.eq_laplaceTransform ht]
  exact hgle t ht

/-! ## The easy direction: Laplace transforms have alternating mixed differences -/

/-- The integrand computing a mixed forward difference of a Laplace transform: the product of the
factors `1 - e^{-hp}` over the list `l` of steps, against the Laplace kernel `e^{-tp}`. -/
private noncomputable def laplaceDiffIntegrand (l : List ℝ) (t : ℝ) (p : ℝ≥0) : ℝ :=
  (l.map fun h => 1 - Real.exp (-(h * (p : ℝ)))).prod * Real.exp (-(t * (p : ℝ)))

private lemma laplaceDiffIntegrand_nil (t : ℝ) (p : ℝ≥0) :
    laplaceDiffIntegrand [] t p = Real.exp (-(t * (p : ℝ))) := by
  simp [laplaceDiffIntegrand]

private lemma laplaceDiffIntegrand_cons (a : ℝ) (l : List ℝ) (t : ℝ) (p : ℝ≥0) :
    laplaceDiffIntegrand (a :: l) t p
      = (1 - Real.exp (-(a * (p : ℝ)))) * laplaceDiffIntegrand l t p := by
  simp [laplaceDiffIntegrand, mul_assoc]

/-- Advancing the Laplace parameter by `a` multiplies the integrand by `e^{-ap}`; this is what
turns a forward difference in `t` into one more factor of the product. -/
private lemma laplaceDiffIntegrand_add (l : List ℝ) (t a : ℝ) (p : ℝ≥0) :
    laplaceDiffIntegrand l (t + a) p
      = Real.exp (-(a * (p : ℝ))) * laplaceDiffIntegrand l t p := by
  simp only [laplaceDiffIntegrand]
  have hsplit : -((t + a) * (p : ℝ)) = -(a * (p : ℝ)) + -(t * (p : ℝ)) := by ring
  rw [hsplit, Real.exp_add]
  ring

/-- Each factor of the integrand lies in `[0, 1]`, hence so does the integrand. -/
private lemma laplaceDiffIntegrand_mem_Icc : ∀ (l : List ℝ), (∀ h ∈ l, 0 ≤ h) →
    ∀ (t : ℝ), 0 ≤ t → ∀ p : ℝ≥0, laplaceDiffIntegrand l t p ∈ Icc (0 : ℝ) 1 := by
  intro l
  induction l with
  | nil =>
      intro _ t ht p
      rw [laplaceDiffIntegrand_nil]
      exact ⟨(Real.exp_pos _).le, exp_neg_mul_le_one ht p⟩
  | cons a l ih =>
      intro hl t ht p
      have ha : 0 ≤ a := hl a (by simp)
      obtain ⟨h0, h1⟩ := ih (fun h hh => hl h (by simp [hh])) t ht p
      have hfac0 : 0 ≤ 1 - Real.exp (-(a * (p : ℝ))) :=
        sub_nonneg.mpr (exp_neg_mul_le_one ha p)
      have hfac1 : 1 - Real.exp (-(a * (p : ℝ))) ≤ 1 := by
        have := (Real.exp_pos (-(a * (p : ℝ)))).le
        linarith
      rw [laplaceDiffIntegrand_cons]
      exact ⟨mul_nonneg hfac0 h0, by simpa using mul_le_mul hfac1 h1 h0 zero_le_one⟩

private lemma continuous_laplaceDiffIntegrand (l : List ℝ) (t : ℝ) :
    Continuous (laplaceDiffIntegrand l t) := by
  induction l with
  | nil =>
      have hfun : laplaceDiffIntegrand ([] : List ℝ) t
          = fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ))) := funext (laplaceDiffIntegrand_nil t)
      rw [hfun]
      exact continuous_exp_neg_mul t
  | cons a l ih =>
      have hfun : laplaceDiffIntegrand (a :: l) t
          = fun p : ℝ≥0 => (1 - Real.exp (-(a * (p : ℝ)))) * laplaceDiffIntegrand l t p :=
        funext (laplaceDiffIntegrand_cons a l t)
      rw [hfun]
      exact (continuous_const.sub (continuous_exp_neg_mul a)).mul ih

private lemma integrable_laplaceDiffIntegrand (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {l : List ℝ}
    (hl : ∀ h ∈ l, 0 ≤ h) {t : ℝ} (ht : 0 ≤ t) : Integrable (laplaceDiffIntegrand l t) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (continuous_laplaceDiffIntegrand l t).aestronglyMeasurable (.of_forall fun p => ?_)
  obtain ⟨h0, h1⟩ := laplaceDiffIntegrand_mem_Icc l hl t ht p
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

/-- **A mixed forward difference of a Laplace transform is an integral.** Differencing with the
step `h` multiplies the integrand by `e^{-hp} - 1`, so a mixed difference along `l` accumulates
the product of those factors; pulling out the sign leaves the nonnegative integrand
`∏ᵢ (1 - e^{-hᵢp}) · e^{-tp}`. -/
private lemma fwdDiffList_laplaceTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ∀ (l : List ℝ), (∀ h ∈ l, 0 ≤ h) → ∀ (t : ℝ), 0 ≤ t →
      fwdDiffList l (laplaceTransform μ) t
        = (-1) ^ l.length * ∫ p, laplaceDiffIntegrand l t p ∂μ := by
  intro l
  induction l with
  | nil =>
      intro _ t _
      simp only [fwdDiffList_nil, List.length_nil, pow_zero, one_mul]
      simp_rw [laplaceDiffIntegrand_nil]
      exact laplaceTransform_apply μ t
  | cons a l ih =>
      intro hl t ht
      have ha : 0 ≤ a := hl a (by simp)
      have hl' : ∀ h ∈ l, 0 ≤ h := fun h hh => hl h (by simp [hh])
      have hta : (0 : ℝ) ≤ t + a := by linarith
      have hpt : ∀ p : ℝ≥0, laplaceDiffIntegrand l (t + a) p - laplaceDiffIntegrand l t p
          = -laplaceDiffIntegrand (a :: l) t p := by
        intro p
        rw [laplaceDiffIntegrand_add, laplaceDiffIntegrand_cons]
        ring
      rw [fwdDiffList_cons, fwdDiff, ih hl' (t + a) hta, ih hl' t ht, ← mul_sub,
        ← integral_sub (integrable_laplaceDiffIntegrand μ hl' hta)
          (integrable_laplaceDiffIntegrand μ hl' ht)]
      simp_rw [hpt]
      rw [integral_neg, List.length_cons, pow_succ]
      ring

/-- **The Laplace transform of a finite measure is completely monotone in the finite-difference
sense.** Every mixed forward difference with nonnegative steps has the sign `(-1)ⁿ`, because it
is `(-1)ⁿ` times the integral of a nonnegative function. -/
theorem isDifferenceCompletelyMonotone_laplaceTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    IsDifferenceCompletelyMonotone (laplaceTransform μ) := by
  refine isDifferenceCompletelyMonotone_iff.2 fun l hl t ht => ?_
  rw [fwdDiffList_laplaceTransform μ l hl t ht, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul]
  exact integral_nonneg fun p => (laplaceDiffIntegrand_mem_Icc l hl t ht p).1

/-- A function represented by a finite measure through its Laplace transform is completely
monotone in the finite-difference sense. -/
theorem RepresentsLaplace.isDifferenceCompletelyMonotone {μ : Measure ℝ≥0}
    (h : RepresentsLaplace μ f) : IsDifferenceCompletelyMonotone f := by
  have := h.isFiniteMeasure
  exact (isDifferenceCompletelyMonotone_laplaceTransform μ).congr fun t ht =>
    h.eq_laplaceTransform ht

/-- A finite-difference completely monotone function is automatically continuous away from the
endpoint. The equal-step second-difference inequality gives the midpoint bound used below, while
antitonicity turns its dyadic estimates into a two-sided squeeze. -/
private lemma IsDifferenceCompletelyMonotone.continuousAt_of_pos
    (hf : IsDifferenceCompletelyMonotone f) {x : ℝ} (hx : 0 < x) : ContinuousAt f x := by
  have hmidpoint : ∀ {a h : ℝ}, 0 ≤ a → 0 ≤ h →
      2 * f (a + h) ≤ f a + f (a + 2 * h) := by
    intro a h ha hh
    have hdiff := isDifferenceCompletelyMonotone_iff.mp hf [h, h] (by simpa using hh) a ha
    simp only [List.length_cons, List.length_nil, fwdDiffList_cons, fwdDiffList_nil, fwdDiff,
      zero_add, pow_succ, pow_zero] at hdiff
    have hadd : a + h + h = a + 2 * h := by ring
    rw [hadd] at hdiff
    norm_num at hdiff
    linarith
  have hdyadic : ∀ n : ℕ,
      f ((1 - (1 / 2 : ℝ) ^ n) * x) ≤
        (1 / 2 : ℝ) ^ n * f 0 + (1 - (1 / 2 : ℝ) ^ n) * f x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hc_nonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
        have hc_le_one : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have hstep := hmidpoint (a := (1 - (1 / 2 : ℝ) ^ n) * x)
          (h := (1 / 2 : ℝ) ^ n * x / 2) (by positivity) (by positivity)
        have hhalf : (1 - (1 / 2 : ℝ) ^ n) * x + (1 / 2 : ℝ) ^ n * x / 2 =
            (1 - (1 / 2 : ℝ) ^ n / 2) * x := by ring
        have hend : (1 - (1 / 2 : ℝ) ^ n) * x +
            2 * ((1 / 2 : ℝ) ^ n * x / 2) = x := by ring
        rw [hhalf, hend] at hstep
        have hpoint : (1 - (1 / 2 : ℝ) ^ n / 2) * x =
            (1 - (1 / 2 : ℝ) ^ n * (1 / 2)) * x := by ring
        rw [hpoint] at hstep
        rw [pow_succ]
        calc
          f ((1 - (1 / 2 : ℝ) ^ n * (1 / 2)) * x)
              ≤ (f ((1 - (1 / 2 : ℝ) ^ n) * x) + f x) / 2 := by
                nlinarith
          _ ≤ ((1 / 2 : ℝ) ^ n * f 0 + (1 - (1 / 2 : ℝ) ^ n) * f x + f x) / 2 :=
            by linarith
          _ = (1 / 2 : ℝ) ^ n * (1 / 2) * f 0 +
              (1 - (1 / 2 : ℝ) ^ n * (1 / 2)) * f x := by ring
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n * (f 0 - f x)) atTop (𝓝 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa using hbase.mul_const (f 0 - f x)
  obtain ⟨n, hn, hsmall⟩ :=
    ((eventually_ge_atTop 1).and (hpow.eventually (eventually_lt_nhds hε))).exists
  let c : ℝ := (1 / 2 : ℝ) ^ n
  have hc_pos : 0 < c := by positivity
  have hc_lt_one : c < 1 := by
    dsimp [c]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_of_gt hn)
  refine ⟨c * x, mul_pos hc_pos hx, ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy ⊢
  have hy_bounds : (1 - c) * x < y ∧ y < (1 + c) * x := by
    constructor <;> nlinarith [abs_lt.mp hy]
  have hq_nonneg : 0 ≤ (1 - c) * x := mul_nonneg (sub_nonneg.mpr hc_lt_one.le) hx.le
  have hy_nonneg : 0 ≤ y := hq_nonneg.trans hy_bounds.1.le
  have hr_nonneg : 0 ≤ (1 + c) * x := by positivity
  have hq : f ((1 - c) * x) ≤ c * f 0 + (1 - c) * f x := by
    simpa only [c] using hdyadic n
  have hy_upper : f y < f x + ε := by
    have := hf.antitoneOn (mem_Ici.2 hq_nonneg) (mem_Ici.2 hy_nonneg) hy_bounds.1.le
    nlinarith
  have hcenter := hmidpoint (a := (1 - c) * x) (h := c * x)
    hq_nonneg (mul_nonneg hc_pos.le hx.le)
  have hcenter_left : (1 - c) * x + c * x = x := by ring
  have hcenter_right : (1 - c) * x + 2 * (c * x) = (1 + c) * x := by ring
  rw [hcenter_left, hcenter_right] at hcenter
  have hy_lower : f x - ε < f y := by
    have := hf.antitoneOn (mem_Ici.2 hy_nonneg) (mem_Ici.2 hr_nonneg) hy_bounds.2.le
    nlinarith
  exact abs_lt.2 ⟨by linarith, by linarith⟩

/-! ## Tightness of the approximating measures -/

/-- **The approximating measures of a continuous finite-difference completely monotone function
are uniformly tight.** The mass a member of the family puts outside a large ball is bounded, by
`TauCeti.measure_compl_closedBall_le_of_laplaceTransform`, by its Laplace gap
`μ.real univ - laplaceTransform μ x`, and the squeeze bounds that gap by `f 0 - f (x + aₙ)`.
Choosing `x` so small that `f` has barely dropped by `2x` makes the estimate uniform over all
shifts `aₙ ≤ x`; the finitely many larger shifts are handled by
`TauCeti.isTightMeasureSet_range_finite`. -/
private lemma isTightMeasureSet_range_of_laplaceTransform_between_shift
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0)
    {a : ℕ → ℝ} (ha_pos : ∀ n, 0 < a n) (ha : Tendsto a atTop (𝓝 0))
    {μ : ℕ → Measure ℝ≥0} (hfin : ∀ n, IsFiniteMeasure (μ n))
    (hlow : ∀ n, ∀ t : ℝ, 0 ≤ t → f (t + a n) ≤ laplaceTransform (μ n) t)
    (hhigh : ∀ n, ∀ t : ℝ, 0 ≤ t → laplaceTransform (μ n) t ≤ f t) :
    IsTightMeasureSet (range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ∞
  · exact ⟨∅, isCompact_empty, fun ν _ => by simp [hε_top]⟩
  have hε_pos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hε_top
  have hc_pos : 0 < 1 - Real.exp (-1 : ℝ) := by
    have : Real.exp (-1 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  -- A point `y > 0` at which `f` has dropped from `f 0` by less than `ε.toReal * (1 - e⁻¹)`.
  have hcw : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    hcont.tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hdrop : f 0 - ε.toReal * (1 - Real.exp (-1 : ℝ)) < f 0 := by nlinarith
  obtain ⟨y, hy, hy_pos⟩ :=
    ((hcw.eventually (eventually_gt_nhds hdrop)).and self_mem_nhdsWithin).exists
  -- The Markov parameter is `y / 2` and the radius its inverse, so that their product is `1`.
  have hx_pos : 0 < y / 2 := by linarith
  have hR_pos : 0 < (y / 2)⁻¹ := inv_pos.mpr hx_pos
  have hden : 1 - Real.exp (-(y / 2 * (y / 2)⁻¹)) = 1 - Real.exp (-1 : ℝ) := by
    rw [mul_inv_cancel₀ hx_pos.ne']
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ha.eventually (eventually_lt_nhds hx_pos))
  -- The finitely many shifts larger than `x` are tight on their own.
  obtain ⟨K, hK_compact, hK_tail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_range_finite (fun n : {n : ℕ // n < N} => μ n) fun n => hfin n) ε hε
  refine ⟨K ∪ Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹,
    hK_compact.union (isCompact_closedBall _ _), ?_⟩
  rintro ν ⟨n, rfl⟩
  by_cases hn : n < N
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans
      (hK_tail (μ n) ⟨⟨n, hn⟩, rfl⟩)
  -- Beyond the threshold the Markov bound applies with a uniform numerator.
  have hnN : N ≤ n := le_of_not_gt hn
  have hfin_n := hfin n
  have hmass : (μ n).real univ ≤ f 0 := by
    simpa [laplaceTransform_zero] using hhigh n 0 le_rfl
  have han : a n < y / 2 := hN n hnN
  have han_pos : 0 < a n := ha_pos n
  have hgap : f y ≤ laplaceTransform (μ n) (y / 2) :=
    le_trans (hf.antitoneOn (mem_Ici.2 (by linarith)) (mem_Ici.2 hy_pos.le) (by linarith))
      (hlow n (y / 2) hx_pos.le)
  have hnum : (μ n).real univ - laplaceTransform (μ n) (y / 2)
      ≤ ε.toReal * (1 - Real.exp (-1 : ℝ)) := by linarith
  calc
    μ n (K ∪ Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹)ᶜ
        ≤ μ n (Metric.closedBall (0 : ℝ≥0) (y / 2)⁻¹)ᶜ :=
      measure_mono (compl_subset_compl.mpr subset_union_right)
    _ ≤ ENNReal.ofReal (((μ n).real univ - laplaceTransform (μ n) (y / 2))
          / (1 - Real.exp (-(y / 2 * (y / 2)⁻¹)))) :=
      measure_compl_closedBall_le_of_laplaceTransform (μ n) hx_pos hR_pos
    _ ≤ ENNReal.ofReal ε.toReal := by
      rw [hden]
      exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hc_pos).2 hnum)
    _ ≤ ε := ENNReal.ofReal_le_of_le_toReal le_rfl

/-! ## The representation theorem -/

/-- **The existence half of the Hausdorff--Bernstein--Widder theorem in finite-difference form.**
A function right-continuous at zero all of whose mixed forward differences with nonnegative steps
have the sign `(-1)ⁿ` is the Laplace transform of a finite positive measure on `ℝ≥0`.

The smoothings of `f` at the shifts `aₙ = 1/(n+1)` have representing measures squeezing `f`
between `f (· + aₙ)` and `f`; they are uniformly bounded in mass by `f 0` and uniformly tight, so
Prokhorov supplies a weak cluster point `μ₀`. Continuity of `f` closes the squeeze: the Laplace
transform of `μ₀` at `t` is at most `f t`, and at least `f s` for every `s > t`. -/
theorem exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  classical
  have hcontOn : ContinuousOn f (Ici 0) := by
    intro t ht
    rcases (mem_Ici.mp ht).eq_or_lt with rfl | ht
    · exact hcont
    · exact (hf.continuousAt_of_pos ht).continuousWithinAt
  -- Stage 1: the positive null sequence of shifts and the approximating measures.
  have ha_pos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ha : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  choose μ hfin hbetween using fun n : ℕ =>
    hf.exists_isFiniteMeasure_laplaceTransform_between_shift (ha_pos n)
  have hlow : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → f (t + 1 / ((n : ℝ) + 1)) ≤ laplaceTransform (μ n) t :=
    fun n t ht => (hbetween n t ht).1
  have hhigh : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → laplaceTransform (μ n) t ≤ f t :=
    fun n t ht => (hbetween n t ht).2
  -- Stage 2: the uniform mass bound and tightness feed Prokhorov.
  have hmass : ∀ n : ℕ, (μ n) univ ≤ (((f 0).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    intro n
    have := hfin n
    have hle : (μ n).real univ ≤ f 0 := by
      simpa [laplaceTransform_zero] using hhigh n 0 le_rfl
    calc (μ n) univ = ENNReal.ofReal ((μ n).real univ) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (f 0) := ENNReal.ofReal_le_ofReal hle
      _ = (((f 0).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  obtain ⟨μ₀, U, hUle, hμ₀_fin, -, hweak⟩ :=
    finite_measure_cluster_limit μ (f 0).toNNReal hmass
      (isTightMeasureSet_range_of_laplaceTransform_between_shift hf hcont ha_pos ha hfin
        hlow hhigh)
  -- Stage 3: the squeeze identifies the Laplace transform of the cluster point as `f`.
  refine ⟨μ₀, representsLaplace_iff.mpr ⟨hμ₀_fin, fun t ht => ?_⟩⟩
  have hL : Tendsto (fun n => laplaceTransform (μ n) t) (U : Filter ℕ)
      (𝓝 (laplaceTransform μ₀ t)) := by
    have hw := hweak (laplaceKernelBoundedContinuous ht)
    simp only [laplaceKernelBoundedContinuous_apply] at hw
    simpa only [laplaceTransform_apply] using hw
  have hupper : laplaceTransform μ₀ t ≤ f t :=
    le_of_tendsto hL (.of_forall fun n => hhigh n t ht)
  have hlower : ∀ s : ℝ, t < s → f s ≤ laplaceTransform μ₀ t := by
    intro s hs
    refine ge_of_tendsto hL (Eventually.filter_mono hUle ?_)
    filter_upwards [ha.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < s - t))] with n hn
    refine le_trans (hf.antitoneOn (mem_Ici.2 (by positivity)) (mem_Ici.2 (by linarith))
      (by linarith)) (hlow n t ht)
  have hcw : Tendsto f (𝓝[>] t) (𝓝 (f t)) :=
    (hcontOn.continuousWithinAt (mem_Ici.2 ht)).tendsto.mono_left
      (nhdsWithin_mono t fun s hs => mem_Ici.2 (ht.trans (le_of_lt hs)))
  have hft : f t ≤ laplaceTransform μ₀ t :=
    le_of_tendsto hcw (eventually_mem_nhdsWithin.mono fun s hs => hlower s hs)
  exact le_antisymm hft hupper

/-- A continuous finite-difference completely monotone function is the Laplace transform of a
finite positive measure. This is the continuous-on corollary of the endpoint-continuity theorem. -/
theorem exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousOn
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousOn f (Ici 0)) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f :=
  exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf
    (hcont.continuousWithinAt (mem_Ici.2 le_rfl))

/-- **The Hausdorff--Bernstein--Widder theorem in finite-difference form.** A function has
alternating mixed forward differences and is right-continuous at zero if and only if it is the
Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem hausdorff_bernstein_widder_difference (f : ℝ → ℝ) :
    (IsDifferenceCompletelyMonotone f ∧ ContinuousWithinAt f (Ici 0) 0)
      ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  refine ⟨fun ⟨hf, hcont⟩ =>
      exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf hcont,
    fun ⟨μ, hμ⟩ =>
      ⟨hμ.isDifferenceCompletelyMonotone,
        hμ.isContinuousCompletelyMonotoneOnIoi.continuousOn.continuousWithinAt
          (mem_Ici.2 le_rfl)⟩⟩

/-- **The two notions of complete monotonicity agree on continuous functions.** For a function
continuous on `[0, ∞)`, complete monotonicity in the derivative sense on `(0, ∞)` is equivalent
to the sign condition on all mixed forward differences, which mentions no derivatives at all.
Compare `TauCeti.isCompletelyMonotone_iff_isDifferenceCompletelyMonotone`, which assumes
smoothness; here smoothness is a conclusion. -/
theorem isContinuousCompletelyMonotoneOnIoi_iff_isDifferenceCompletelyMonotone_and_continuousOn
    (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f
      ↔ IsDifferenceCompletelyMonotone f ∧ ContinuousOn f (Ici 0) := by
  rw [hausdorff_bernstein_widder f]
  refine ⟨fun ⟨μ, hμ⟩ =>
      ⟨hμ.isDifferenceCompletelyMonotone, hμ.isContinuousCompletelyMonotoneOnIoi.continuousOn⟩,
    fun ⟨hf, hcont⟩ =>
      exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousOn hf hcont⟩

/-- **From finite differences to derivatives.** This is the form in which applications use the
equivalence: the Bernstein measure and the Bernstein kernel take
`TauCeti.IsContinuousCompletelyMonotoneOnIoi` as their hypothesis, while what is checkable in
practice is the finite-difference condition. -/
theorem IsDifferenceCompletelyMonotone.isContinuousCompletelyMonotoneOnIoi
    (hf : IsDifferenceCompletelyMonotone f) (hcont : ContinuousWithinAt f (Ici 0) 0) :
    IsContinuousCompletelyMonotoneOnIoi f := by
  obtain ⟨μ, hμ⟩ :=
    exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt hf hcont
  exact hμ.isContinuousCompletelyMonotoneOnIoi

end TauCeti

end
