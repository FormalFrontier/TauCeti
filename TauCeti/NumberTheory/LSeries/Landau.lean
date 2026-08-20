/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.Positivity
public import TauCeti.NumberTheory.LSeries.EntireExtension

/-!
# Landau's theorem on Dirichlet series with nonnegative coefficients

A Dirichlet series whose coefficients are nonnegative real numbers is singular at the real point
of its abscissa of absolute convergence. Writing `σ` for that abscissa, no function analytic on a
disc around `σ` can agree with `LSeries a` immediately to the right of `σ`: the series would then
already converge to the left of `σ`.

The obstruction is recorded by `TauCeti.LSeries.HasAnalyticExtensionAt a σ`, the existence of such
a disc and such a function; `TauCeti.LSeries.hasAnalyticExtensionAt_of_abscissaOfAbsConv_lt` shows
the predicate is not vacuous, since strictly inside the half-plane of convergence the L-series is
its own analytic continuation.

## Main results

* `TauCeti.LSeries.landau`: **Landau's theorem**. If `0 ≤ a` and
  `LSeries.abscissaOfAbsConv a = (σ : EReal)`, then `¬ HasAnalyticExtensionAt a σ`. The equality
  hypothesis is what makes `σ` the *actual* boundary and records its finiteness; convergence
  throughout `Re s > σ` alone would not suffice.
* `TauCeti.LSeries.abscissaOfAbsConv_le_of_differentiableOn`: the half-plane form. A nonnegative
  Dirichlet series with finite abscissa converges as far to the left as it continues analytically.
* `TauCeti.LSeries.abscissaOfAbsConv_eq_bot_of_differentiable`: the entire form, which is what a
  nonvanishing argument applies once a positive combination of L-series has been shown entire.
* `TauCeti.LSeries.abscissaOfAbsConv_eq_bot_of_hasEntireExtension`: the same conclusion phrased
  through the repository's `LSeries.HasEntireExtension` predicate.
* `TauCeti.LSeries.not_hasAnalyticExtensionAt_one`: the coefficient sequence of the Riemann zeta
  function is singular at `s = 1`.

## Implementation notes

Mathlib's `LSeriesSummable` is equivalent to absolute summability of the Dirichlet terms, since
`summable_norm_iff` holds in `ℂ`; consequently `LSeriesSummable.abscissaOfAbsConv_le` already
identifies the ordinary and the absolute abscissa, and no separate lemma is needed here for
nonnegative coefficients.

The proof follows the classical argument. Suppose `F` is analytic on a disc around `σ` and agrees
with `LSeries a` to its right. Patching `F` with `LSeries a` produces a function `G` analytic on a
disc of radius slightly larger than `1` around `σ + 1`, and the Taylor coefficients of `G` at
`σ + 1` are, up to sign, the numbers `∑ a n (log n) ^ k / n ^ (σ + 1) ≥ 0`
(`LSeries.iteratedDeriv_alternating`). Evaluating the Taylor series at a real point `x < σ` of
that disc and exchanging the two nonnegative summations exhibits `∑ a n / n ^ x` as a convergent
series, contradicting `abscissaOfAbsConv a = σ`.

## References

* H. Davenport, *Multiplicative Number Theory*, §11.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.1,
  Theorem 10.
-/

public section

namespace TauCeti.LSeries

open Complex Filter Metric
open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- Iterating `LSeries.logMul` multiplies the Dirichlet term by a power of `Real.log n`. -/
lemma term_logMul_iterate (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    LSeries.term (LSeries.logMul^[k] f) s n = (Real.log n : ℂ) ^ k * LSeries.term f s n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : LSeries.term (LSeries.logMul (LSeries.logMul^[k] f)) s n
        = (Real.log n : ℂ) * LSeries.term (LSeries.logMul^[k] f) s n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.logMul,
          Complex.natCast_log, mul_div_assoc]
    rw [Function.iterate_succ_apply', h1, ih, pow_succ]
    ring

/-- The `k`-th iterated derivative of an L-series, with its alternating sign removed, is the
L-series of `log ^ k * a`. -/
lemma LSeries_logMul_iterate_eq {x : ℝ} (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    LSeries (LSeries.logMul^[k] a) (x : ℂ)
      = (-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) (x : ℂ) := by
  rw [LSeries_iteratedDeriv k (by simpa using hx), ← mul_assoc, ← pow_add,
    Even.neg_one_pow ⟨k, rfl⟩, one_mul]

/-- For nonnegative coefficients the L-series of `log ^ k * a` is a nonnegative real number
throughout the half-plane of absolute convergence. -/
lemma LSeries_logMul_iterate_nonneg (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    0 ≤ LSeries (LSeries.logMul^[k] a) (x : ℂ) :=
  (LSeries_logMul_iterate_eq hx k).symm ▸ LSeries.iteratedDeriv_alternating ha hx k

/-- The real part of a Dirichlet term of a nonnegative coefficient sequence at a real point. -/
lemma re_term_of_ne_zero (ha : 0 ≤ a) (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term a (x : ℂ) n).re = (a n).re / (n : ℝ) ^ x := by
  have hA : a n = ((a n).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact ha n)
  have hcast : (n : ℂ) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [LSeries.term_of_ne_zero hn, hA, hcast, ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.ofReal_re]

/-- The real part of a Dirichlet term of a nonnegative coefficient sequence is nonnegative. -/
lemma re_term_nonneg (ha : 0 ≤ a) (x : ℝ) (n : ℕ) : 0 ≤ (LSeries.term a (x : ℂ) n).re := by
  simpa using (Complex.le_def.mp (LSeries.term_nonneg (ha n) x)).1

/-- For nonnegative coefficients and `x` in the half-plane of absolute convergence, the real
series `∑ (log n) ^ k * a n / n ^ x` converges to the real part of the L-series of
`log ^ k * a`. -/
lemma hasSum_logPow_mul_re_term (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    HasSum (fun n : ℕ ↦ Real.log n ^ k * (LSeries.term a (x : ℂ) n).re)
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)).re := by
  have hsum : LSeriesSummable (LSeries.logMul^[k] a) (x : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa [LSeries.absicssaOfAbsConv_logPowMul] using hx)
  have h : HasSum (LSeries.term (LSeries.logMul^[k] a) (x : ℂ))
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)) := hsum.hasSum
  refine (Complex.hasSum_re h).congr_fun fun n ↦ ?_
  rw [term_logMul_iterate]
  have hre : (LSeries.term a (x : ℂ) n) = ((LSeries.term a (x : ℂ) n).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (by
      rw [Complex.ofReal_zero]; exact LSeries.term_nonneg (ha n) x)
  rw [hre, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact (Complex.ofReal_re _).symm

/-- `HasAnalyticExtensionAt a σ` says that the L-series of `a` continues analytically across the
real point `σ`: some function differentiable on a disc around `σ` agrees with `LSeries a` on the
part of that disc lying in the half-plane `Re s > σ`. -/
def HasAnalyticExtensionAt (a : ℕ → ℂ) (σ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (σ : ℂ) r) ∧
    ∀ s ∈ ball (σ : ℂ) r, σ < s.re → F s = LSeries a s

/-- Above the abscissa of absolute convergence the L-series continues across every real point:
it is already analytic there. -/
lemma hasAnalyticExtensionAt_of_abscissaOfAbsConv_lt {σ : ℝ}
    (h : LSeries.abscissaOfAbsConv a < σ) : HasAnalyticExtensionAt a σ := by
  obtain ⟨σ', h₁, h₂⟩ := EReal.exists_between_coe_real h
  have h₂' : σ' < σ := mod_cast h₂
  refine ⟨σ - σ', by linarith, LSeries a, ?_, fun _ _ _ ↦ rfl⟩
  refine (LSeries_differentiableOn a).mono fun s hs ↦ ?_
  have key : |s.re - σ| ≤ dist s ((σ : ℝ) : ℂ) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (s - ((σ : ℝ) : ℂ))
  rw [mem_ball] at hs
  have hσ' : σ' < s.re := by
    have := (abs_lt.mp (key.trans_lt hs)).1
    linarith
  exact Set.mem_ofPred.mpr (h₁.trans_le (by exact_mod_cast hσ'.le))

/-- **Landau's theorem.** If `a` has nonnegative values and its abscissa of absolute convergence
is the real number `σ`, then `LSeries a` has no analytic continuation across `σ`. -/
theorem landau (ha : 0 ≤ a) {σ : ℝ} (habs : LSeries.abscissaOfAbsConv a = (σ : EReal)) :
    ¬ HasAnalyticExtensionAt a σ := by
  rintro ⟨r, hr, F, hF, hFeq⟩
  set δ : ℝ := min (r ^ 2 / 4) 1 with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδr : 3 * δ < r ^ 2 := by
    have h4 : δ ≤ r ^ 2 / 4 := min_le_left _ _
    nlinarith
  set c : ℝ := σ + 1 with hcdef
  set U : Set ℂ := {s : ℂ | σ < s.re} with hUdef
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have habs_lt : ∀ {s : ℂ}, σ < s.re → LSeries.abscissaOfAbsConv a < s.re := by
    intro s hs
    rw [habs]
    exact_mod_cast hs
  set G : ℂ → ℂ := fun s ↦ if σ < s.re then LSeries a s else F s with hGdef
  have hGU : Set.EqOn G (LSeries a) U := fun s hs ↦ ite_eq_left hs
  have hGF : Set.EqOn G F (ball ((σ : ℝ) : ℂ) r) := by
    intro s hs
    by_cases h : σ < s.re
    · simp only [hGdef]
      rw [ite_eq_left h]
      exact (hFeq s hs h).symm
    · simp only [hGdef]
      exact ite_eq_right h
  -- every point of the disc of radius `1 + δ` around `c` lies in the half-plane or in the
  -- given disc around `σ`
  have hsub : ∀ s ∈ ball ((c : ℝ) : ℂ) (1 + δ), σ < s.re ∨ s ∈ ball ((σ : ℝ) : ℂ) r := by
    intro s hs
    by_cases h : σ < s.re
    · exact Or.inl h
    replace h := not_lt.mp h
    refine Or.inr ?_
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' hr]
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' (by linarith)] at hs
    simp only [Complex.ofReal_re, Complex.ofReal_im, hcdef] at hs ⊢
    nlinarith [sq_nonneg (s.im - 0), sq_nonneg (s.re - σ)]
  have hGdiff : ∀ s ∈ ball ((c : ℝ) : ℂ) (1 + δ), DifferentiableAt ℂ G s := by
    intro s hs
    rcases hsub s hs with h | h
    · have hev : G =ᶠ[nhds s] LSeries a :=
        Filter.eventuallyEq_of_mem (hUopen.mem_nhds h) hGU
      exact hev.differentiableAt_iff.mpr (LSeries_hasDerivAt (habs_lt h)).differentiableAt
    · have hev : G =ᶠ[nhds s] F := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds h) hGF
      exact hev.differentiableAt_iff.mpr (hF.differentiableAt (isOpen_ball.mem_nhds h))
  -- Taylor expansion of `G` at `c`, evaluated at the real point `x = σ - δ / 2`
  set y : ℝ := 1 + δ / 2 with hydef
  set x : ℝ := c - y with hxdef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hxσ : x < σ := by rw [hxdef, hydef, hcdef]; linarith
  have habsc : LSeries.abscissaOfAbsConv a < c := by
    rw [habs]
    exact_mod_cast (by rw [hcdef]; linarith : σ < c)
  have hxball : ((x : ℝ) : ℂ) ∈ ball ((c : ℝ) : ℂ) (1 + δ) := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, hxdef,
      show c - y - c = -y by ring, abs_neg, abs_of_pos hy0, hydef]
    linarith
  have hGdiffOn : DifferentiableOn ℂ G (ball ((c : ℝ) : ℂ) (1 + δ)) :=
    fun s hs ↦ (hGdiff s hs).differentiableWithinAt
  have htaylor := Complex.hasSum_taylorSeries_on_ball hGdiffOn hxball
  have hcU : ((c : ℝ) : ℂ) ∈ U := by
    simp only [hUdef, Set.mem_ofPred_eq, Complex.ofReal_re, hcdef]
    linarith
  have hterm : ∀ k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (((x : ℝ) : ℂ) - ((c : ℝ) : ℂ)) ^ k •
      iteratedDeriv k G ((c : ℝ) : ℂ)
      = ((y ^ k / Nat.factorial k *
          (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) := by
    intro k
    have hd : iteratedDeriv k G ((c : ℝ) : ℂ) = iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ) :=
      hGU.iteratedDeriv_of_isOpen hUopen k hcU
    have hTk : LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)
        = (((LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) :=
      Complex.eq_re_of_ofReal_le (by
        rw [Complex.ofReal_zero]; exact LSeries_logMul_iterate_nonneg ha habsc k)
    have hzc : ((x : ℝ) : ℂ) - ((c : ℝ) : ℂ) = -((y : ℝ) : ℂ) := by
      rw [hxdef]; push_cast; ring
    have e1 : (-((y : ℝ) : ℂ)) ^ k * iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ)
        = ((y : ℝ) : ℂ) ^ k * ((-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ)) := by
      rw [neg_pow]; ring
    rw [hd, hzc, smul_eq_mul, smul_eq_mul, e1, ← LSeries_logMul_iterate_eq habsc k]
    nth_rewrite 1 [hTk]
    push_cast
    ring
  -- the majorant series over `k` converges
  have hsummable_k : Summable (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re) :=
    Complex.summable_ofReal.mp (htaylor.congr_fun fun k ↦ (hterm k).symm).summable
  -- expand each Dirichlet term at `x` as a series in `k`
  have hexp : ∀ n : ℕ, HasSum (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (Real.log n ^ k * (LSeries.term a ((c : ℝ) : ℂ) n).re))
      ((LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    intro n
    have h1 : HasSum (fun k : ℕ ↦ (y * Real.log n) ^ k / Nat.factorial k)
        (Real.exp (y * Real.log n)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp _
    have h2 := h1.mul_right ((LSeries.term a ((c : ℝ) : ℂ) n).re)
    have heq : Real.exp (y * Real.log n) * (LSeries.term a ((c : ℝ) : ℂ) n).re
        = (LSeries.term a ((x : ℝ) : ℂ) n).re := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < n := by positivity
        have hyexp : Real.exp (y * Real.log n) = (n : ℝ) ^ y := by
          rw [Real.rpow_def_of_pos hn0, mul_comm]
        have hc : (n : ℝ) ^ c = (n : ℝ) ^ x * (n : ℝ) ^ y := by
          rw [← Real.rpow_add hn0, hxdef]
          norm_num
        rw [re_term_of_ne_zero ha c hn, re_term_of_ne_zero ha x hn, hyexp, hc]
        field_simp
    rw [← heq]
    refine h2.congr_fun fun k ↦ ?_
    rw [mul_pow]
    ring
  -- hence the L-series converges absolutely at `x < σ`
  have hsum_x : Summable (fun n : ℕ ↦ (LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    refine summable_of_sum_le (c := ∑' k : ℕ, y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re)
      (fun n ↦ re_term_nonneg ha x n) fun s ↦ ?_
    refine hasSum_le (fun k ↦ ?_) (hasSum_sum fun n _ ↦ hexp n) hsummable_k.hasSum
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_
      (div_nonneg (pow_nonneg hy0.le k) (Nat.cast_nonneg _))
    exact sum_le_hasSum s
      (fun n _ ↦ mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) (re_term_nonneg ha c n))
      (hasSum_logPow_mul_re_term ha habsc k)
  have hLS : LSeriesSummable a ((x : ℝ) : ℂ) :=
    (Complex.summable_ofReal.mpr hsum_x).congr fun n ↦
      (Complex.eq_re_of_ofReal_le (by
        rw [Complex.ofReal_zero]; exact LSeries.term_nonneg (ha n) x)).symm
  have hle := hLS.abscissaOfAbsConv_le
  rw [habs, Complex.ofReal_re] at hle
  exact absurd (show σ ≤ x from mod_cast hle) (by linarith)

/-- **Landau's theorem, half-plane form.** A Dirichlet series with nonnegative coefficients and
finite abscissa of absolute convergence converges as far to the left as it continues
analytically: if some function differentiable on `Re s > σ₁` agrees with `LSeries a` on the
half-plane of absolute convergence, then that abscissa is at most `σ₁`.

This is the form consumed by nonvanishing arguments, where `F` is a quotient of L-functions known
to be analytic on a half-plane, or on the complement of a pole that a positive combination has
already cancelled. -/
theorem abscissaOfAbsConv_le_of_differentiableOn (ha : 0 ≤ a)
    (hfin : LSeries.abscissaOfAbsConv a ≠ ⊤) {σ₁ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | σ₁ < s.re})
    (hFeq : ∀ s : ℂ, LSeries.abscissaOfAbsConv a < s.re → F s = LSeries a s) :
    LSeries.abscissaOfAbsConv a ≤ σ₁ := by
  by_contra hcon
  have hlt : (σ₁ : EReal) < LSeries.abscissaOfAbsConv a := not_le.mp hcon
  have hbot : LSeries.abscissaOfAbsConv a ≠ ⊥ := fun h ↦ by simp [h] at hlt
  set σ : ℝ := (LSeries.abscissaOfAbsConv a).toReal with hσdef
  have habs : LSeries.abscissaOfAbsConv a = (σ : EReal) := (EReal.coe_toReal hfin hbot).symm
  have hσ₁σ : σ₁ < σ := by rw [habs] at hlt; exact_mod_cast hlt
  refine landau ha habs ⟨σ - σ₁, by linarith, F, ?_, fun s _ h ↦ hFeq s ?_⟩
  · refine hF.mono fun s hs ↦ ?_
    have key : |s.re - σ| ≤ dist s ((σ : ℝ) : ℂ) := by
      rw [dist_eq_norm]
      simpa using Complex.abs_re_le_norm (s - ((σ : ℝ) : ℂ))
    rw [mem_ball] at hs
    have := (abs_lt.mp (key.trans_lt hs)).1
    exact Set.mem_ofPred.mpr (by linarith)
  · rw [habs]
    exact_mod_cast h

/-- **Landau's theorem, entire form.** If `a` has nonnegative values, its abscissa of absolute
convergence is finite, and `LSeries a` agrees on its half-plane of convergence with an entire
function, then the L-series converges absolutely at every point of the plane.

This is the shape used to rule out a hypothetical zero of an L-function: the zero would cancel a
pole, making a product of L-series entire, and a nonnegative Dirichlet series that is entire must
converge everywhere. -/
theorem abscissaOfAbsConv_eq_bot_of_differentiable (ha : 0 ≤ a)
    (hfin : LSeries.abscissaOfAbsConv a ≠ ⊤) {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, LSeries.abscissaOfAbsConv a < s.re → F s = LSeries a s) :
    LSeries.abscissaOfAbsConv a = ⊥ := by
  have key : ∀ σ₁ : ℝ, LSeries.abscissaOfAbsConv a ≤ (σ₁ : EReal) := fun σ₁ ↦
    abscissaOfAbsConv_le_of_differentiableOn ha hfin hF.differentiableOn hFeq
  refine le_antisymm ?_ bot_le
  by_contra hne
  obtain ⟨r, -, hr⟩ := EReal.exists_between_coe_real (not_le.mp hne)
  exact absurd (key r) (not_le.mpr hr)

/-- A Dirichlet series with nonnegative coefficients that has an entire extension in the sense of
`LSeries.HasEntireExtension` converges absolutely at every point of the plane. -/
theorem abscissaOfAbsConv_eq_bot_of_hasEntireExtension (ha : 0 ≤ a)
    (h : LSeries.HasEntireExtension a) : LSeries.abscissaOfAbsConv a = ⊥ := by
  obtain ⟨F, hF, hFa⟩ := h.exists_extension
  exact abscissaOfAbsConv_eq_bot_of_differentiable ha h.abscissa_lt_top.ne hF fun _ hs ↦ hFa hs

/-- **The Dirichlet series of the Riemann zeta function is singular at `s = 1`.** The constant
sequence `1` has nonnegative values and abscissa of absolute convergence `1`, so Landau's theorem
applies: no function differentiable on a disc around `1` agrees with `LSeries 1` to the right
of `1`. -/
theorem not_hasAnalyticExtensionAt_one : ¬ HasAnalyticExtensionAt (1 : ℕ → ℂ) 1 :=
  landau (fun _ ↦ zero_le_one) (by
    rw [EReal.coe_one]
    exact LSeries.abscissaOfAbsConv_one)

end TauCeti.LSeries
