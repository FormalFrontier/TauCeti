/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.NumberTheory.LSeries.Deriv
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
* `TauCeti.LSeries.abscissaOfAbsConv_eq_bot_of_hasEntireExtension`: the same conclusion phrased
  through the repository's `LSeries.HasEntireExtension` predicate, which is what a nonvanishing
  argument applies once a positive combination of L-series has been shown entire.

## Implementation notes

Mathlib formalizes only the abscissa of absolute convergence: `LSeriesSummable` is equivalent to
absolute summability of the Dirichlet terms because `summable_norm_iff` holds in `ℂ`. It does not
define the classical abscissa of conditional convergence, so the ordinary/absolute distinction
does not arise in this development and no equality between those abscissae is proved here.

The proof follows the classical argument. Suppose `F` is analytic on a disc around `σ` and agrees
with `LSeries a` to its right. Patching `F` with `LSeries a` produces a function `G` analytic on a
disc of radius slightly larger than `1` around `σ + 1`, and the Taylor coefficients of `G` at
`σ + 1` are, up to sign, the numbers `∑ a n (log n) ^ k / n ^ (σ + 1) ≥ 0`
(`LSeries.iteratedDeriv_alternating`). Evaluating the Taylor series at a real point `x < σ` of
that disc and exchanging the two nonnegative summations exhibits `∑ a n / n ^ x` as a convergent
series, contradicting `abscissaOfAbsConv a = σ`.

## References

* [G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*][tenenbaum1995],
  Chapter II.1, Theorem 10.
-/

public section

namespace TauCeti.LSeries

open Complex Filter Metric
open scoped ComplexOrder

variable {a : ℕ → ℂ}

/-- Applying Mathlib's `logPowMul` operation multiplies the Dirichlet term by a power of
`Real.log n`. -/
lemma term_logPowMul (f : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
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

private lemma logPowMul_eq_alternating {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv a < s.re) (k : ℕ) :
    LSeries (LSeries.logMul^[k] a) s = (-1 : ℂ) ^ k * iteratedDeriv k (LSeries a) s := by
  rw [LSeries_iteratedDeriv k hs, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨k, rfl⟩, one_mul]

private lemma logPowMul_nonneg (ha : 0 ≤ a) {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    0 ≤ LSeries (LSeries.logMul^[k] a) (x : ℂ) :=
  (logPowMul_eq_alternating (s := (x : ℂ)) (by simpa using hx) k).symm ▸
    LSeries.iteratedDeriv_alternating ha hx k

/-- The real part of a Dirichlet term at a real point. -/
lemma re_term_of_ne_zero (a : ℕ → ℂ) (x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.term a (x : ℂ) n).re = (a n).re / (n : ℝ) ^ x := by
  have hcast : (n : ℂ) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  rw [LSeries.term_of_ne_zero hn, hcast, Complex.div_ofReal_re]

/-- At a real point `x` in the half-plane of absolute convergence, the real series obtained by
taking real parts of the terms of `logPowMul` converges to the real part of its L-series. -/
lemma hasSum_logPowMul_re_term {x : ℝ}
    (hx : LSeries.abscissaOfAbsConv a < x) (k : ℕ) :
    HasSum (fun n : ℕ ↦ Real.log n ^ k * (LSeries.term a (x : ℂ) n).re)
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)).re := by
  have hsum : LSeriesSummable (LSeries.logMul^[k] a) (x : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by
      simpa [LSeries.absicssaOfAbsConv_logPowMul] using hx)
  have h : HasSum (LSeries.term (LSeries.logMul^[k] a) (x : ℂ))
      (LSeries (LSeries.logMul^[k] a) (x : ℂ)) := hsum.hasSum
  refine (Complex.hasSum_re h).congr_fun fun n ↦ ?_
  rw [term_logPowMul, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

private lemma re_term_nonneg (ha : 0 ≤ a) (x : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term a (x : ℂ) n).re := by
  simpa using (Complex.le_def.mp (LSeries.term_nonneg (ha n) x)).1

private lemma term_eq_ofReal_re (ha : 0 ≤ a) (x : ℝ) (n : ℕ) :
    LSeries.term a (x : ℂ) n = ((LSeries.term a (x : ℂ) n).re : ℂ) :=
  Complex.eq_re_of_ofReal_le (by
    rw [Complex.ofReal_zero]
    exact LSeries.term_nonneg (ha n) x)

/-- `HasAnalyticExtensionAt a σ` says that the L-series of `a` continues analytically across the
real point `σ`: some function differentiable on a disc around `σ` agrees with `LSeries a` on the
part of that disc lying in the half-plane `Re s > σ`. -/
def HasAnalyticExtensionAt (a : ℕ → ℂ) (σ : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (σ : ℂ) r) ∧
    ∀ s ∈ ball (σ : ℂ) r, σ < s.re → F s = LSeries a s

private lemma sub_lt_re_of_mem_ball {σ r : ℝ} {s : ℂ}
    (hs : s ∈ ball ((σ : ℝ) : ℂ) r) : σ - r < s.re := by
  have key : |s.re - σ| ≤ dist s ((σ : ℝ) : ℂ) := by
    rw [dist_eq_norm]
    simpa using Complex.abs_re_le_norm (s - ((σ : ℝ) : ℂ))
  rw [mem_ball] at hs
  have := (abs_lt.mp (key.trans_lt hs)).1
  linarith

/-- Above the abscissa of absolute convergence the L-series continues across every real point:
it is already analytic there. -/
lemma hasAnalyticExtensionAt_of_abscissaOfAbsConv_lt {σ : ℝ}
    (h : LSeries.abscissaOfAbsConv a < σ) : HasAnalyticExtensionAt a σ := by
  obtain ⟨σ', h₁, h₂⟩ := EReal.exists_between_coe_real h
  have h₂' : σ' < σ := mod_cast h₂
  refine ⟨σ - σ', by linarith, LSeries a, ?_, fun _ _ _ ↦ rfl⟩
  refine (LSeries_differentiableOn a).mono fun s hs ↦ ?_
  have hσ' : σ' < s.re := by
    have := sub_lt_re_of_mem_ball hs
    linarith
  exact Set.mem_ofPred.mpr (h₁.trans_le (by exact_mod_cast hσ'.le))

private lemma exists_differentiableOn_patch {σ : ℝ}
    (habs : LSeries.abscissaOfAbsConv a = (σ : EReal)) (h : HasAnalyticExtensionAt a σ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G (ball (((σ + 1 : ℝ) : ℂ)) (1 + δ)) ∧
        Set.EqOn G (LSeries a) {s : ℂ | σ < s.re} := by
  obtain ⟨r, hr, F, hF, hFeq⟩ := h
  set δ : ℝ := min (r ^ 2 / 4) 1 with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδr : 3 * δ < r ^ 2 := by
    have h4 : δ ≤ r ^ 2 / 4 := min_le_left _ _
    nlinarith
  have hUopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have habs_lt : ∀ {s : ℂ}, σ < s.re → LSeries.abscissaOfAbsConv a < s.re := by
    intro s hs
    rw [habs]
    exact_mod_cast hs
  set G : ℂ → ℂ := fun s ↦ if σ < s.re then LSeries a s else F s with hGdef
  have hGU : Set.EqOn G (LSeries a) {s : ℂ | σ < s.re} := fun s hs ↦
    ite_eq_left (Set.mem_ofPred.mp hs)
  have hGF : Set.EqOn G F (ball ((σ : ℝ) : ℂ) r) := by
    intro s hs
    by_cases hsσ : σ < s.re
    · simpa [hGdef, hsσ] using (hFeq s hs hsσ).symm
    · simp [hGdef, hsσ]
  have hsub : ∀ s ∈ ball (((σ + 1 : ℝ) : ℂ)) (1 + δ),
      σ < s.re ∨ s ∈ ball ((σ : ℝ) : ℂ) r := by
    intro s hs
    by_cases hsσ : σ < s.re
    · exact Or.inl hsσ
    replace hsσ := not_lt.mp hsσ
    refine Or.inr ?_
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' hr]
    rw [mem_ball, Complex.dist_eq_re_im, Real.sqrt_lt' (by linarith)] at hs
    simp only [Complex.ofReal_re, Complex.ofReal_im] at hs ⊢
    nlinarith [sq_nonneg (s.im - 0), sq_nonneg (s.re - σ)]
  refine ⟨δ, hδpos, G, fun s hs ↦ ?_, hGU⟩
  rcases hsub s hs with hsU | hsF
  · have hev : G =ᶠ[nhds s] LSeries a := Filter.eventuallyEq_of_mem
      (hUopen.mem_nhds (Set.mem_ofPred.mpr hsU)) hGU
    exact (hev.differentiableAt_iff.mpr
      (LSeries_hasDerivAt (habs_lt hsU)).differentiableAt).differentiableWithinAt
  · have hev : G =ᶠ[nhds s] F :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hsF) hGF
    exact (hev.differentiableAt_iff.mpr
      (hF.differentiableAt (isOpen_ball.mem_nhds hsF))).differentiableWithinAt

private lemma taylorSeries_term_eq (ha : 0 ≤ a) {σ c x y : ℝ} {G : ℂ → ℂ}
    (hGU : Set.EqOn G (LSeries a) {s : ℂ | σ < s.re}) (hc : σ < c)
    (hxc : x - c = -y) (habsc : LSeries.abscissaOfAbsConv a < c) (k : ℕ) :
    (Nat.factorial k : ℂ)⁻¹ • (((x : ℝ) : ℂ) - ((c : ℝ) : ℂ)) ^ k •
        iteratedDeriv k G ((c : ℝ) : ℂ) =
      ((y ^ k / Nat.factorial k *
        (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) := by
  have hUopen : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hcU : ((c : ℝ) : ℂ) ∈ {s : ℂ | σ < s.re} :=
    Set.mem_ofPred.mpr (by simpa using hc)
  have hd : iteratedDeriv k G ((c : ℝ) : ℂ) =
      iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ) :=
    hGU.iteratedDeriv_of_isOpen hUopen k hcU
  have hTk : LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ) =
      (((LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) :=
    Complex.eq_re_of_ofReal_le (by
      rw [Complex.ofReal_zero]
      exact logPowMul_nonneg ha habsc k)
  have hzc : ((x : ℝ) : ℂ) - ((c : ℝ) : ℂ) = -((y : ℝ) : ℂ) := by
    exact_mod_cast hxc
  have e1 : (-((y : ℝ) : ℂ)) ^ k * iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ) =
      ((y : ℝ) : ℂ) ^ k * ((-1 : ℂ) ^ k *
        iteratedDeriv k (LSeries a) ((c : ℝ) : ℂ)) := by
    rw [neg_pow]
    ring
  rw [hd, hzc, smul_eq_mul, smul_eq_mul, e1,
    ← logPowMul_eq_alternating (by simpa using habsc) k]
  nth_rewrite 1 [hTk]
  push_cast
  ring

private lemma hasSum_pow_mul_re_term (a : ℕ → ℂ) (c y : ℝ) (n : ℕ) :
    HasSum (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (Real.log n ^ k * (LSeries.term a ((c : ℝ) : ℂ) n).re))
      ((LSeries.term a (((c - y : ℝ) : ℂ)) n).re) := by
  have h1 : HasSum (fun k : ℕ ↦ (y * Real.log n) ^ k / Nat.factorial k)
      (Real.exp (y * Real.log n)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have h2 := h1.mul_right ((LSeries.term a ((c : ℝ) : ℂ) n).re)
  have heq : Real.exp (y * Real.log n) * (LSeries.term a ((c : ℝ) : ℂ) n).re =
      (LSeries.term a (((c - y : ℝ) : ℂ)) n).re := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := by positivity
      have hyexp : Real.exp (y * Real.log n) = (n : ℝ) ^ y := by
        rw [Real.rpow_def_of_pos hn0, mul_comm]
      have hc : (n : ℝ) ^ c = (n : ℝ) ^ (c - y) * (n : ℝ) ^ y := by
        rw [← Real.rpow_add hn0]
        ring_nf
      rw [re_term_of_ne_zero a c hn, re_term_of_ne_zero a (c - y) hn, hyexp, hc]
      field_simp
  rw [← heq]
  refine h2.congr_fun fun k ↦ ?_
  rw [mul_pow]
  ring

private lemma summable_re_term_of_summable_logPow (ha : 0 ≤ a) {c x y : ℝ}
    (hx : x = c - y) (hy : 0 < y) (habsc : LSeries.abscissaOfAbsConv a < c)
    (hsummable : Summable (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re)) :
    Summable (fun n : ℕ ↦ (LSeries.term a ((x : ℝ) : ℂ) n).re) := by
  have hexp : ∀ n : ℕ, HasSum (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (Real.log n ^ k * (LSeries.term a ((c : ℝ) : ℂ) n).re))
      ((LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    intro n
    simpa only [hx] using hasSum_pow_mul_re_term a c y n
  refine summable_of_sum_le (c := ∑' k : ℕ, y ^ k / Nat.factorial k *
    (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re)
    (fun n ↦ re_term_nonneg ha x n) fun s ↦ ?_
  refine hasSum_le (fun k ↦ ?_) (hasSum_sum fun n _ ↦ hexp n) hsummable.hasSum
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_
    (div_nonneg (pow_nonneg hy.le k) (Nat.cast_nonneg _))
  exact sum_le_hasSum s
    (fun n _ ↦ mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
      (re_term_nonneg ha c n))
    (hasSum_logPowMul_re_term habsc k)

/-- **Landau's theorem.** If `a` has nonnegative values and its abscissa of absolute convergence
is the real number `σ`, then `LSeries a` has no analytic continuation across `σ`. -/
theorem landau (ha : 0 ≤ a) {σ : ℝ} (habs : LSeries.abscissaOfAbsConv a = (σ : EReal)) :
    ¬ HasAnalyticExtensionAt a σ := by
  intro h
  obtain ⟨δ, hδpos, G, hGdiffOn', hGU⟩ := exists_differentiableOn_patch habs h
  set c : ℝ := σ + 1 with hcdef
  set y : ℝ := 1 + δ / 2 with hydef
  set x : ℝ := c - y with hxdef
  have hy0 : 0 < y := by rw [hydef]; linarith
  have hxσ : x < σ := by rw [hxdef, hydef, hcdef]; linarith
  have habsc : LSeries.abscissaOfAbsConv a < c := by
    rw [habs]
    exact_mod_cast (by rw [hcdef]; linarith : σ < c)
  have hxc : x - c = -y := by rw [hxdef]; ring
  have hxball : ((x : ℝ) : ℂ) ∈ ball ((c : ℝ) : ℂ) (1 + δ) := by
    rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, hxc, abs_neg,
      abs_of_pos hy0, hydef]
    linarith
  have hGdiffOn : DifferentiableOn ℂ G (ball ((c : ℝ) : ℂ) (1 + δ)) := by
    simpa only [hcdef] using hGdiffOn'
  have htaylor := Complex.hasSum_taylorSeries_on_ball hGdiffOn hxball
  have hterm : ∀ k : ℕ, (Nat.factorial k : ℂ)⁻¹ • (((x : ℝ) : ℂ) - ((c : ℝ) : ℂ)) ^ k •
      iteratedDeriv k G ((c : ℝ) : ℂ)
      = ((y ^ k / Nat.factorial k *
          (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re : ℝ) : ℂ) := by
    exact fun k ↦ taylorSeries_term_eq ha hGU (by rw [hcdef]; linarith) hxc habsc k
  have hsummable_k : Summable (fun k : ℕ ↦ y ^ k / Nat.factorial k *
      (LSeries (LSeries.logMul^[k] a) ((c : ℝ) : ℂ)).re) :=
    Complex.summable_ofReal.mp (htaylor.congr_fun fun k ↦ (hterm k).symm).summable
  have hsum_x : Summable (fun n : ℕ ↦ (LSeries.term a ((x : ℝ) : ℂ) n).re) := by
    exact summable_re_term_of_summable_logPow ha hxdef hy0 habsc hsummable_k
  have hLS : LSeriesSummable a ((x : ℝ) : ℂ) :=
    (Complex.summable_ofReal.mpr hsum_x).congr fun n ↦
      (term_eq_ofReal_re ha x n).symm
  have hle := hLS.abscissaOfAbsConv_le
  rw [habs, Complex.ofReal_re] at hle
  have hσx : σ ≤ x := mod_cast hle
  linarith

/-- **Landau's theorem, half-plane form.** A Dirichlet series with nonnegative coefficients and
finite abscissa of absolute convergence converges as far to the left as it continues
analytically: if some function differentiable on `Re s > σ₁` agrees with `LSeries a` on the
part of the absolute-convergence half-plane where it is differentiable, then that abscissa is at
most `σ₁`.

This is the form consumed by nonvanishing arguments, where `F` is a quotient of L-functions known
to be analytic on a half-plane, or on the complement of a pole that a positive combination has
already cancelled. -/
theorem abscissaOfAbsConv_le_of_differentiableOn (ha : 0 ≤ a)
    (hfin : LSeries.abscissaOfAbsConv a ≠ ⊤) {σ₁ : ℝ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {s : ℂ | σ₁ < s.re})
    (hFeq : ∀ s : ℂ, σ₁ < s.re → LSeries.abscissaOfAbsConv a < s.re → F s = LSeries a s) :
    LSeries.abscissaOfAbsConv a ≤ σ₁ := by
  by_contra hcon
  have hlt : (σ₁ : EReal) < LSeries.abscissaOfAbsConv a := not_le.mp hcon
  have hbot : LSeries.abscissaOfAbsConv a ≠ ⊥ := fun h ↦ by simp [h] at hlt
  set σ : ℝ := (LSeries.abscissaOfAbsConv a).toReal with hσdef
  have habs : LSeries.abscissaOfAbsConv a = (σ : EReal) := (EReal.coe_toReal hfin hbot).symm
  have hσ₁σ : σ₁ < σ := by rw [habs] at hlt; exact_mod_cast hlt
  refine landau ha habs ⟨σ - σ₁, by linarith, F, ?_, ?_⟩
  · refine hF.mono fun s hs ↦ ?_
    have := sub_lt_re_of_mem_ball hs
    exact Set.mem_ofPred.mpr (by linarith)
  · intro s _ hs
    refine hFeq s (hσ₁σ.trans hs) ?_
    rw [habs]
    exact_mod_cast hs

/-- A Dirichlet series with nonnegative coefficients that has an entire extension in the sense of
`LSeries.HasEntireExtension` converges absolutely at every point of the plane. -/
theorem abscissaOfAbsConv_eq_bot_of_hasEntireExtension (ha : 0 ≤ a)
    (h : LSeries.HasEntireExtension a) : LSeries.abscissaOfAbsConv a = ⊥ := by
  obtain ⟨F, hF, hFa⟩ := h.exists_extension
  have key : ∀ σ₁ : ℝ, LSeries.abscissaOfAbsConv a ≤ (σ₁ : EReal) := fun σ₁ ↦
    abscissaOfAbsConv_le_of_differentiableOn ha h.abscissa_lt_top.ne
      hF.differentiableOn fun s _ hs ↦ hFa hs
  refine le_antisymm ?_ bot_le
  by_contra hne
  obtain ⟨r, -, hr⟩ := EReal.exists_between_coe_real (not_le.mp hne)
  exact absurd (key r) (not_le.mpr hr)

end TauCeti.LSeries
