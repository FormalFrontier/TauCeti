/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# Cancellation in ideal partial sums, and the L-function it continues

The Dirichlet series of a unitary ideal weight `χ` converges absolutely only on `Re s > 1`, because
`|χ|` is `1` on the good ideals and the ideals of `𝓞 K` of absolute norm at most `x` are linear in
`x`. Any continuation past that line has to come from *cancellation* in the ideal partial sums
`A_χ(x) = ∑_{N(I) ≤ x} χ(I)`. This file names that hypothesis and spends it.

* `TauCeti.HasCancellation χ` is the bound `A_χ(x) = O(x ^ (1 - 1 / [K : ℚ]))`, with the exponent
  `TauCeti.cancellationExponent K`.
* `TauCeti.continuedLFunctionOfWeight χ` is the Mellin integral `s ∫_1^∞ A_χ(t) t^(-s-1) dt`,
  which is what Abel summation turns the Dirichlet series into.

The two main results are that the integral *is* the Dirichlet series where the latter converges
(`TauCeti.continuedLFunctionOfWeight_eq_LSeries`, on `Re s > 1`, with no cancellation hypothesis),
and that under `TauCeti.HasCancellation` it is analytic on the strictly larger half-plane
`Re s > 1 - 1 / [K : ℚ]` (`TauCeti.differentiableAt_continuedLFunctionOfWeight` and
`TauCeti.analyticOnNhd_continuedLFunctionOfWeight`). Together they exhibit
`TauCeti.continuedLFunctionOfWeight χ` as an analytic continuation of the norm-regrouped series.

`TauCeti.not_hasCancellation_one` is the accompanying rejection test: the trivial weight has no
cancellation at all, since its ideal partial sums are bounded below by a positive multiple of `x`
by the Layer 5 count `TauCeti.idealCount_linearBounds`. So the hypothesis is a genuine restriction,
and no downstream character family may assume it for free.

## Implementation notes

The bridge between the two indexings is the Layer 4 regrouping lemma
`TauCeti.idealSummatory_eq_sum_Icc_normCoeff` of `Counting.lean`: an ideal partial sum is the
partial sum of the norm coefficients over `1 ≤ k ≤ ⌊x⌋₊`, because the absolute-norm fibres
partition the nonzero ideals of bounded norm. The unconditional `O(n)` bounds on those partial
sums are the Layer 5 estimates `TauCeti.isBigO_sum_Icc_normCoeff` and
`TauCeti.LSeriesSummable_normCoeff_of_one_lt_re` of `Estimates.lean`. Through them, Mathlib's
`LSeries_eq_mul_integral` — Abel summation in its integral form — supplies the identity on
`Re s > 1`, and Mathlib's `mellin_differentiableAt_of_isBigO_rpow` supplies the analyticity: the
integral is the Mellin transform of `A_χ` at `-s`, and `A_χ` vanishes below the cutoff `1`, so the
only constraint on the strip is the growth bound at infinity.

## Roadmap role

This is Layer **6.5** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, whose export table
names `HasCancellation` and `continuedLFunctionOfWeight`. Of that node this file supplies the
definition, the agreement with the norm-regrouped series on `Re s > 1`, the analyticity on
`Re s > 1 - 1 / [K : ℚ]`, and the trivial-weight rejection test; the conjugation operation is
`TauCeti.HasCancellation.conj`. The remaining Layer 6.5 exports — the good-ideal restriction, the
pointwise square, and the imaginary norm twist of a weight with cancellation — are not proved here.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1, for partial summation and the
  half-plane of a Dirichlet series with bounded partial sums.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, for Hecke characters and their L-series.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
* Mathlib's `LSeries_eq_mul_integral` in `Mathlib/NumberTheory/LSeries/SumCoeff.lean`, by
  Xavier Roblot, and `mellin_differentiableAt_of_isBigO_rpow` in
  `Mathlib/Analysis/MellinTransform.lean`: the two analytic inputs used here.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped nonZeroDivisors NumberField Topology

variable {K : Type*} [Field K] [NumberField K]

/-! ### The cancellation exponent -/

variable (K) in
/-- The exponent `1 - 1 / [K : ℚ]` of the cancellation hypothesis of a unitary ideal weight. It
lies in `[0, 1)`, so cancellation at this rate is strictly stronger than the trivial linear bound
on ideal partial sums, and continues the associated Dirichlet series past `Re s = 1`. -/
noncomputable def cancellationExponent : ℝ := 1 - (Module.finrank ℚ K : ℝ)⁻¹

variable (K) in
/-- Defining equation of `TauCeti.cancellationExponent`. -/
theorem cancellationExponent_def :
    cancellationExponent K = 1 - (Module.finrank ℚ K : ℝ)⁻¹ :=
  (rfl)

variable (K) in
/-- The cancellation exponent is nonnegative, since `[K : ℚ] ≥ 1`. -/
theorem cancellationExponent_nonneg : 0 ≤ cancellationExponent K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ)
  have := inv_le_one_of_one_le₀ h
  simpa [cancellationExponent] using this

variable (K) in
/-- The cancellation exponent is strictly less than `1`, since `[K : ℚ]` is finite. -/
theorem cancellationExponent_lt_one : cancellationExponent K < 1 := by
  have h : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ)
  have := inv_pos.mpr h
  simpa [cancellationExponent] using this

/-! ### Cancellation in the ideal partial sums -/

/-- **Cancellation** in the ideal partial sums of a unitary ideal weight: the sums
`∑_{N(I) ≤ x} χ(I)` are `O(x ^ (1 - 1 / [K : ℚ]))`.

Without any hypothesis those sums are only `O(x)`, which is exactly what the trivial weight
achieves; see `TauCeti.not_hasCancellation_one`. A finite quotient of the free ideal group is no
substitute for this hypothesis, since the values of a weight at the primes may be arbitrary.

The predicate is stated for unitary weights, and not for a general ideal arithmetic function,
because the rate `TauCeti.cancellationExponent K` is the one calibrated to coefficients of modulus
at most `1`: a function of unbounded size would have to carry its own exponent. -/
def HasCancellation (χ : UnitaryIdealWeight K) : Prop :=
  (fun x : ℝ ↦ idealSummatory K χ.1.toIdealArithmeticFunction x) =O[atTop]
    fun x : ℝ ↦ x ^ cancellationExponent K

/-- Defining equation of `TauCeti.HasCancellation`. -/
theorem hasCancellation_def (χ : UnitaryIdealWeight K) :
    HasCancellation χ ↔
      (fun x : ℝ ↦ idealSummatory K χ.1.toIdealArithmeticFunction x) =O[atTop]
        fun x : ℝ ↦ x ^ cancellationExponent K :=
  (Iff.rfl)

/-- Cancellation is preserved by conjugation of the weight. -/
theorem HasCancellation.conj {χ : UnitaryIdealWeight K} (hχ : HasCancellation χ) :
    HasCancellation (UnitaryIdealWeight.conj χ) := by
  have hconj : (UnitaryIdealWeight.conj χ).1.toIdealArithmeticFunction
      = fun I ↦ star (χ.1.toIdealArithmeticFunction I) :=
    funext fun I ↦ by simp [UnitaryIdealWeight.val_conj, MultiplicativeIdealWeight.conj_apply]
  rw [hasCancellation_def, ← Asymptotics.isBigO_norm_left] at hχ ⊢
  refine hχ.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  simp only [hconj, idealSummatory_star, norm_star]

/-- **Rejection test: the trivial weight has no cancellation.** Its ideal partial sums count the
nonzero ideals of bounded absolute norm, and the Layer 5 bound `TauCeti.idealCount_linearBounds`
puts a positive multiple of `x` below that count, whereas `x ^ (1 - 1 / [K : ℚ])` is `o(x)`.

So the hypothesis `TauCeti.HasCancellation` genuinely excludes the trivial weight, and with it the
Dedekind zeta function, whose series has a pole at `s = 1`. -/
theorem not_hasCancellation_one : ¬ HasCancellation (1 : UnitaryIdealWeight K) := by
  obtain ⟨b⟩ := idealCount_linearBounds K
  have hθ : cancellationExponent K < 1 := cancellationExponent_lt_one K
  intro h
  rw [hasCancellation_def, Asymptotics.isBigO_iff] at h
  obtain ⟨C, hC⟩ := h
  obtain ⟨x, ⟨hCx, hlim⟩, hx1⟩ :=
    ((hC.and ((tendsto_rpow_atTop (by linarith : (0:ℝ) < 1 - cancellationExponent K)
      ).eventually_gt_atTop (C / b.lower))).and (eventually_ge_atTop (1 : ℝ))).exists
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hcount : b.lower * x ≤ ‖idealSummatory K
      (1 : UnitaryIdealWeight K).1.toIdealArithmeticFunction x‖ := by
    have hval : idealSummatory K (1 : UnitaryIdealWeight K).1.toIdealArithmeticFunction x
        = ((idealsLE K x).card : ℂ) := by
      simp [idealSummatory_apply]
    rw [hval, Complex.norm_natCast,
      ← Nat.card_coe_normLE (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x]
    exact b.le_card x hx1
  rw [Real.norm_rpow_of_nonneg hx0.le, Real.norm_of_nonneg hx0.le] at hCx
  -- Splitting `x = x ^ θ * x ^ (1 - θ)` turns the two bounds into `C < C`.
  have hsplit : x ^ cancellationExponent K * x ^ (1 - cancellationExponent K) = x := by
    rw [← Real.rpow_add hx0]
    simp
  have hpow : (0 : ℝ) < x ^ cancellationExponent K := Real.rpow_pos_of_pos hx0 _
  have hkey : b.lower * (x ^ (1 - cancellationExponent K)) ≤ C := by
    have := hcount.trans hCx
    rw [← hsplit] at this
    nlinarith [b.lower_pos]
  have hgt : C < x ^ (1 - cancellationExponent K) * b.lower := (div_lt_iff₀ b.lower_pos).mp hlim
  rw [mul_comm] at hkey
  linarith

/-! ### The continued L-function of a unitary weight -/

/-- The **continued L-function of a unitary ideal weight**: the Mellin integral
`s ∫_1^∞ A_χ(t) t^(-s-1) dt` of its ideal partial sums `A_χ`.

On `Re s > 1` this is the Dirichlet series of the norm coefficients, by
`TauCeti.continuedLFunctionOfWeight_eq_LSeries`; under `TauCeti.HasCancellation` it is analytic on
the larger half-plane `Re s > TauCeti.cancellationExponent K`, by
`TauCeti.analyticOnNhd_continuedLFunctionOfWeight`. -/
noncomputable def continuedLFunctionOfWeight (χ : UnitaryIdealWeight K) (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ),
    idealSummatory K χ.1.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1))

/-- Defining equation of `TauCeti.continuedLFunctionOfWeight`. -/
theorem continuedLFunctionOfWeight_def (χ : UnitaryIdealWeight K) (s : ℂ) :
    continuedLFunctionOfWeight χ s = s * ∫ t in Set.Ioi (1 : ℝ),
      idealSummatory K χ.1.toIdealArithmeticFunction t * (t : ℂ) ^ (-(s + 1)) :=
  (rfl)

/-- **The continued L-function is the Dirichlet series on `Re s > 1`.** No cancellation hypothesis
is needed: the identity is Abel summation, in Mathlib's integral form
`LSeries_eq_mul_integral`, applied to the unconditional linear bound on ideal partial sums. -/
theorem continuedLFunctionOfWeight_eq_LSeries (χ : UnitaryIdealWeight K) {s : ℂ} (hs : 1 < s.re) :
    continuedLFunctionOfWeight χ s = LSeries (normCoeff K χ.1.toIdealArithmeticFunction) s := by
  rw [continuedLFunctionOfWeight_def,
    LSeries_eq_mul_integral _ zero_le_one hs (LSeriesSummable_normCoeff_of_one_lt_re χ hs)
      (isBigO_sum_Icc_normCoeff χ)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  rw [idealSummatory_eq_sum_Icc_normCoeff K _ (by linarith [Set.mem_Ioi.mp ht] : (0 : ℝ) ≤ t)]

/-! ### Analyticity past the line `Re s = 1` -/

/-- Ideal partial sums are locally integrable on `(0, ∞)`: they are the step function of the
partial sums of the norm coefficients. -/
private theorem locallyIntegrableOn_idealSummatory (f : IdealArithmeticFunction K) :
    LocallyIntegrableOn (fun t : ℝ ↦ idealSummatory K f t) (Set.Ioi 0) := by
  have h := locallyIntegrableOn_mul_sum_Icc (fun k ↦ normCoeff K f k) (m := 1) (a := 0) le_rfl
    (g := fun _ ↦ (1 : ℂ)) ((locallyIntegrable_const (1 : ℂ)).locallyIntegrableOn _)
  refine (h.mono_set Set.Ioi_subset_Ici_self).congr
    ((ae_restrict_iff' measurableSet_Ioi).2 (.of_forall fun t ht ↦ ?_))
  rw [one_mul]
  exact (idealSummatory_eq_sum_Icc_normCoeff K f (le_of_lt ht)).symm

/-- Ideal partial sums vanish near `0`, so they are `O` of every real power there. -/
private theorem isBigO_idealSummatory_nhdsGT_zero (f : IdealArithmeticFunction K) (c : ℝ) :
    (fun t : ℝ ↦ idealSummatory K f t) =O[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ c := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
  rw [idealSummatory_eq_zero_of_lt_one K f ht, norm_zero, one_mul]
  exact norm_nonneg _

/-- The integral defining `TauCeti.continuedLFunctionOfWeight` is the Mellin transform of the
ideal partial sums at `-s`: the integrand vanishes below the cutoff `1`, so extending the range
from `(1, ∞)` to `(0, ∞)` changes nothing. -/
private theorem integral_Ioi_one_eq_mellin (f : IdealArithmeticFunction K) (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), idealSummatory K f t * (t : ℂ) ^ (-(s + 1))
      = mellin (fun t : ℝ ↦ idealSummatory K f t) (-s) := by
  have h : ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ ((-s) - 1) • idealSummatory K f t
      = ∫ t in Set.Ici (1 : ℝ), (t : ℂ) ^ ((-s) - 1) • idealSummatory K f t := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht ↦ Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht))) ?_
    rintro t ⟨-, ht⟩
    rw [idealSummatory_eq_zero_of_lt_one K f (by simpa using ht), smul_zero]
  -- Mathlib writes the Mellin exponent as `(-s) - 1`, the integrand above as `-(s + 1)`.
  have hexp : (-s) - 1 = -(s + 1) := by ring
  rw [mellin, h, integral_Ici_eq_integral_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm ((t : ℂ) ^ ((-s) - 1)), hexp]

/-- **The continued L-function is complex differentiable past `Re s = 1`.** Cancellation at rate
`1 - 1 / [K : ℚ]` makes the defining Mellin integral converge, and depend differentiably on `s`,
at every point of the half-plane `Re s > 1 - 1 / [K : ℚ]`. The half-plane form, and with it
analyticity on a neighbourhood, is `TauCeti.analyticOnNhd_continuedLFunctionOfWeight`. -/
theorem differentiableAt_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) {s : ℂ} (hs : cancellationExponent K < s.re) :
    DifferentiableAt ℂ (continuedLFunctionOfWeight χ) s := by
  have hmellin : DifferentiableAt ℂ
      (mellin fun t : ℝ ↦ idealSummatory K χ.1.toIdealArithmeticFunction t) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -cancellationExponent K) (b := -s.re - 1)
      (locallyIntegrableOn_idealSummatory _)
      (by simpa only [neg_neg] using (hasCancellation_def χ).mp hχ) (by simpa using hs)
      (isBigO_idealSummatory_nhdsGT_zero _ _) (by simp)
  have hfun : continuedLFunctionOfWeight χ =
      fun z : ℂ ↦ z * mellin (fun t : ℝ ↦ idealSummatory K χ.1.toIdealArithmeticFunction t) (-z) :=
    funext fun z ↦ by rw [continuedLFunctionOfWeight_def, integral_Ioi_one_eq_mellin]
  rw [hfun]
  exact differentiableAt_id.mul (hmellin.comp s differentiable_neg.differentiableAt)

/-- **The continued L-function is analytic on `Re s > 1 - 1 / [K : ℚ]`**, the half-plane form of
`TauCeti.differentiableAt_continuedLFunctionOfWeight`. -/
theorem analyticOnNhd_continuedLFunctionOfWeight {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) :
    AnalyticOnNhd ℂ (continuedLFunctionOfWeight χ)
      {s : ℂ | cancellationExponent K < s.re} :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs ↦ (differentiableAt_continuedLFunctionOfWeight hχ hs).differentiableWithinAt)
    (isOpen_lt continuous_const Complex.continuous_re)

end TauCeti
