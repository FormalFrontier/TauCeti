/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates

/-!
# The logarithmic Euler sum of a set of prime ideals

Dirichlet-density arguments compare the prime sum `∑_{𝔭 ∈ S} N(𝔭)⁻ˢ` — Mathlib's
`NumberField.Set.primeIdealZetaSum` — with the logarithm `∑_{𝔭 ∈ S} log (1 - N(𝔭)⁻ˢ)⁻¹` of the
Euler product over `S`, because it is the *latter* that an Euler product turns into the logarithm
of a zeta function.  This file introduces that logarithmic sum as
`TauCeti.primeIdealLogEulerSum` and proves that the two differ by a bounded amount: the difference
lies between `0` and the constant `2 * primeIdealZetaSum Set.univ 2`, uniformly in the exponent
`s > 1` and in the set `S`.  That excess is what the higher prime powers `𝔭 ^ m`, `m ≥ 2`,
contribute to a logarithmic Euler product; the bound below is proved directly, without expanding
the logarithm into its series.

The estimate is elementary and uses no Euler product: for `0 ≤ x ≤ 1/2` one has
`0 ≤ -log (1 - x) - x ≤ 2 * x ^ 2`, and at a height-one prime the local parameter `x = N(𝔭)⁻ˢ` is
at most `1/2` once `s ≥ 1`, with `x ^ 2 ≤ N(𝔭)⁻²`.  Summing over the primes therefore costs no
more than twice the convergent sum `∑_𝔭 N(𝔭)⁻²`.

## Main definitions

* `TauCeti.primeIdealLogEulerSum K S s` is `∑_{𝔭 ∈ S} -log (1 - N(𝔭)⁻ˢ)`, the logarithm of the
  Euler product over `S`.

## Main results

* `TauCeti.primeIdealZetaSum_le_primeIdealLogEulerSum`: the logarithmic sum dominates the prime
  sum.
* `TauCeti.primeIdealLogEulerSum_sub_primeIdealZetaSum_le`: the excess is at most
  `2 * primeIdealZetaSum Set.univ 2`, uniformly in `S` and in `s > 1`.
* `TauCeti.abs_primeIdealLogEulerSum_sub_primeIdealZetaSum_le` and
  `TauCeti.isBigO_primeIdealLogEulerSum_sub_primeIdealZetaSum`: the two-sided form and its `O(1)`
  restatement as `s → 1⁺`.

## Roadmap role

This is the "bounded higher-prime-power contribution" that Layer **7.2** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md` names as one of the two inputs to the
all-prime normalization `P_all(s) = log (1/(s-1)) + O(1)`.  The other input, the infinite Euler
product of Layer **3.3**, is what will identify `primeIdealLogEulerSum K Set.univ s` with
`log ζ_K(s)`; it is not available yet, and nothing here anticipates or assumes it.  Both the
definition and the estimate are stated for an arbitrary set `S` of primes, which is the form
Layer 7.3's density calculus and its Chebotarev consumers use.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

namespace TauCeti

open scoped NumberField
open Filter Topology
open IsDedekindDomain (HeightOneSpectrum)

variable (K : Type*) [Field K] [NumberField K]

/-! ### Elementary bounds on the logarithm -/

/-- The elementary lower bound `x ≤ -log (1 - x)`, valid for every `x < 1`. -/
private theorem self_le_neg_log_one_sub {x : ℝ} (hx : x < 1) : x ≤ -Real.log (1 - x) := by
  have h := Real.log_le_sub_one_of_pos (x := 1 - x) (by linarith)
  linarith

/-- The second-order bound `-log (1 - x) - x ≤ 2 * x ^ 2` on `[0, 1/2]`.  It quantifies the
contribution of the terms `x ^ m / m` with `m ≥ 2` to the logarithmic series. -/
private theorem neg_log_one_sub_sub_self_le {x : ℝ} (hx₀ : 0 ≤ x) (hx : x ≤ 1 / 2) :
    -Real.log (1 - x) - x ≤ 2 * x ^ 2 := by
  have habs : |x| = x := abs_of_nonneg hx₀
  -- Mathlib's Taylor estimate at order one reads `|x + log (1 - x)| ≤ x ^ 2 / (1 - x)`.
  have h := Real.abs_log_sub_add_sum_range_le (x := x) (by rw [habs]; linarith) 1
  rw [Finset.sum_range_one, habs] at h
  norm_num at h
  have h₂ : -(x + Real.log (1 - x)) ≤ |x + Real.log (1 - x)| := neg_le_abs _
  have h₃ : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

variable {K}

/-! ### The local parameter at a height-one prime -/

/-- The local parameter `N(𝔭)⁻ˢ` is positive. -/
theorem absNorm_asIdeal_rpow_neg_pos (P : HeightOneSpectrum (𝓞 K)) (s : ℝ) :
    0 < (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) :=
  Real.rpow_pos_of_pos (absNorm_asIdeal_real_pos P) _

/-- The local parameter `N(𝔭)⁻ˢ` is smaller than `1` as soon as `0 < s`, because `N(𝔭) ≥ 2`. -/
theorem absNorm_asIdeal_rpow_neg_lt_one {s : ℝ} (hs : 0 < s) (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by linarith [two_le_absNorm_asIdeal_real P]) (by linarith)

/-- For `1 ≤ s` the local parameter `N(𝔭)⁻ˢ` is at most `1/2`, because `N(𝔭) ≥ 2`. -/
theorem absNorm_asIdeal_rpow_neg_le_one_half {s : ℝ} (hs : 1 ≤ s) (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h₂ := two_le_absNorm_asIdeal_real P
  have hpow : (2 : ℝ) ^ s ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ s :=
    Real.rpow_le_rpow (by norm_num) h₂ (by linarith)
  have h2s : (2 : ℝ) ≤ (2 : ℝ) ^ s := by
    simpa using Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num) hs
  rw [Real.rpow_neg (Nat.cast_nonneg _), inv_le_comm₀ (by linarith) (by norm_num)]
  linarith

/-- The square of the local parameter at an exponent `s ≥ 1` is at most `N(𝔭)⁻²`. -/
theorem sq_absNorm_asIdeal_rpow_neg_le {s : ℝ} (hs : 1 ≤ s) (P : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2 ≤ (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
  have h₂ := two_le_absNorm_asIdeal_real P
  have hsq : ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) ^ 2
      = (Ideal.absNorm P.asIdeal : ℝ) ^ (-(2 * s)) := by
    rw [← Real.rpow_natCast ((Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) 2,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [hsq]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- **The local higher-prime-power contribution is nonnegative**: the local logarithm always
dominates the local parameter. -/
theorem absNorm_asIdeal_rpow_neg_le_neg_log_one_sub {s : ℝ} (hs : 0 < s)
    (P : HeightOneSpectrum (𝓞 K)) :
    (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)
      ≤ -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)) :=
  self_le_neg_log_one_sub (absNorm_asIdeal_rpow_neg_lt_one hs P)

/-- **The local higher-prime-power contribution is at most `2 N(𝔭)⁻²`**, uniformly in `s ≥ 1`.
This is the estimate that makes the whole prime-power correction bounded. -/
theorem neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg_le {s : ℝ} (hs : 1 ≤ s)
    (P : HeightOneSpectrum (𝓞 K)) :
    -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))
        - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s)
      ≤ 2 * (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ) := by
  refine (neg_log_one_sub_sub_self_le (absNorm_asIdeal_rpow_neg_pos P s).le
    (absNorm_asIdeal_rpow_neg_le_one_half hs P)).trans ?_
  exact mul_le_mul_of_nonneg_left (sq_absNorm_asIdeal_rpow_neg_le hs P) (by norm_num)

variable (K)

/-! ### The logarithmic Euler sum -/

/-- The logarithm `∑_{𝔭 ∈ S} log (1 - N(𝔭)⁻ˢ)⁻¹` of the Euler product over a set `S` of
height-one primes.  For `S = Set.univ` this is the series that the Euler product of Layer 3.3 will
identify with `log ζ_K(s)`. -/
noncomputable def primeIdealLogEulerSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' P : S, -Real.log (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))

variable {K}

/-- Defining equation of `TauCeti.primeIdealLogEulerSum`. -/
theorem primeIdealLogEulerSum_def (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) :
    primeIdealLogEulerSum K S s =
      ∑' P : S, -Real.log (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) :=
  (rfl)

@[simp]
theorem primeIdealLogEulerSum_empty (s : ℝ) :
    primeIdealLogEulerSum K (∅ : Set (HeightOneSpectrum (𝓞 K))) s = 0 := by
  rw [primeIdealLogEulerSum_def]
  exact tsum_empty

/-- The excess of the local logarithms over the local parameters is summable over any set of
primes, for every `s ≥ 1`; it is dominated by `2 N(𝔭)⁻²`. -/
theorem summable_neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 ≤ s) :
    Summable fun P : S ↦ -Real.log (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))
      - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s) := by
  refine Summable.of_nonneg_of_le (fun P ↦ by
      linarith [absNorm_asIdeal_rpow_neg_le_neg_log_one_sub (by linarith : (0 : ℝ) < s) P.1])
    (fun P ↦ neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg_le hs P.1) ?_
  exact ((summable_absNorm_asIdeal_rpow_neg K (by norm_num : (1 : ℝ) < 2)).subtype S).mul_left 2

/-- The logarithmic Euler sum converges for `1 < s`. -/
theorem summable_neg_log_one_sub_absNorm_asIdeal_rpow_neg
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable fun P : S ↦ -Real.log (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) := by
  have h := (summable_neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg S hs.le).add
    ((summable_absNorm_asIdeal_rpow_neg K hs).subtype S)
  simpa using h

/-- The logarithmic Euler sum is nonnegative. -/
theorem primeIdealLogEulerSum_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 0 < s) :
    0 ≤ primeIdealLogEulerSum K S s :=
  tsum_nonneg fun P ↦
    (absNorm_asIdeal_rpow_neg_pos P.1 s).le.trans
      (absNorm_asIdeal_rpow_neg_le_neg_log_one_sub hs P.1)

/-- **The logarithmic Euler sum dominates the prime sum.** -/
theorem primeIdealZetaSum_le_primeIdealLogEulerSum
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    NumberField.Set.primeIdealZetaSum S s ≤ primeIdealLogEulerSum K S s := by
  rw [NumberField.Set.primeIdealZetaSum_def, primeIdealLogEulerSum_def]
  exact ((summable_absNorm_asIdeal_rpow_neg K hs).subtype S).tsum_le_tsum
    (fun P ↦ absNorm_asIdeal_rpow_neg_le_neg_log_one_sub (by linarith) P.1)
    (summable_neg_log_one_sub_absNorm_asIdeal_rpow_neg S hs)

/-- **The excess of the logarithmic Euler sum over the prime sum is the higher-prime-power
contribution**, term by term. -/
theorem primeIdealLogEulerSum_sub_primeIdealZetaSum_eq_tsum
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    primeIdealLogEulerSum K S s - NumberField.Set.primeIdealZetaSum S s
      = ∑' P : S, (-Real.log (1 - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s))
          - (Ideal.absNorm P.1.asIdeal : ℝ) ^ (-s)) := by
  rw [primeIdealLogEulerSum_def, NumberField.Set.primeIdealZetaSum_def]
  exact ((summable_neg_log_one_sub_absNorm_asIdeal_rpow_neg S hs).tsum_sub
    ((summable_absNorm_asIdeal_rpow_neg K hs).subtype S)).symm

/-- **The higher-prime-power contribution is bounded**, uniformly in the set `S` of primes and in
the exponent `s > 1`: it never exceeds twice the convergent sum `∑_𝔭 N(𝔭)⁻²`.

Together with the Euler product of Layer 3.3 and Mathlib's
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`, this is what turns the prime sum over all
primes into `log (1/(s-1)) + O(1)`. -/
theorem primeIdealLogEulerSum_sub_primeIdealZetaSum_le
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    primeIdealLogEulerSum K S s - NumberField.Set.primeIdealZetaSum S s
      ≤ 2 * NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 2 := by
  have hsum2 := summable_absNorm_asIdeal_rpow_neg K (by norm_num : (1 : ℝ) < 2)
  rw [primeIdealLogEulerSum_sub_primeIdealZetaSum_eq_tsum S hs,
    NumberField.Set.primeIdealZetaSum_def,
    tsum_univ fun P : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm P.asIdeal : ℝ) ^ (-2 : ℝ),
    ← tsum_mul_left]
  refine le_trans ((summable_neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg S hs.le).tsum_le_tsum
    (fun P ↦ neg_log_one_sub_sub_absNorm_asIdeal_rpow_neg_le hs.le P.1)
    (((summable_absNorm_asIdeal_rpow_neg K (by norm_num : (1 : ℝ) < 2)).subtype S).mul_left 2)) ?_
  exact Summable.tsum_subtype_le _ S (fun _ ↦ by positivity) (hsum2.mul_left 2)

/-- **The logarithmic Euler sum and the prime sum differ by a bounded amount.** -/
theorem abs_primeIdealLogEulerSum_sub_primeIdealZetaSum_le
    (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    |primeIdealLogEulerSum K S s - NumberField.Set.primeIdealZetaSum S s|
      ≤ 2 * NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 2 := by
  rw [abs_le]
  refine ⟨?_, primeIdealLogEulerSum_sub_primeIdealZetaSum_le S hs⟩
  have h₀ : 0 ≤ 2 * NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 2 := by
    have := NumberField.Set.primeIdealZetaSum_nonneg (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 2
    linarith
  linarith [primeIdealZetaSum_le_primeIdealLogEulerSum S hs]

/-- **The `O(1)` form of the higher-prime-power estimate as `s → 1⁺`**, which is how Layer 7.2
consumes it. -/
theorem isBigO_primeIdealLogEulerSum_sub_primeIdealZetaSum
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    (fun s ↦ primeIdealLogEulerSum K S s - NumberField.Set.primeIdealZetaSum S s)
      =O[𝓝[>] (1 : ℝ)] (1 : ℝ → ℝ) := by
  refine Asymptotics.isBigO_iff.mpr
    ⟨2 * NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 2, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with s hs
  simpa using abs_primeIdealLogEulerSum_sub_primeIdealZetaSum_le S hs

end TauCeti
