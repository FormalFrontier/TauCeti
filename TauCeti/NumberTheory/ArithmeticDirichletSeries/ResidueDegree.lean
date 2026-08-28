/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The primes of residue degree above one are negligible

A height-one prime `𝔭` of `𝓞 K` lies over a unique rational prime `p`, and its absolute norm is
`p ^ f` for `f` the residue degree `Ideal.inertiaDeg 𝔭.asIdeal ℤ`.  The primes with `f = 1`
carry all the mass of every prime-indexed Dirichlet series and of every prime count; this file
proves that the remaining ones, those of residue degree at least `2`, do not.

Two elementary inputs carry the whole argument.

* A prime with `f ≥ 2` has `N(𝔭) = p ^ f ≥ p ^ 2`, so it is *not* determined by a rational prime
  of size `N(𝔭)` but by one of size at most `√(N(𝔭))`.
* At most `[K : ℚ]` height-one primes lie over one rational prime, by the fundamental identity
  `∑ e f = [K : ℚ]`; this is the already available
  `TauCeti.NumberField.card_primesOverFinset_le_finrank`.

Together these compare any finite sum over the degree-above-one primes with `[K : ℚ]` times a sum
over the rational primes with the exponent doubled, which is
`TauCeti.sum_rpow_le_finrank_mul_tsum` below.  Counting gives the `O(√x)` bound, and summing
`m ^ (-2s)` gives convergence for every `s > 1/2` together with a bound on the partial Dirichlet
series that is *uniform* on `s ≥ 1`.

## Main definitions

* `TauCeti.rationalPrimeBelow 𝔭` is the rational prime below a height-one prime `𝔭` of `𝓞 K`,
  namely the absolute norm of `𝔭 ∩ ℤ`.
* `TauCeti.higherDegreePrimes K` is the set of height-one primes of `𝓞 K` whose residue degree
  over `ℚ` exceeds `1`.

## Main results

* `TauCeti.mem_higherDegreePrimes_iff_not_prime_absNorm`: a height-one prime has residue degree
  above one exactly when its absolute norm is not a prime number.
* `TauCeti.primeCount_higherDegreePrimes_le`: the explicit count
  `π_K(x; f ≥ 2) ≤ [K : ℚ] · √x`, with `TauCeti.primeCount_higherDegreePrimes_isBigO` and
  `TauCeti.primeCount_higherDegreePrimes_isLittleO` its `O(√x)` and `o(x / log x)` forms.
* `TauCeti.summable_absNorm_rpow_higherDegreePrimes`: `∑ N(𝔭) ^ (-s)` over the degree-above-one
  primes converges for every `s > 1/2`, in particular at `s = 1`.
* `TauCeti.primeIdealZetaSum_higherDegreePrimes_le`: that sum, in Mathlib's
  `NumberField.Set.primeIdealZetaSum` vocabulary, is at most `2 [K : ℚ]` for every `s ≥ 1`.

The last statement is the shape Dirichlet density consumes: the numerator over the
degree-above-one primes stays bounded as `s → 1⁺`, while the denominator over all primes does
not, so the density is `0`.  The `o(x / log x)` form is the same statement for natural counts,
`x / log x` being the order of magnitude the prime ideal theorem gives for `π_K`.  Neither the
divergence of the all-prime denominator nor the prime ideal theorem is available here, so both
statements are proved from the explicit `√x` bound rather than against an asymptotic for `π_K`.

## Implementation notes

`rationalPrimeBelow` is named rather than spelled out as `Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)`
because every statement below fibres the primes over it: keeping it a single head symbol is what
makes the fibrewise rewriting elaborate, and it is the object `Chebotarev` will name when it
compares a prime of `K` with the rational prime under it.

## Roadmap role

This is Layer **5.3** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`, "Degree-above-one
primes", which asks for "the standard convergence and density-zero statements for residue degree
greater than one" and completes Layer 5.  Layer 7.2 uses the convergence statement to replace the
all-prime Dirichlet sum by the sum over rational primes when proving
`P_all(s) = log (1 / (s - 1)) + O(1)`, and the roadmap records `Chebotarev` as the consumer that
needs it when moving between a field and a fixed subfield.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* J.-P. Serre, *A Course in Arithmetic*, Chapter VI, and J. Milne, *Algebraic Number Theory*,
  Chapter VIII, for the same estimate in the Dirichlet-density setting.
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The height-one primes of `𝓞 K` whose residue degree over `ℚ` is greater than one, that is,
whose absolute norm is a proper power of the rational prime below them. -/
def higherDegreePrimes (K : Type*) [Field K] :
    Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | 1 < Ideal.inertiaDeg 𝔭.asIdeal ℤ}

omit [NumberField K] in
@[simp]
theorem mem_higherDegreePrimes {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ higherDegreePrimes K ↔ 1 < Ideal.inertiaDeg 𝔭.asIdeal ℤ :=
  Iff.rfl

/-! ### The rational prime below a height-one prime -/

/-- The rational prime below a height-one prime `𝔭` of `𝓞 K`, that is, the residue
characteristic of `𝔭`.  It is the absolute norm of the prime `𝔭 ∩ ℤ` of `ℤ`. -/
noncomputable def rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal)

omit [NumberField K] in
/-- The defining formula for `TauCeti.rationalPrimeBelow`. -/
theorem rationalPrimeBelow_def (𝔭 : HeightOneSpectrum (𝓞 K)) :
    rationalPrimeBelow 𝔭 = Ideal.absNorm (Ideal.under ℤ 𝔭.asIdeal) := by
  rw [rationalPrimeBelow]

omit [NumberField K] in
/-- The rational prime below a height-one prime really is a prime number. -/
theorem prime_rationalPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow 𝔭).Prime := by
  have := 𝔭.isPrime
  have : NeZero 𝔭.asIdeal := ⟨𝔭.ne_bot⟩
  exact Nat.absNorm_under_prime 𝔭.asIdeal

/-- The absolute norm of a height-one prime is the rational prime below it raised to the residue
degree. -/
theorem absNorm_eq_rationalPrimeBelow_pow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm 𝔭.asIdeal =
      rationalPrimeBelow 𝔭 ^ Ideal.inertiaDeg 𝔭.asIdeal ℤ := by
  have := 𝔭.isPrime
  exact (Ideal.absNorm_pow_inertiaDeg (Ideal.under ℤ 𝔭.asIdeal) 𝔭.asIdeal).symm

/-- A height-one prime has residue degree above one exactly when its absolute norm is not a prime
number: the norm is `p ^ f`, which is prime precisely for `f = 1`. -/
theorem mem_higherDegreePrimes_iff_not_prime_absNorm {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ higherDegreePrimes K ↔ ¬ (Ideal.absNorm 𝔭.asIdeal).Prime := by
  have := 𝔭.isPrime
  have hpos := Ideal.inertiaDeg_pos 𝔭.asIdeal ℤ
  rw [mem_higherDegreePrimes, absNorm_eq_rationalPrimeBelow_pow 𝔭, Nat.prime_iff, prime_pow_iff,
    ← Nat.prime_iff, not_and_or, or_iff_right (not_not_intro (prime_rationalPrimeBelow 𝔭))]
  omega

/-- A prime of residue degree above one has norm at least the square of the rational prime below
it. -/
theorem sq_rationalPrimeBelow_le_absNorm {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h𝔭 : 𝔭 ∈ higherDegreePrimes K) :
    rationalPrimeBelow 𝔭 ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  rw [absNorm_eq_rationalPrimeBelow_pow 𝔭]
  exact Nat.pow_le_pow_right (prime_rationalPrimeBelow 𝔭).one_lt.le h𝔭

/-! ### Fibring the primes over the rational primes below them -/

/-- In any finite set of height-one primes of `𝓞 K`, at most `[K : ℚ]` have a given rational
prime below them: this is the height-one-spectrum fibre form of
`TauCeti.NumberField.card_primesOverFinset_le_finrank`. -/
theorem card_filter_rationalPrimeBelow_le_finrank (F : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) :
    (F.filter fun 𝔮 ↦ rationalPrimeBelow 𝔮 = m).card ≤
      Module.finrank ℚ K := by
  rcases Finset.eq_empty_or_nonempty
    (F.filter fun 𝔮 ↦ rationalPrimeBelow 𝔮 = m) with h | ⟨𝔭, h𝔭⟩
  · simp [h]
  -- Every prime in the fibre lies over the ideal `span {m}` of `ℤ`, which is therefore maximal.
  have key : ∀ 𝔮 ∈ F.filter fun 𝔮 ↦ rationalPrimeBelow 𝔮 = m,
      Ideal.under ℤ 𝔮.asIdeal = Ideal.span {(m : ℤ)} := by
    intro 𝔮 h𝔮
    rw [← (Finset.mem_filter.mp h𝔮).2, rationalPrimeBelow_def, Int.ideal_span_absNorm_eq_self]
  have h𝔭' := 𝔭.isPrime
  have hspan : (Ideal.span {(m : ℤ)}).IsPrime := key 𝔭 h𝔭 ▸ Ideal.IsPrime.under ℤ 𝔭.asIdeal
  have hne : (Ideal.span {(m : ℤ)} : Ideal ℤ) ≠ ⊥ :=
    key 𝔭 h𝔭 ▸ Ideal.under_ne_bot (A := ℤ) 𝔭.ne_bot
  have : (Ideal.span {(m : ℤ)}).IsMaximal := hspan.isMaximal hne
  refine le_trans (Finset.card_le_card_of_injOn (fun 𝔮 ↦ 𝔮.asIdeal) (fun 𝔮 h𝔮 ↦ ?_)
    (fun 𝔮 _ 𝔮' _ h ↦ HeightOneSpectrum.ext h))
    (NumberField.card_primesOverFinset_le_finrank (K := K) hne)
  exact (IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)).mpr ⟨𝔮.isPrime, ⟨(key 𝔮 h𝔮).symm⟩⟩

/-- Comparison of a finite sum over height-one primes with a sum over the rational primes below
them: the fibres have at most `[K : ℚ]` elements. -/
theorem sum_comp_rationalPrimeBelow_le {g : ℕ → ℝ} {F : Finset (HeightOneSpectrum (𝓞 K))}
    {T : Finset ℕ} (hg : ∀ m ∈ T, 0 ≤ g m) (hFT : ∀ 𝔭 ∈ F, rationalPrimeBelow 𝔭 ∈ T) :
    ∑ 𝔭 ∈ F, g (rationalPrimeBelow 𝔭) ≤ Module.finrank ℚ K * ∑ m ∈ T, g m := by
  rw [← Finset.sum_fiberwise_of_maps_to' hFT g, Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right
    (mod_cast card_filter_rationalPrimeBelow_le_finrank F m) (hg m hm)

/-! ### Counting the primes of residue degree above one -/

/-- There are at most `[K : ℚ] √x` primes of residue degree above one and norm at most `x`:
each lies over a rational prime of size at most `√x`, and at most `[K : ℚ]` of them lie over
the same one. -/
theorem primeCount_higherDegreePrimes_le (x : ℝ) :
    primeCount K (higherDegreePrimes K) x ≤ Module.finrank ℚ K * √x := by
  classical
  have hsqrt : (0 : ℝ) ≤ √x := Real.sqrt_nonneg x
  set F := {𝔭 ∈ primesLE K x | 𝔭 ∈ higherDegreePrimes K} with hF
  have hFT : ∀ 𝔭 ∈ F, rationalPrimeBelow 𝔭 ∈ Finset.Icc 2 ⌊√x⌋₊ := by
    intro 𝔭 h𝔭
    rw [hF, Finset.mem_filter, mem_normLE] at h𝔭
    refine Finset.mem_Icc.mpr ⟨(prime_rationalPrimeBelow 𝔭).two_le, Nat.le_floor ?_⟩
    have hsq : ((rationalPrimeBelow 𝔭 : ℝ)) ^ 2 ≤ x :=
      le_trans (mod_cast sq_rationalPrimeBelow_le_absNorm h𝔭.2) h𝔭.1
    exact (Real.le_sqrt (Nat.cast_nonneg _) (le_trans (by positivity) hsq)).mpr hsq
  have hcount : primeCount K (higherDegreePrimes K) x = ∑ _𝔭 ∈ F, (1 : ℝ) := by
    rw [primeCount_eq_card, hF, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcount]
  refine le_trans (sum_comp_rationalPrimeBelow_le (g := fun _ ↦ (1 : ℝ))
    (fun _ _ ↦ zero_le_one) hFT) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
  calc ((⌊√x⌋₊ + 1 - 2 : ℕ) : ℝ) ≤ ((⌊√x⌋₊ : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    _ ≤ √x := Nat.floor_le hsqrt

/-- The primes of residue degree above one and norm at most `x` number `O(√x)`. -/
theorem primeCount_higherDegreePrimes_isBigO :
    primeCount K (higherDegreePrimes K) =O[atTop] Real.sqrt := by
  refine .of_bound (Module.finrank ℚ K) (.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (primeCount_nonneg (higherDegreePrimes K) x),
    Real.norm_of_nonneg (Real.sqrt_nonneg x)]
  exact primeCount_higherDegreePrimes_le x

private theorem sqrt_isLittleO_div_log : Real.sqrt =o[atTop] fun x ↦ x / Real.log x := by
  have hne : ∀ᶠ x in atTop, x / Real.log x = 0 → √x = 0 := by
    filter_upwards [eventually_gt_atTop 2] with x hx h
    exact absurd h (div_ne_zero (by linarith) (Real.log_pos (by linarith)).ne')
  rw [isLittleO_iff_tendsto' hne]
  -- The quotient is `log x / √x`, which tends to `0` because `log =o[atTop] x ^ (1 / 2)`.
  have hquot : (fun x : ℝ ↦ √x / (x / Real.log x)) =ᶠ[atTop] fun x : ℝ ↦ Real.log x / √x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hsx : √x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
    calc √x / (x / Real.log x) = √x * Real.log x / x := div_div_eq_mul_div _ _ _
      _ = √x * Real.log x / (√x * √x) := by rw [Real.mul_self_sqrt hx.le]
      _ = Real.log x / √x := mul_div_mul_left _ _ hsx
  have h0 : Tendsto (fun x : ℝ ↦ Real.log x / √x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  exact Tendsto.congr' hquot.symm h0

/-- The primes of residue degree above one are a vanishing proportion of all primes: their count
is `o(x / log x)`, and `x / log x` is the order of magnitude the prime ideal theorem gives for the
full prime count `π_K(x)`. -/
theorem primeCount_higherDegreePrimes_isLittleO :
    primeCount K (higherDegreePrimes K) =o[atTop] fun x ↦ x / Real.log x :=
  primeCount_higherDegreePrimes_isBigO.trans_isLittleO sqrt_isLittleO_div_log

/-! ### Convergence of the prime Dirichlet series over the degree-above-one primes -/

private theorem tsum_nat_rpow_neg_le_two {t : ℝ} (ht : 2 ≤ t) :
    ∑' m : ℕ, (m : ℝ) ^ (-t) ≤ 2 := by
  have hsum : ∀ u : ℝ, 1 < u → Summable fun m : ℕ ↦ (m : ℝ) ^ (-u) := fun u hu ↦
    Real.summable_nat_rpow.mpr (by linarith)
  have hfun : (fun m : ℕ ↦ (m : ℝ) ^ (-(2 : ℝ))) = fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2 := by
    funext m
    rw [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_two, one_div]
  have hzeta : ∑' m : ℕ, (m : ℝ) ^ (-(2 : ℝ)) = Real.pi ^ 2 / 6 := by
    rw [hfun]
    exact hasSum_zeta_two.tsum_eq
  refine le_trans (Summable.tsum_le_tsum (fun m ↦ ?_) (hsum t (by linarith))
    (hsum 2 one_lt_two)) ?_
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by norm_num)]
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  · rw [hzeta]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- The key comparison: a finite sum of `N(𝔭) ^ (-s)` over primes of residue degree above one is
bounded by `[K : ℚ]` times the full sum of `m ^ (-2s)` over the natural numbers. -/
theorem sum_rpow_le_finrank_mul_tsum {s : ℝ} (hs : 1 / 2 < s)
    {F : Finset (HeightOneSpectrum (𝓞 K))} (hF : ∀ 𝔭 ∈ F, 𝔭 ∈ higherDegreePrimes K) :
    ∑ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)) := by
  have hs0 : 0 < s := by linarith
  have hsummable : Summable fun m : ℕ ↦ (m : ℝ) ^ (-(2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  -- Compare each term with the corresponding term for the rational prime below it.
  have hterm : ∀ 𝔭 ∈ F, (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤
      ((rationalPrimeBelow 𝔭 : ℝ)) ^ (-(2 * s)) := by
    intro 𝔭 h𝔭
    set a : ℝ := (rationalPrimeBelow 𝔭 : ℝ) with ha
    have ha1 : (1 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (prime_rationalPrimeBelow 𝔭).one_lt.le
    have hle : a ^ (2 : ℕ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := by
      rw [ha]; exact_mod_cast sq_rationalPrimeBelow_le_absNorm (hF 𝔭 h𝔭)
    have hpow : a ^ (-(2 * s)) = (a ^ (2 : ℕ)) ^ (-s) := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_mul (by linarith)]
      congr 1
      push_cast
      ring
    rw [hpow]
    exact Real.rpow_le_rpow_of_nonpos (pow_pos (by linarith) 2) hle (by linarith)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  refine le_trans (sum_comp_rationalPrimeBelow_le (g := fun m ↦ (m : ℝ) ^ (-(2 * s)))
    (fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _)
    (T := F.image rationalPrimeBelow)
    (fun 𝔭 h𝔭 ↦ Finset.mem_image_of_mem rationalPrimeBelow h𝔭)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact Summable.sum_le_tsum _ (fun m _ ↦ Real.rpow_nonneg (Nat.cast_nonneg m) _) hsummable

/-- The Dirichlet series over the primes of residue degree above one converges for every
`s > 1/2`, in particular at `s = 1`. -/
theorem summable_absNorm_rpow_higherDegreePrimes {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun 𝔭 : higherDegreePrimes K ↦ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
  classical
  refine summable_of_sum_le (c := Module.finrank ℚ K * ∑' m : ℕ, (m : ℝ) ^ (-(2 * s)))
    (fun 𝔭 ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) fun u ↦ ?_
  have := sum_rpow_le_finrank_mul_tsum (K := K) hs
    (F := u.image Subtype.val) (fun 𝔭 h𝔭 ↦ by
      obtain ⟨𝔮, -, rfl⟩ := Finset.mem_image.mp h𝔭
      exact 𝔮.2)
  rwa [Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext h] at this

/-- Uniformly in `s ≥ 1`, the partial Dirichlet sum over the primes of residue degree above one is
at most `2 [K : ℚ]`.  This is the density-zero input: the numerator stays bounded as `s → 1⁺`
while the all-prime denominator does not. -/
theorem primeIdealZetaSum_higherDegreePrimes_le {s : ℝ} (hs : 1 ≤ s) :
    (higherDegreePrimes K).primeIdealZetaSum s ≤ 2 * Module.finrank ℚ K := by
  classical
  rw [NumberField.Set.primeIdealZetaSum_def]
  refine Real.tsum_le_of_sum_le (fun 𝔭 ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _) fun u ↦ ?_
  have hsum := sum_rpow_le_finrank_mul_tsum (K := K) (s := s) (show (1 : ℝ) / 2 < s by linarith)
    (F := u.image Subtype.val) (fun 𝔭 h𝔭 ↦ by
      obtain ⟨𝔮, -, rfl⟩ := Finset.mem_image.mp h𝔭
      exact 𝔮.2)
  rw [Finset.sum_image fun _ _ _ _ h ↦ Subtype.ext h] at hsum
  refine hsum.trans ?_
  rw [mul_comm (2 : ℝ) (Module.finrank ℚ K : ℝ)]
  exact mul_le_mul_of_nonneg_left (tsum_nat_rpow_neg_le_two (t := 2 * s) (by linarith))
    (Nat.cast_nonneg _)

end TauCeti
