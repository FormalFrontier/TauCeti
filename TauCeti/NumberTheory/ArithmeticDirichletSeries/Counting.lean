/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.Order.Northcott

/-!
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory` and `TauCeti.primeSummatory` the associated summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

For `0 ≤ x`, a real cutoff and its floor select the same indices, so
`TauCeti.normLE_eq_normLE_natFloor` and `TauCeti.summatory_eq_summatory_natFloor` convert between
the real and natural conventions. The small-cutoff cases are degenerate for a reason worth
recording: a nonzero ideal has absolute norm at least `1`, and a height-one prime at least `2`, so
`TauCeti.idealsLE_one` isolates the unit ideal and `TauCeti.primesLE_eq_empty_of_lt_two` empties the
prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the finite cutoff
carriers of 4.1, the generic summatory functions of 4.2, and the weighted prime counts `primeTheta`
and `primeCount` of 4.3. What remains in Layer 4 is the prime-power summatory function, which is the
ideal summatory function of a weight supported on prime powers and is therefore written together
with the ideal von Mangoldt weight of Layer 2.3. Layer 5 then supplies the actual size estimates for
these counts.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/-! ### Ideals and height-one primes of bounded absolute norm -/

/-- The absolute norm on nonzero ideals of a Dedekind domain finite and free over `ℤ` is Northcott,
by `Ideal.finite_setOfPred_absNorm_le₀`. Mathlib already supplies the corresponding instance on
height-one primes. -/
instance instNorthcottAbsNormNonZeroDivisors {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] [CharZero R] :
    Northcott (fun I : (Ideal R)⁰ ↦ Ideal.absNorm (I : Ideal R)) :=
  ⟨fun B ↦ Ideal.finite_setOfPred_absNorm_le₀ B⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The nonzero integral ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev idealsLE (x : ℝ) : Finset ((Ideal (𝓞 K))⁰) :=
  normLE (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x

/-- The height-one primes of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primesLE (x : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) x

variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem one_le_absNorm_real_of_nonZeroDivisors (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

/-- The absolute norm of a height-one prime is at least `2`, as a real number. -/
theorem two_le_absNorm_asIdeal_real (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

/-- Below the cutoff `1` there is no nonzero integral ideal to count. -/
theorem idealsLE_eq_empty_of_lt_one {x : ℝ} (hx : x < 1) : idealsLE K x = ∅ :=
  normLE_eq_empty_of_lt _ one_le_absNorm_real_of_nonZeroDivisors hx

/-- At the cutoff `1` the only nonzero integral ideal counted is the unit ideal. -/
theorem idealsLE_one : idealsLE K 1 = {1} := by
  have h : idealsLE K 1 = normFiber K 1 := by
    ext I
    rw [mem_normLE, mem_normFiber]
    exact ⟨fun hI ↦ by
      exact_mod_cast le_antisymm hI (one_le_absNorm_real_of_nonZeroDivisors I),
      fun hI ↦ by simp [hI]⟩
  rw [h, normFiber_one]

/-- Below the cutoff `2` there is no height-one prime to count. -/
theorem primesLE_eq_empty_of_lt_two {x : ℝ} (hx : x < 2) : primesLE K x = ∅ :=
  normLE_eq_empty_of_lt _ two_le_absNorm_asIdeal_real hx

/-- There are at most as many height-one primes as nonzero ideals below any cutoff. -/
theorem card_primesLE_le_card_idealsLE (x : ℝ) : (primesLE K x).card ≤ (idealsLE K x).card := by
  refine Finset.card_le_card_of_injOn
    (fun v ↦ ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩)
    (fun v hv ↦ ?_) fun v _ w _ h ↦ ?_
  · simpa using (mem_normLE _).mp hv
  · exact HeightOneSpectrum.ext (congrArg Subtype.val h)

variable (K)

/-! ### Summatory functions over ideals and over primes -/

/-- The inclusive summatory function of a weight on the nonzero integral ideals of `𝓞 K`. -/
noncomputable abbrev idealSummatory {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) : M :=
  summatory (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) w x

/-- The inclusive summatory function of a weight on the height-one primes of `𝓞 K`. -/
noncomputable abbrev primeSummatory {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) : M :=
  summatory (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) w x

theorem idealSummatory_apply {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I := (rfl)

theorem primeSummatory_apply {M : Type*} [AddCommMonoid M]
    (w : HeightOneSpectrum (𝓞 K) → M) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v := (rfl)

/-- Below the cutoff `1` there is nothing to sum over the nonzero ideals. -/
theorem idealSummatory_eq_zero_of_lt_one {M : Type*} [AddCommMonoid M]
    (w : (Ideal (𝓞 K))⁰ → M) {x : ℝ} (hx : x < 1) :
    idealSummatory K w x = 0 :=
  summatory_eq_zero_of_lt _ one_le_absNorm_real_of_nonZeroDivisors hx w

/-- At the cutoff `1` only the unit ideal contributes. -/
theorem idealSummatory_one {M : Type*} [AddCommMonoid M] (w : (Ideal (𝓞 K))⁰ → M) :
    idealSummatory K w 1 = w 1 := by
  rw [idealSummatory_apply, idealsLE_one, Finset.sum_singleton]

/-! ### The weighted prime counts -/

/-- The logarithmically weighted count of the primes of `S` of absolute norm at most `x`: the
number-field analogue of Chebyshev's `ϑ`. -/
noncomputable def primeTheta (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) x

/-- The number of primes of `S` of absolute norm at most `x`, as a real number: the number-field
analogue of `π`. -/
noncomputable def primeCount (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : ℝ :=
  primeSummatory K (S.indicator 1) x

variable {K}
variable {S T : Set (HeightOneSpectrum (𝓞 K))} {x : ℝ}

theorem primeTheta_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x =
      ∑ v ∈ primesLE K x, S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v :=
  (rfl)

theorem primeCount_apply (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeCount K S x = ∑ v ∈ primesLE K x, S.indicator 1 v := (rfl)

/-- The count of `S` really is the cardinality of the set of primes of `S` below the cutoff. -/
theorem primeCount_eq_card (S : Set (HeightOneSpectrum (𝓞 K))) [DecidablePred (· ∈ S)] (x : ℝ) :
    primeCount K S x = ((primesLE K x).filter (· ∈ S)).card := by
  rw [primeCount_apply]
  simp [Set.indicator_apply, Finset.sum_boole]

@[simp]
theorem primeTheta_empty (x : ℝ) : primeTheta K (∅ : Set (HeightOneSpectrum (𝓞 K))) x = 0 := by
  simp [primeTheta_apply]

@[simp]
theorem primeCount_empty (x : ℝ) : primeCount K (∅ : Set (HeightOneSpectrum (𝓞 K))) x = 0 := by
  simp [primeCount_apply]

/-- The absolute norm of a height-one prime is positive, as a real number. -/
theorem absNorm_asIdeal_real_pos (v : HeightOneSpectrum (𝓞 K)) :
    0 < (Ideal.absNorm v.asIdeal : ℝ) :=
  lt_of_lt_of_le zero_lt_two (two_le_absNorm_asIdeal_real v)

/-- The logarithm of the absolute norm of a height-one prime is nonnegative. -/
theorem log_absNorm_asIdeal_nonneg (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
  Real.log_nonneg (by linarith [two_le_absNorm_asIdeal_real v])

theorem primeTheta_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeTheta K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v) x

theorem primeCount_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeCount K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v) x

theorem primeTheta_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeTheta K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ log_absNorm_asIdeal_nonneg v) v

theorem primeCount_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeCount K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v

theorem primeTheta_mono_set (hST : S ⊆ T) (x : ℝ) : primeTheta K S x ≤ primeTheta K T x :=
  summatory_le_summatory _ (fun v ↦ Set.indicator_le_indicator_of_subset hST
    log_absNorm_asIdeal_nonneg v) x

theorem primeCount_mono_set (hST : S ⊆ T) (x : ℝ) : primeCount K S x ≤ primeCount K T x :=
  summatory_le_summatory _
    (fun v ↦ Set.indicator_le_indicator_of_subset hST (fun _ ↦ zero_le_one) v) x

/-- Below the cutoff `2` no prime is counted. -/
theorem primeTheta_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeTheta K S x = 0 :=
  summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real hx _

theorem primeCount_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeCount K S x = 0 :=
  summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real hx _

theorem primeTheta_eq_primeTheta_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) (hx : 0 ≤ x) :
    primeTheta K S x = primeTheta K S (⌊x⌋₊ : ℝ) :=
  summatory_eq_summatory_natFloor _ _ hx

theorem primeCount_eq_primeCount_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) (hx : 0 ≤ x) :
    primeCount K S x = primeCount K S (⌊x⌋₊ : ℝ) :=
  summatory_eq_summatory_natFloor _ _ hx

/-- The weighted counts are additive along a disjoint union of prime sets. -/
theorem primeTheta_union (hST : Disjoint S T) (x : ℝ) :
    primeTheta K (S ∪ T) x = primeTheta K S x + primeTheta K T x := by
  rw [primeTheta, Set.indicator_union_of_disjoint hST]
  exact summatory_add _ _ _ x

theorem primeCount_union (hST : Disjoint S T) (x : ℝ) :
    primeCount K (S ∪ T) x = primeCount K S x + primeCount K T x := by
  rw [primeCount, Set.indicator_union_of_disjoint hST]
  exact summatory_add _ _ _ x

/-- Chebyshev's trivial comparison: each counted prime contributes at most `log x`. -/
theorem primeTheta_le_primeCount_mul_log (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) :
    primeTheta K S x ≤ primeCount K S x * Real.log x := by
  rw [primeTheta_apply, primeCount_apply, Finset.sum_mul]
  refine Finset.sum_le_sum fun v hv ↦ ?_
  rw [mem_normLE] at hv
  by_cases hS : v ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem hS, Pi.one_apply, one_mul]
    exact Real.log_le_log (absNorm_asIdeal_real_pos v) hv
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS, zero_mul]

/-- A finite set of primes has eventually constant count, namely its cardinality.  This is the
input to the Layer 7 statement that a finite set of primes has Dirichlet density zero. -/
theorem eventually_primeCount_eq_card (hS : S.Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x = S.ncard := by
  filter_upwards [eventually_summatory_eq_sum
    (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (S.indicator (1 : HeightOneSpectrum (𝓞 K) → ℝ)) hS.toFinset
    fun v hv ↦ Set.indicator_of_notMem (by simpa using hv) _] with x hx
  rw [primeCount]
  change summatory (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal)
    (S.indicator 1) x = (S.ncard : ℝ)
  rw [hx, Finset.sum_congr rfl fun v hv ↦
    Set.indicator_of_mem (hS.mem_toFinset.mp hv) _, Set.ncard_eq_toFinset_card S hS]
  simp

theorem eventually_primeTheta_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeTheta K S x - primeTheta K T x
      = ∑ v ∈ hST.toFinset, (S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v
          - T.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v) :=
  eventually_summatory_indicator_sub_eq _ _ hST

theorem eventually_primeCount_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x - primeCount K T x
      = ∑ v ∈ hST.toFinset, (S.indicator 1 v - T.indicator 1 v) :=
  eventually_summatory_indicator_sub_eq _ _ hST

end TauCeti
