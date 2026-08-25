/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Counting carriers for ideals and prime ideals

Every estimate in the arithmetic-Dirichlet-series roadmap counts objects whose absolute norm does
not exceed a *real* cutoff `x`, and always inclusively: an object of norm exactly `x` is counted.
This file fixes that convention once.

The common core is Mathlib's `Northcott` property: a function `N : ι → ℕ` is Northcott when each
set `{i | N i ≤ B}` is finite.  For such an `N`:

* `TauCeti.normLE N x` is the finite set of indices with `(N i : ℝ) ≤ x`;
* `TauCeti.summatory N w x` is the inclusive sum of a real weight `w` over `TauCeti.normLE N x`.

Two instances of this core carry the arithmetic content, `TauCeti.idealsLE` for the nonzero
integral ideals of `𝓞 K` and `TauCeti.primesLE` for the height-one primes, with
`TauCeti.idealSummatory` and `TauCeti.primeSummatory` the associated summatory functions.  The
weighted prime counts of the roadmap are the two named specializations
`TauCeti.primeTheta`, the logarithmically weighted count, and `TauCeti.primeCount`, the
unweighted one; both are restricted to a set `S` of height-one primes through `Set.indicator`,
so no decidability hypothesis is needed on `S`.

Because a real cutoff and its floor select the same indices, `TauCeti.normLE_natFloor` and
`TauCeti.summatory_natFloor` convert between the real and natural conventions.  The small-cutoff
cases are degenerate for a reason worth recording: a nonzero ideal has absolute norm at least `1`,
and a height-one prime at least `2`, so `TauCeti.idealsLE_one` isolates the unit ideal and
`TauCeti.primesLE_eq_empty_of_lt_two` empties the prime carrier below `2`.

Modifying a weight on a finite set, or a prime set on a finite symmetric difference, changes a
summatory function by a quantity that is eventually the *constant* total discrepancy; this is
`TauCeti.eventually_summatory_sub_eq` and its two prime specializations. Layer 7 uses these to
show that finite changes do not affect a density.

## Roadmap role

This is Layer **4** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: the cutoff subtypes
of 4.1, the generic summatory functions of 4.2, and the weighted prime counts `primeTheta` and
`primeCount` of 4.3.  What remains in Layer 4 is the prime-power summatory function, which is the
ideal summatory function of a weight supported on prime powers and is therefore written together
with the ideal von Mangoldt weight of Layer 2.3.  Layer 5 then supplies the actual size estimates
for these counts.

## References

* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters I--II.
* H. Davenport, *Multiplicative Number Theory*, Chapters 1 and 7.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField
open IsDedekindDomain

/-! ### The generic real-cutoff carrier -/

section Northcott

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-- Only finitely many indices have `N`-value at most a fixed real number, because the `N`-value
is a natural number and `N` is Northcott. -/
theorem finite_setOf_natCast_le (x : ℝ) : {i : ι | (N i : ℝ) ≤ x}.Finite :=
  (Northcott.finite_le (h := N) ⌊x⌋₊).subset fun _ hi ↦ Nat.le_floor hi

/-- The finite set of indices whose `N`-value is at most the real cutoff `x`.  The cutoff is
inclusive: an index with `N i = x` belongs to `normLE N x`. -/
noncomputable def normLE (x : ℝ) : Finset ι :=
  (finite_setOf_natCast_le N x).toFinset

@[simp]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

theorem coe_normLE (x : ℝ) : (normLE N x : Set ι) = {i : ι | (N i : ℝ) ≤ x} := by
  ext i
  simp

theorem normLE_mono : Monotone (normLE N) := fun _ _ hxy _ hi ↦
  mem_normLE N |>.mpr <| (mem_normLE N |>.mp hi).trans hxy

/-- Membership in a carrier with natural cutoff is the plain inequality of natural numbers. -/
theorem mem_normLE_natCast {i : ι} {n : ℕ} : i ∈ normLE N (n : ℝ) ↔ N i ≤ n := by
  simp

/-- A nonnegative real cutoff and its floor select the same indices; this is the promised
conversion between the real and the natural cutoff conventions.  Nonnegativity is needed: for
`x < 0` the floor is `0`, which still admits an index of `N`-value `0`. -/
theorem normLE_natFloor {x : ℝ} (hx : 0 ≤ x) : normLE N x = normLE N (⌊x⌋₊ : ℝ) := by
  ext i
  rw [mem_normLE, mem_normLE_natCast]
  exact ⟨Nat.le_floor, fun hi ↦ (Nat.le_floor_iff hx).mp hi⟩

/-- Below a uniform lower bound for the `N`-values the carrier is empty. -/
theorem normLE_eq_empty {b x : ℝ} (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b) : normLE N x = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi ↦ ?_
  exact absurd ((hb i).trans (mem_normLE N |>.mp hi)) (not_le.mpr hx)

/-! ### The generic summatory function -/

/-- The inclusive summatory function of a real weight `w`: the sum of `w` over all indices of
`N`-value at most `x`. -/
noncomputable def summatory (w : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ normLE N x, w i

theorem summatory_apply (w : ι → ℝ) (x : ℝ) : summatory N w x = ∑ i ∈ normLE N x, w i := (rfl)

@[simp]
theorem summatory_zero (x : ℝ) : summatory N (0 : ι → ℝ) x = 0 := by
  simp [summatory]

theorem summatory_add (w₁ w₂ : ι → ℝ) (x : ℝ) :
    summatory N (w₁ + w₂) x = summatory N w₁ x + summatory N w₂ x := by
  simp [summatory, Finset.sum_add_distrib]

theorem summatory_sub (w₁ w₂ : ι → ℝ) (x : ℝ) :
    summatory N (w₁ - w₂) x = summatory N w₁ x - summatory N w₂ x := by
  simp [summatory, Finset.sum_sub_distrib]

theorem summatory_const_mul (c : ℝ) (w : ι → ℝ) (x : ℝ) :
    summatory N (fun i ↦ c * w i) x = c * summatory N w x := by
  simp [summatory, Finset.mul_sum]

theorem summatory_eq_empty_cutoff {b x : ℝ} (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b)
    (w : ι → ℝ) : summatory N w x = 0 := by
  simp [summatory, normLE_eq_empty N hb hx]

theorem summatory_natFloor (w : ι → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    summatory N w x = summatory N w (⌊x⌋₊ : ℝ) := by
  rw [summatory, summatory, normLE_natFloor N hx]

theorem summatory_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) : 0 ≤ summatory N w x :=
  Finset.sum_nonneg fun i _ ↦ hw i

theorem summatory_le_summatory {w₁ w₂ : ι → ℝ} (h : ∀ i, w₁ i ≤ w₂ i) (x : ℝ) :
    summatory N w₁ x ≤ summatory N w₂ x :=
  Finset.sum_le_sum fun i _ ↦ h i

/-- A summatory function with nonnegative weight is monotone in the cutoff. -/
theorem summatory_mono {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (summatory N w) :=
  fun _ _ hxy ↦ Finset.sum_le_sum_of_subset_of_nonneg (normLE_mono N hxy) fun i _ _ ↦ hw i

/-- Changing a weight on a finite set of indices changes the summatory function, for all large
cutoffs, by the constant total discrepancy over that set. -/
theorem eventually_summatory_sub_eq (w₁ w₂ : ι → ℝ) (u : Finset ι) (h : ∀ i ∉ u, w₁ i = w₂ i) :
    ∀ᶠ x in Filter.atTop,
      summatory N w₁ x - summatory N w₂ x = ∑ i ∈ u, (w₁ i - w₂ i) := by
  filter_upwards [Filter.eventually_ge_atTop ((u.sup N : ℕ) : ℝ)] with x hx
  have hsub : u ⊆ normLE N x := fun i hi ↦
    mem_normLE N |>.mpr <| le_trans (by exact_mod_cast Finset.le_sup (f := N) hi) hx
  rw [summatory, summatory, ← Finset.sum_sub_distrib]
  exact (Finset.sum_subset hsub fun i _ hi ↦ by rw [h i hi, sub_self]).symm

/-- A weight vanishing outside a finite set has eventually constant summatory function, equal to
its total sum. -/
theorem eventually_summatory_eq_sum (w : ι → ℝ) (u : Finset ι) (h : ∀ i ∉ u, w i = 0) :
    ∀ᶠ x in Filter.atTop, summatory N w x = ∑ i ∈ u, w i := by
  filter_upwards [eventually_summatory_sub_eq N w 0 u (by simpa using h)] with x hx
  simpa using hx

end Northcott

/-! ### Ideals and height-one primes of bounded absolute norm -/

variable (K : Type*) [Field K] [NumberField K]

instance instNorthcottAbsNormNonZeroDivisors :
    Northcott (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) :=
  ⟨fun B ↦ Ideal.finite_setOfPred_absNorm_le₀ B⟩

/-- The nonzero integral ideals of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev idealsLE (x : ℝ) : Finset ((Ideal (𝓞 K))⁰) :=
  normLE (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) x

/-- The height-one primes of `𝓞 K` of absolute norm at most `x`. -/
noncomputable abbrev primesLE (x : ℝ) : Finset (HeightOneSpectrum (𝓞 K)) :=
  normLE (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) x

variable {K}

/-- The absolute norm of a nonzero integral ideal is at least `1`, as a real number. -/
theorem one_le_absNorm_of_nonZeroDivisors (I : (Ideal (𝓞 K))⁰) :
    (1 : ℝ) ≤ Ideal.absNorm (I : Ideal (𝓞 K)) := by
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

/-- The absolute norm of a height-one prime is at least `2`, as a real number. -/
theorem two_le_absNorm_asIdeal (v : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

/-- Below the cutoff `1` there is no nonzero integral ideal to count. -/
theorem idealsLE_eq_empty_of_lt_one {x : ℝ} (hx : x < 1) : idealsLE K x = ∅ :=
  normLE_eq_empty _ one_le_absNorm_of_nonZeroDivisors hx

/-- At the cutoff `1` the only nonzero integral ideal counted is the unit ideal. -/
theorem idealsLE_one : idealsLE K 1 = {1} := by
  ext I
  rw [mem_normLE, Finset.mem_singleton]
  refine ⟨fun hI ↦ ?_, fun hI ↦ ?_⟩
  · have : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 := by
      have := one_le_absNorm_of_nonZeroDivisors I
      have : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) = 1 := le_antisymm hI this
      exact_mod_cast this
    exact Subtype.ext (by simpa [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp this)
  · subst hI
    simp [Ideal.one_eq_top, Ideal.absNorm_eq_one_iff.mpr rfl]

/-- Below the cutoff `2` there is no height-one prime to count. -/
theorem primesLE_eq_empty_of_lt_two {x : ℝ} (hx : x < 2) : primesLE K x = ∅ :=
  normLE_eq_empty _ two_le_absNorm_asIdeal hx

/-- There are at most as many height-one primes as nonzero ideals below any cutoff. -/
theorem card_primesLE_le_card_idealsLE (x : ℝ) : (primesLE K x).card ≤ (idealsLE K x).card := by
  refine Finset.card_le_card_of_injOn
    (fun v ↦ ⟨v.asIdeal, Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mp
      (by have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)⟩)
    (fun v hv ↦ ?_) fun v _ w _ h ↦ ?_
  · simpa using (mem_normLE _).mp hv
  · exact HeightOneSpectrum.ext (congrArg Subtype.val h)

variable (K)

/-! ### Summatory functions over ideals and over primes -/

/-- The inclusive summatory function of a weight on the nonzero integral ideals of `𝓞 K`. -/
noncomputable abbrev idealSummatory (w : (Ideal (𝓞 K))⁰ → ℝ) (x : ℝ) : ℝ :=
  summatory (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) w x

/-- The inclusive summatory function of a weight on the height-one primes of `𝓞 K`. -/
noncomputable abbrev primeSummatory (w : HeightOneSpectrum (𝓞 K) → ℝ) (x : ℝ) : ℝ :=
  summatory (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) w x

theorem idealSummatory_apply (w : (Ideal (𝓞 K))⁰ → ℝ) (x : ℝ) :
    idealSummatory K w x = ∑ I ∈ idealsLE K x, w I := (rfl)

theorem primeSummatory_apply (w : HeightOneSpectrum (𝓞 K) → ℝ) (x : ℝ) :
    primeSummatory K w x = ∑ v ∈ primesLE K x, w v := (rfl)

/-- Below the cutoff `1` there is nothing to sum over the nonzero ideals. -/
theorem idealSummatory_eq_zero_of_lt_one (w : (Ideal (𝓞 K))⁰ → ℝ) {x : ℝ} (hx : x < 1) :
    idealSummatory K w x = 0 :=
  summatory_eq_empty_cutoff _ one_le_absNorm_of_nonZeroDivisors hx w

/-- At the cutoff `1` only the unit ideal contributes. -/
theorem idealSummatory_one (w : (Ideal (𝓞 K))⁰ → ℝ) : idealSummatory K w 1 = w 1 := by
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

theorem primeTheta_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeTheta K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ Real.log_nonneg (by linarith [two_le_absNorm_asIdeal v])) v) x

theorem primeCount_nonneg (S : Set (HeightOneSpectrum (𝓞 K))) (x : ℝ) : 0 ≤ primeCount K S x :=
  summatory_nonneg _ (fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v) x

theorem primeTheta_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeTheta K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg
    (fun v _ ↦ Real.log_nonneg (by linarith [two_le_absNorm_asIdeal v])) v

theorem primeCount_mono (S : Set (HeightOneSpectrum (𝓞 K))) : Monotone (primeCount K S) :=
  summatory_mono _ fun v ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) v

theorem primeTheta_mono_set (hST : S ⊆ T) (x : ℝ) : primeTheta K S x ≤ primeTheta K T x :=
  summatory_le_summatory _ (fun v ↦ Set.indicator_le_indicator_of_subset hST
    (fun v ↦ Real.log_nonneg (by linarith [two_le_absNorm_asIdeal v])) v) x

theorem primeCount_mono_set (hST : S ⊆ T) (x : ℝ) : primeCount K S x ≤ primeCount K T x :=
  summatory_le_summatory _
    (fun v ↦ Set.indicator_le_indicator_of_subset hST (fun _ ↦ zero_le_one) v) x

/-- Below the cutoff `2` no prime is counted. -/
theorem primeTheta_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeTheta K S x = 0 :=
  summatory_eq_empty_cutoff _ two_le_absNorm_asIdeal hx _

theorem primeCount_eq_zero_of_lt_two (S : Set (HeightOneSpectrum (𝓞 K))) (hx : x < 2) :
    primeCount K S x = 0 :=
  summatory_eq_empty_cutoff _ two_le_absNorm_asIdeal hx _

theorem primeTheta_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) (hx : 0 ≤ x) :
    primeTheta K S x = primeTheta K S (⌊x⌋₊ : ℝ) :=
  summatory_natFloor _ _ hx

theorem primeCount_natFloor (S : Set (HeightOneSpectrum (𝓞 K))) (hx : 0 ≤ x) :
    primeCount K S x = primeCount K S (⌊x⌋₊ : ℝ) :=
  summatory_natFloor _ _ hx

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
    exact Real.log_le_log (by linarith [two_le_absNorm_asIdeal v]) hv
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem hS, zero_mul]

/-- Two prime sets differing by a finite symmetric difference have eventually constant difference
of weighted counts.  Layer 7 turns this into the invariance of a Dirichlet density under a finite
change of the prime set. -/
theorem eventually_primeSummatory_indicator_sub_eq (w : HeightOneSpectrum (𝓞 K) → ℝ)
    (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeSummatory K (S.indicator w) x - primeSummatory K (T.indicator w) x
      = ∑ v ∈ hST.toFinset, (S.indicator w v - T.indicator w v) := by
  refine eventually_summatory_sub_eq _ _ _ hST.toFinset fun v hv ↦ ?_
  rw [Set.Finite.mem_toFinset, Set.mem_symmDiff] at hv
  by_cases hS : v ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (by tauto)]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem (by tauto)]

/-- A finite set of primes has eventually constant count, namely its cardinality.  This is the
input to the Layer 7 statement that a finite set of primes has Dirichlet density zero. -/
theorem eventually_primeCount_eq_card (hS : S.Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x = hS.toFinset.card := by
  filter_upwards [eventually_summatory_eq_sum
    (fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal) (S.indicator 1) hS.toFinset
    fun v hv ↦ Set.indicator_of_notMem (by simpa using hv) _] with x hx
  have hx' : primeCount K S x = ∑ v ∈ hS.toFinset, S.indicator 1 v := hx
  rw [hx', Finset.sum_congr rfl fun v hv ↦ Set.indicator_of_mem (hS.mem_toFinset.mp hv) _]
  simp

theorem eventually_primeTheta_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeTheta K S x - primeTheta K T x
      = ∑ v ∈ hST.toFinset, (S.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v
          - T.indicator (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) v) :=
  eventually_primeSummatory_indicator_sub_eq _ hST

theorem eventually_primeCount_sub_eq (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, primeCount K S x - primeCount K T x
      = ∑ v ∈ hST.toFinset, (S.indicator 1 v - T.indicator 1 v) :=
  eventually_primeSummatory_indicator_sub_eq _ hST

end TauCeti
