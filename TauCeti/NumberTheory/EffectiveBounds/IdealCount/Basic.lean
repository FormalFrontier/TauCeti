/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Pi.Interval
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.Data.Set.Card.Arithmetic

/-!
# An effective count of ideals of bounded norm

In a number field `F` of degree `n`, the number of nonzero integral ideals of norm at most
`X` is at most `X² · 2ⁿ`. A nonzero ideal is encoded injectively as an `n`-tuple of positive
naturals with product `≤ absNorm I` (distributing, for each rational prime `p`, the value
`p^{vₚ}` of the `i`-th prime above `p` into the `i`-th coordinate); the valuations of the
tuple recover the ideal, and there are at most `X²·2ⁿ` such tuples.

Mathlib's `Ideal.finite_setOf_absNorm_le` already gives finiteness (and `Ideal/Asymptotics`
the sharp asymptotic `~ ρ·X`); the contribution here is the explicit elementary bound, the
input to the effective class-number estimate.

## Main result

* `TauCeti.NumberField.card_ideal_absNorm_le`: at most `X²·2^[F:ℚ]` nonzero ideals of norm
  `≤ X`.

The `Consumer` section at the end restates this bound in the natural-number and degree-monotone
forms later effective estimates use (`ncard_ideal_absNorm_le_nat`,
`ncard_ideal_absNorm_le_of_nat_le_of_finrank_le`, `ncard_ideal_absNorm_le_of_finrank_le`,
`ncard_ideal_absNorm_le_nat_of_finrank_le`).

## Provenance

Migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where this Rankin-style count fed the class-number bound.
-/

public section

attribute [local instance] Classical.propDecidable

namespace TauCeti.NumberField

/-- The set of `n`-tuples of positive naturals with real product at most `X`. -/
private def prodLeTuples (n : ℕ) (X : ℝ) : Set (Fin n → ℕ) :=
  {d : Fin n → ℕ | (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X}

@[simp]
private theorem mem_prodLeTuples {n : ℕ} {X : ℝ} {d : Fin n → ℕ} :
    d ∈ prodLeTuples n X ↔ (∀ i, 0 < d i) ∧ (∏ i, (d i : ℝ)) ≤ X := Iff.rfl

/-- The tuple set is finite: every coordinate lies in `[1, ⌊X⌋]`. -/
private theorem prodLeTuples_finite (n : ℕ) (X : ℝ) : (prodLeTuples n X).Finite := by
  apply Set.Finite.subset (Set.finite_Icc (1 : Fin n → ℕ) (fun _ => ⌊X⌋₊))
  rintro d ⟨hpos, hprod⟩
  refine ⟨fun i => hpos i, fun i => Nat.le_floor ?_⟩
  exact le_trans (mod_cast Finset.single_le_prod' (fun a _ => hpos a) (Finset.mem_univ i)) hprod

/-- `∑_{j=1}^{N} 1/j² ≤ 2`, from the Basel sum `π²/6 < 2`. -/
private theorem sum_one_div_sq_le_two (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  have hconv : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 := by
    simpa using sum_le_hasSum (Finset.Icc 1 N) (fun n _ => by positivity)
      (by simpa using hasSum_zeta_two)
  have hpi : Real.pi < 3.4 := by pi_upper_bound [7 / 5]
  nlinarith [hconv, Real.pi_pos, hpi]

/-- Splitting off the last coordinate `j`, which ranges over `{1, …, ⌊X⌋}`: an `(n+1)`-tuple
with product at most `X` is an `n`-tuple with product at most `X / j` followed by `j`. -/
private theorem prodLeTuples_succ_eq_iUnion (n : ℕ) (X : ℝ) :
    prodLeTuples (n + 1) X = ⋃ j ∈ Finset.Icc 1 ⌊X⌋₊,
      (fun e => Fin.snoc e j) '' (prodLeTuples n (X / j)) := by
  ext d; simp only [prodLeTuples, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image,
    Finset.mem_Icc]
  constructor <;> intro h
  · refine ⟨d (Fin.last n), ⟨h.1 _, Nat.le_floor ?_⟩, Fin.init d, ⟨?_, ?_⟩,
      Fin.snoc_init_self d⟩
    · refine le_trans ?_ h.2
      rw [Fin.prod_univ_castSucc]
      exact le_mul_of_one_le_left (Nat.cast_nonneg _)
        (mod_cast Finset.one_le_prod' fun i _ => h.1 _)
    · exact fun i => h.1 _
    · rw [le_div_iff₀ (mod_cast h.1 (Fin.last n))]
      rw [Fin.prod_univ_castSucc] at h
      simpa [Fin.init] using h.2
  · obtain ⟨j, ⟨hj1, -⟩, e, ⟨hepos, heprod⟩, rfl⟩ := h
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · rw [Fin.snoc_last]; exact hj1
      · rw [Fin.snoc_castSucc]; exact hepos i
    · rw [Fin.prod_univ_castSucc, Fin.snoc_last]
      simp only [Fin.snoc_castSucc]
      rw [le_div_iff₀ hj0] at heprod
      linarith [heprod]

/-- The number of `(n+1)`-tuples with product at most `X` is at most the sum, over the last
coordinate `j ∈ {1, …, ⌊X⌋}`, of the counts of `n`-tuples with product at most `X / j`. -/
private theorem prodLeTuples_succ_ncard_le (n : ℕ) (X : ℝ) :
    (prodLeTuples (n + 1) X).ncard ≤
      ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (prodLeTuples n (X / j)).ncard := by
  rw [prodLeTuples_succ_eq_iUnion]
  exact (Finset.set_ncard_biUnion_le _ _).trans
    (Finset.sum_le_sum fun j _ => Set.ncard_image_le (prodLeTuples_finite _ _))

/-- The number of positive `n`-tuples of natural numbers whose real product is at most `X` is
at most `X² * 2ⁿ`, for `X ≥ 1`. -/
private theorem prodLeTuples_ncard_le (n : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((prodLeTuples n X).ncard : ℝ) ≤ X ^ 2 * 2 ^ n := by
  induction n generalizing X with
  | zero =>
      have huniv : prodLeTuples 0 X = Set.univ := by
        ext d; simp [prodLeTuples, Subsingleton.elim d 0, hX]
      rw [huniv, Set.ncard_univ, Nat.card_unique, pow_zero, Nat.cast_one, mul_one]
      nlinarith [hX, sq_nonneg (X - 1)]
  | succ n ih =>
      -- Bound the count by the sum over the last coordinate, then apply the IH to each term.
      refine le_trans (Nat.cast_le.mpr (prodLeTuples_succ_ncard_le n X)) ?_
      push_cast
      refine le_trans (Finset.sum_le_sum fun i hi => ih ?_) ?_
      · rw [le_div_iff₀ (by exact_mod_cast (Finset.mem_Icc.mp hi).1)]
        simpa using le_trans (mod_cast (Finset.mem_Icc.mp hi).2) (Nat.floor_le (by linarith))
      · have h_sum : ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (X / (j : ℝ)) ^ 2 * 2 ^ n
            = X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        rw [h_sum, pow_succ]
        calc X ^ 2 * 2 ^ n * ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 / (j : ℝ)) ^ 2
            ≤ X ^ 2 * 2 ^ n * 2 :=
              mul_le_mul_of_nonneg_left (by simpa using sum_one_div_sq_le_two ⌊X⌋₊)
                (by positivity)
          _ = X ^ 2 * (2 ^ n * 2) := by ring

/-! ### Encoding ideals as tuples (for the Rankin-style ideal count)

We encode a nonzero ideal `I` of `𝓞 F` as an `n`-tuple of positive naturals
(`n = [F:ℚ]`) whose product is at most `absNorm I`, injectively. For a nonzero
prime `P`, `absNormUnder P` is the norm of the rational prime below `P` and `primeCoord P`
is the index of `P` among the (at most `n`) primes above that rational prime. The
`i`-th coordinate of the encoding multiplies `(absNormUnder P) ^ (mult of P in I)`
over all prime factors `P` of `I` with `primeCoord P = i`. -/
section RankinCount

open _root_.NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-- The norm of the rational prime below a prime ideal `P` of `𝓞 F`. -/
private def absNormUnder (P : Ideal (𝓞 F)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The coordinate (index in `Fin [F:ℚ]`) assigned to a prime ideal `P`: its
position in the list of primes above the rational prime below `P`. -/
private def primeCoord (P : Ideal (𝓞 F)) : ℕ :=
  (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.idxOf P

/-- The `i`-th coordinate of the tuple encoding the ideal `I`. -/
private def encodeIdeal (I : Ideal (𝓞 F)) (i : Fin (Module.finrank ℚ F)) : ℕ :=
  ∏ P ∈ (normalizedFactors I).toFinset.filter (fun P => primeCoord F P = i.val),
    (absNormUnder F P) ^ ((normalizedFactors I).count P)

/-
[foundational] `P` belongs to the finite set of primes above the rational
prime below it.
-/
private theorem mem_primesOverFinset_under {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P ∈ IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F) := by
  -- Since P is a prime ideal in O_F, we have that P is maximal in O_F.
  have hP_max : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  rw [ IsDedekindDomain.mem_primesOverFinset_iff ];
  · constructor;
    · exact hP;
    · constructor;
      rfl;
  · exact Ideal.under_ne_bot (A := ℤ) hP0

/-
[foundational] The coordinate of a nonzero prime ideal is `< [F:ℚ]`.
-/
private theorem primeCoord_lt {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    primeCoord F P < Module.finrank ℚ F := by
  have hmax : (Ideal.under ℤ P).IsMaximal :=
    Ideal.IsPrime.isMaximal (IsPrime.under ℤ P) (Ideal.under_ne_bot (A := ℤ) hP0)
  calc primeCoord F P
      < (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList.length := by
        rw [primeCoord]
        exact List.idxOf_lt_length_iff.mpr
          (Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0))
    _ = (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).card := Finset.length_toList _
    _ ≤ Module.finrank ℚ F :=
        Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F (Ideal.under_ne_bot (A := ℤ) hP0)

/-
[foundational] `absNormUnder` injectivity: equal `absNormUnder` means the primes lie
over the same rational prime, hence have the same `IsDedekindDomain.primesOverFinset`.
-/
omit [NumberField F] in
private theorem under_eq_of_absNormUnder_eq {P Q : Ideal (𝓞 F)}
    (hr : absNormUnder F P = absNormUnder F Q) :
    Ideal.under ℤ P = Ideal.under ℤ Q := by
  have hr' : Ideal.absNorm (Ideal.under ℤ P) = Ideal.absNorm (Ideal.under ℤ Q) := hr
  rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P),
    ← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ Q), hr']

/-
[foundational] Two nonzero primes over the same rational prime with the same
coordinate are equal.
-/
private theorem prime_eq_of_absNormUnder_eq_of_primeCoord_eq {P Q : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥)
    (hr : absNormUnder F P = absNormUnder F Q)
    (hc : primeCoord F P = primeCoord F Q) : P = Q := by
  have hUeq : Ideal.under ℤ P = Ideal.under ℤ Q := under_eq_of_absNormUnder_eq F hr
  set l := (IsDedekindDomain.primesOverFinset (Ideal.under ℤ P) (𝓞 F)).toList with hl
  have hPl : P ∈ l := Finset.mem_toList.mpr (mem_primesOverFinset_under F hP hP0)
  have hQl : Q ∈ l := by
    rw [hl, hUeq]
    exact Finset.mem_toList.mpr (mem_primesOverFinset_under F hQ hQ0)
  have hidx : l.idxOf P = l.idxOf Q := by
    have hP' : l.idxOf P = primeCoord F P := by rw [primeCoord, hl]
    have hQ' : l.idxOf Q = primeCoord F Q := by rw [primeCoord, hl, hUeq]
    rw [hP', hQ', hc]
  exact (List.idxOf_inj hPl).mp hidx

/-
[foundational] Each coordinate of the encoding of a nonzero ideal is positive.
-/
private theorem encodeIdeal_pos {I : Ideal (𝓞 F)}
    (i : Fin (Module.finrank ℚ F)) : 0 < encodeIdeal F I i := by
  refine Finset.prod_pos fun P hP => ?_
  rw [Finset.mem_filter, Multiset.mem_toFinset] at hP
  have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP.1)
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP.1
  haveI := hPp
  haveI : NeZero P := ⟨hP0⟩
  exact pow_pos (by simpa [absNormUnder] using (Nat.absNorm_under_prime P).pos) _

/-
Regrouping: the product of all coordinates is the product over all prime
factors of `(absNormUnder P) ^ (mult of P)`.
-/
private theorem prod_encodeIdeal_eq {I : Ideal (𝓞 F)} :
    ∏ i, encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset,
        (absNormUnder F P) ^ ((normalizedFactors I).count P) := by
  have h_sum : ∏ i : Fin (Module.finrank ℚ F), encodeIdeal F I i =
      ∏ P ∈ (normalizedFactors I).toFinset, ∏ i : Fin (Module.finrank ℚ F),
        if primeCoord F P = i.val then
          (absNormUnder F P) ^ ((normalizedFactors I).count P)
        else 1 := by
    rw [Finset.prod_comm, Finset.prod_congr rfl]
    unfold encodeIdeal
    simp +decide [Finset.prod_ite]
  rw [h_sum]
  refine Finset.prod_congr rfl fun P hP => ?_
  have hPp : P.IsPrime :=
    isPrime_of_prime (prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
  rw [Fintype.prod_eq_single ⟨primeCoord F P, primeCoord_lt F hPp hP0⟩]
  · simp
  · intro i hi
    have hcoord : primeCoord F P ≠ i.val := by
      intro hval
      exact hi (Fin.ext hval.symm)
    simp [hcoord]

/-
The product of the encoding coordinates is at most `absNorm I`.
-/
private theorem prod_encodeIdeal_le_absNorm {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∏ i, encodeIdeal F I i ≤ Ideal.absNorm I := by
  rw [prod_encodeIdeal_eq F]
  have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
      (Ideal.absNorm P) ^ ((normalizedFactors I).count P) ≤ Ideal.absNorm I := by
    have h_prod_le : ∏ P ∈ (normalizedFactors I).toFinset,
          (Ideal.absNorm P) ^ ((normalizedFactors I).count P)
        = Ideal.absNorm (∏ P ∈ (normalizedFactors I).toFinset,
          P ^ ((normalizedFactors I).count P)) := by
      simp only [map_prod, map_pow]
    have hI_eq : ∏ P ∈ (normalizedFactors I).toFinset,
        P ^ ((normalizedFactors I).count P) = I := by
      rw [← Finset.prod_multiset_count, Ideal.prod_normalizedFactors_eq_self hI]
    exact le_of_eq (h_prod_le.trans (by rw [hI_eq]))
  refine le_trans ?_ h_prod_le
  gcongr with Q hQ
  have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hQ)
  exact Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hQ0))
    (by simpa [absNormUnder] using Int.absNorm_under_dvd_absNorm Q)

/-
Recovery: the multiplicity of a prime `P` in `I` is the `absNormUnder P`-adic
valuation of the `primeCoord P` coordinate of the encoding.
-/
private theorem count_eq_padicValNat {I : Ideal (𝓞 F)} {P : Ideal (𝓞 F)}
    (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (normalizedFactors I).count P =
      padicValNat (absNormUnder F P)
        (encodeIdeal F I ⟨primeCoord F P, primeCoord_lt F hP hP0⟩) := by
  classical
  haveI := hP
  haveI : NeZero P := ⟨hP0⟩
  have hpp : (absNormUnder F P).Prime := by simpa [absNormUnder] using Nat.absNorm_under_prime P
  have hfact : ∀ Q ∈ (normalizedFactors I).toFinset.filter
      (fun Q => primeCoord F Q = primeCoord F P),
      (absNormUnder F Q) ^ ((normalizedFactors I).count Q) ≠ 0 := by
    intro Q hQ
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp : Q.IsPrime := isPrime_of_prime (prime_of_normalized_factor Q hQ.1)
    have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQ.1
    haveI := hQp
    haveI : NeZero Q := ⟨hQ0⟩
    exact pow_ne_zero _ (by simpa [absNormUnder] using (Nat.absNorm_under_prime Q).pos.ne')
  rw [eq_comm, ← Nat.factorization_def _ hpp]
  simp only [encodeIdeal]
  rw [Nat.factorization_prod hfact]
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single P]
  · rw [hpp.factorization_pow, Finsupp.single_apply]
    simp
  · intro Q hQ hQP
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hQ
    have hQp : Q.IsPrime := isPrime_of_prime (prime_of_normalized_factor Q hQ.1)
    have hQ0 : Q ≠ ⊥ := ne_zero_of_mem_normalizedFactors hQ.1
    have hrb : absNormUnder F Q ≠ absNormUnder F P := fun h =>
      hQP (prime_eq_of_absNormUnder_eq_of_primeCoord_eq F hQp hQ0 hP hP0 h hQ.2)
    haveI := hQp
    haveI : NeZero Q := ⟨hQ0⟩
    have hQbelow : (absNormUnder F Q).Prime := by
      simpa [absNormUnder] using Nat.absNorm_under_prime Q
    rw [hQbelow.factorization_pow, Finsupp.single_apply]
    simp [hrb]
  · intro hPnot
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hPnot
    rw [not_and] at hPnot
    have hPmem : P ∉ normalizedFactors I := fun hmem => (hPnot hmem) rfl
    rw [Multiset.count_eq_zero_of_notMem hPmem]
    simp

/-
[foundational] The encoding is injective on nonzero ideals.
-/
private theorem encodeIdeal_injOn :
    Set.InjOn (encodeIdeal F) {I : Ideal (𝓞 F) | I ≠ ⊥} := by
  intro I hI J hJ h_eq
  -- The multiplicity of every nonzero prime is recovered from the encoding, so it agrees.
  have hcount : ∀ {P : Ideal (𝓞 F)}, P.IsPrime → P ≠ ⊥ →
      (normalizedFactors I).count P = (normalizedFactors J).count P := by
    intro P hPp hP0
    rw [count_eq_padicValNat F hPp hP0, count_eq_padicValNat F hPp hP0, h_eq]
  -- Hence the factor multisets agree, hence the ideals.
  have hms : normalizedFactors I = normalizedFactors J := by
    refine Multiset.ext.mpr fun P => ?_
    by_cases hmem : P ∈ normalizedFactors I ∨ P ∈ normalizedFactors J
    · obtain hP | hP := hmem
      · have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP)
        have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
        exact hcount hPp hP0
      · have hPp : P.IsPrime := isPrime_of_prime (prime_of_normalized_factor P hP)
        have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
        exact hcount hPp hP0
    · rw [not_or] at hmem
      rw [Multiset.count_eq_zero_of_notMem hmem.1, Multiset.count_eq_zero_of_notMem hmem.2]
  rw [← Ideal.prod_normalizedFactors_eq_self hI, ← Ideal.prod_normalizedFactors_eq_self hJ, hms]

end

end RankinCount

open _root_.NumberField in
/-- The nonzero integral ideals of norm at most `X` inject into the positive
`[F:ℚ]`-tuples whose product is at most `X`. The encoding assigns each prime ideal `P`
one coordinate and contributes `absNorm (Ideal.under ℤ P) ^ count` there; the coordinate
product is bounded by `Ideal.absNorm I`, and injectivity follows by recovering each count
from a `padicValNat`. -/
private theorem ideal_ncard_le_prodLeTuples_ncard (F : Type*) [Field F] [NumberField F]
    {X : ℝ} :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard ≤
      (prodLeTuples (Module.finrank ℚ F) X).ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (encodeIdeal F) ?_ ?_ (prodLeTuples_finite _ _)
  · rintro I ⟨hI0, hIX⟩
    refine ⟨fun i => encodeIdeal_pos F i, ?_⟩
    calc (∏ i, (encodeIdeal F I i : ℝ))
        = ((∏ i, encodeIdeal F I i : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (Ideal.absNorm I : ℝ) := by exact_mod_cast prod_encodeIdeal_le_absNorm F hI0
      _ ≤ X := hIX
  · intro I hI J hJ h
    exact encodeIdeal_injOn F hI.1 hJ.1 h

open _root_.NumberField in
/-- In any number field `F`, the set of nonzero integral ideals with norm at most `X` is
finite, and for `X ≥ 1` its cardinality is at most `X² * 2^[F:ℚ]`. -/
theorem card_ideal_absNorm_le (F : Type*) [Field F] [NumberField F]
    {X : ℝ} (hX : 1 ≤ X) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.Finite ∧
      (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
        X ^ 2 * 2 ^ Module.finrank ℚ F := by
  refine ⟨?_, ?_⟩
  · apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le ⌊X⌋₊)
    rintro I ⟨-, hI⟩
    exact Nat.le_floor hI
  · calc ((({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}).ncard : ℝ))
        ≤ ((prodLeTuples (Module.finrank ℚ F) X).ncard : ℝ) := by
          exact_mod_cast ideal_ncard_le_prodLeTuples_ncard F (X := X)
      _ ≤ X ^ 2 * 2 ^ Module.finrank ℚ F := prodLeTuples_ncard_le _ hX


/-! ## Consumer forms

These are direct corollaries of `card_ideal_absNorm_le`, packaging its real norm bound as the
natural-number and degree-monotone forms that later effective estimates carry. -/

section Consumer

open scoped NumberField

open Module _root_.NumberField

/-- The set of nonzero integral ideals of `𝓞 F` with natural norm at most `N`. -/
private abbrev idealsWithAbsNormNatLe (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}

/-- The set of nonzero integral ideals of `𝓞 F` with real norm at most `X`. -/
private abbrev idealsWithAbsNormRealLe (F : Type*) [Field F] [NumberField F] (X : ℝ) :
    Set (Ideal (𝓞 F)) :=
  {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}

private theorem idealsWithAbsNormNatLe_finite (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    (idealsWithAbsNormNatLe F N).Finite :=
  (Ideal.finite_setOf_absNorm_le N).subset fun _ hI => hI.2

private theorem idealsWithAbsNormNatLe_eq_real (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    idealsWithAbsNormNatLe F N = idealsWithAbsNormRealLe F (N : ℝ) := by
  ext I
  exact and_congr_right fun _ => by exact_mod_cast (Iff.rfl : Ideal.absNorm I ≤ N ↔ _)

private theorem idealsWithAbsNormNatLe_zero (F : Type*) [Field F] [NumberField F] :
    idealsWithAbsNormNatLe F 0 = ∅ := by
  ext I
  simp only [idealsWithAbsNormNatLe, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hI0 hI
  exact hI0 (Ideal.absNorm_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hI))

private theorem ncard_idealsWithAbsNormNatLe_real_le (F : Type*) [Field F] [NumberField F]
    {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((idealsWithAbsNormNatLe F N).ncard : ℝ) ≤ (N : ℝ) ^ 2 * 2 ^ finrank ℚ F := by
  rw [idealsWithAbsNormNatLe_eq_real F N]
  simpa [idealsWithAbsNormRealLe] using (card_ideal_absNorm_le F (X := (N : ℝ)) hN).2

/-- **Natural-number ideal count.** The number of nonzero integral ideals of `𝓞 F` with norm at
most `N` is at most `N² * 2^[F:ℚ]`. -/
theorem ncard_ideal_absNorm_le_nat (F : Type*) [Field F] [NumberField F]
    (N : ℕ) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤
      N ^ 2 * 2 ^ finrank ℚ F := by
  suffices (idealsWithAbsNormNatLe F N).ncard ≤ N ^ 2 * 2 ^ finrank ℚ F by
    simpa [idealsWithAbsNormNatLe] using this
  rcases N with _ | N
  · rw [idealsWithAbsNormNatLe_zero F]
    simp
  have hreal : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
  have hcount' := ncard_idealsWithAbsNormNatLe_real_le F (N := N + 1) hreal
  exact_mod_cast hcount'

/-- If `1 ≤ X` and `[F : ℚ] ≤ n`, then the number of nonzero integral ideals of norm at most
`X` is at most `X² * 2^n`. This is the degree-monotone form of
`TauCeti.NumberField.card_ideal_absNorm_le`. -/
theorem ncard_ideal_absNorm_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {X : ℝ} {n : ℕ} (hX : 1 ≤ X) (hn : finrank ℚ F ≤ n) :
    (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ)) ≤
      X ^ 2 * 2 ^ n := by
  calc
    (({I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ X}.ncard : ℝ))
        ≤ X ^ 2 * 2 ^ finrank ℚ F := (card_ideal_absNorm_le F hX).2
    _ ≤ X ^ 2 * 2 ^ n := by
      have hpow : (2 : ℝ) ^ finrank ℚ F ≤ 2 ^ n := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg X)

/-- Monotone natural-number ideal count: if all ideals under consideration have norm at most
`N`, and `N ≤ B`, and `[F : ℚ] ≤ n`, then there are at most `B² * 2^n` of them. -/
theorem ncard_ideal_absNorm_le_of_nat_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {N B n : ℕ}
    (hN : N ≤ B) (hn : finrank ℚ F ≤ n) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤ B ^ 2 * 2 ^ n := by
  calc
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard
        ≤ {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ B}.ncard := by
          exact Set.ncard_le_ncard
            (by rintro I ⟨hI0, hI⟩; exact ⟨hI0, hI.trans hN⟩)
            (idealsWithAbsNormNatLe_finite F B)
    _ ≤ B ^ 2 * 2 ^ finrank ℚ F := ncard_ideal_absNorm_le_nat F B
    _ ≤ B ^ 2 * 2 ^ n := by
      exact Nat.mul_le_mul_left (B ^ 2) (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn)

/-- If `[F : ℚ] ≤ n`, then the number of nonzero integral ideals of norm at most `N` is at most
`N² * 2^n`. -/
theorem ncard_ideal_absNorm_le_nat_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {N n : ℕ}
    (hn : finrank ℚ F ≤ n) :
    {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ Ideal.absNorm I ≤ N}.ncard ≤ N ^ 2 * 2 ^ n :=
  ncard_ideal_absNorm_le_of_nat_le_of_finrank_le F le_rfl hn

end Consumer

end TauCeti.NumberField
