/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.NumberTheory.Multiquadratic.Quadratic.RamifiedPrime.Independence
import TauCeti.NumberTheory.NumberField.ClassGroupElementaryTwoQuotient
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification

/-!
# The class number of `ℚ(√-21)`

This file proves that the imaginary quadratic field `ℚ(√-21)` has class number `4`, completing
the class-number calculation in the second genus-field worked example of the multiquadratic
roadmap.

Minkowski's theorem gives every ideal class an integral representative of norm less than `6`.
Norms `2` and `3` give the unique primes above the ramified rational primes `2` and `3`; an ideal
of norm `4` is the square of the prime above `2`, hence principal; and the primes above `5`
contribute at most two further classes. Thus the class number is at most `5`.

For the lower bound, the independent classes of the three ramified primes `2`, `3`, and `7`
give `2`-rank at least `2`, so the class number is divisible by `4`. The only multiple of `4`
between `4` and `5` is `4`.

The main theorem is stated for any number field with an integral generator of minimal polynomial
`X² + 21`; the final theorem applies it to Mathlib's `AdjoinRoot` model.

The argument is the standard Minkowski computation; see D. A. Cox, *Primes of the Form
x² + ny²*, Chapter 5.

## Main results

* `TauCeti.NumberField.classNumber_eq_four_of_minpoly_eq_X_sq_add_twenty_one`: every
  presentation of `ℚ(√-21)` by an integral generator has class number four.
* `TauCeti.NumberField.classNumber_adjoinRoot_sqrt_neg_twenty_one_eq_four`: the result for the
  concrete `AdjoinRoot (X² + 21)` model.
-/

public section

open Ideal Module NumberField Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The radicand `-21` is squarefree. -/
private theorem squarefree_neg_twenty_one : Squarefree (-21 : ℤ) := by
  rw [← Int.squarefree_natAbs]
  change Squarefree (21 : ℕ)
  simpa using (Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).mpr
    ⟨(by decide : Nat.Prime 3).squarefree, (by decide : Nat.Prime 7).squarefree⟩

/-- The discriminant of a presentation of `ℚ(√-21)` is `-84`. -/
private theorem discr_eq_neg_eighty_four
    (hmin : minpoly ℤ θ = X ^ 2 - C (-21 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    NumberField.discr K = -84 := by
  simpa using discr_eq_four_mul_of_mod_four_ne_one hmin hgen
    squarefree_neg_twenty_one (by norm_num)

/-- The Minkowski bound of `ℚ(√-21)` is strictly less than `6`. -/
private theorem minkowski_bound_lt_six
    (hmin : minpoly ℤ θ = X ^ 2 - C (-21 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |(NumberField.discr K : ℝ)|) < 6 := by
  have hfin : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  have _ : IsTotallyComplex K :=
    isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin (by norm_num)
  have hreal : InfinitePlace.nrRealPlaces K = 0 :=
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  have hcomplex : InfinitePlace.nrComplexPlaces K = 1 := by
    have hsignature := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hreal, hfin] at hsignature
    omega
  have hdisc := discr_eq_neg_eighty_four hmin hgen
  have hsqrt : Real.sqrt 84 < 46 / 5 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [hcomplex, hfin, hdisc]
  norm_num [abs_of_nonneg]
  calc
    4 / Real.pi * (1 / 2 * Real.sqrt 84) = 2 * Real.sqrt 84 / Real.pi := by ring
    _ < 6 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_d2]

/-- An ideal of prime norm `p` is the unique prime above `p` when `p` ramifies in a quadratic
number field. -/
private theorem eq_primeAbove_of_absNorm_eq {p : ℕ} (hp : p.Prime)
    (hfin : finrank ℚ K = 2) (hram : p ∈ ramifiedPrimes K)
    (P I : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hI : I.absNorm = p) : I = P := by
  have hirr : Irreducible I.absNorm := by rw [hI]; exact hp
  let _ : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm hirr
  have hprimeNorm : I.absNorm.Prime := by rw [hI]; exact hp
  let _ : I.LiesOver (span {(p : ℤ)}) := ⟨by
    simpa [hI, Ideal.under_def] using Ideal.span_singleton_absNorm (I := I) hprimeNorm⟩
  have hmem : I ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := ⟨inferInstance, inferInstance⟩
  have hset : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) = {P} :=
    primesOver_eq_singleton_of_mem_ramifiedPrimes hfin hram P
  have : I ∈ ({P} : Set (Ideal (𝓞 K))) := hset ▸ hmem
  simpa using this

/-- In a quadratic number field where `2` ramifies, every ideal of norm `4` is principal. -/
private theorem isPrincipal_of_absNorm_eq_four (hfin : finrank ℚ K = 2)
    (hram : 2 ∈ ramifiedPrimes K) (I : Ideal (𝓞 K)) (hI : I.absNorm = 4) :
    Submodule.IsPrincipal I := by
  have htwo : 2 ∣ I.absNorm := by rw [hI]; norm_num
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' Nat.prime_two I htwo
  let _ : P.IsPrime := hPmax.isPrime
  let _ : P.LiesOver (span {(2 : ℤ)}) := ⟨hPunder.symm⟩
  obtain ⟨J, hIJ⟩ := hPdvd
  have hPnorm : P.absNorm = 2 := absNorm_eq_of_mem_ramifiedPrimes hfin hram P
  have hJnorm : J.absNorm = 2 := by
    have hnorm := congrArg Ideal.absNorm hIJ
    rw [map_mul, hI, hPnorm] at hnorm
    omega
  have hJP : J = P :=
    eq_primeAbove_of_absNorm_eq Nat.prime_two hfin hram P J hJnorm
  rw [hIJ, hJP, ← pow_two, ← map_span_eq_sq_of_mem_ramifiedPrimes hfin hram P,
    Ideal.map_span, Set.image_singleton]
  exact ⟨algebraMap ℤ (𝓞 K) 2, rfl⟩

/-- **The class number of `ℚ(√-21)` is four.** This presentation-independent statement assumes
an integral generator with minimal polynomial `X² + 21` which generates the field over `ℚ`. -/
theorem classNumber_eq_four_of_minpoly_eq_X_sq_add_twenty_one
    (hmin : minpoly ℤ θ = X ^ 2 - C (-21 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.classNumber K = 4 := by
  classical
  have hfin : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  have hdisc := discr_eq_neg_eighty_four hmin hgen
  have hram_two : 2 ∈ ramifiedPrimes K := by
    rw [mem_ramifiedPrimes_iff_dvd_discr (K := K) Nat.prime_two, hdisc]
    norm_num
  have hram_three : 3 ∈ ramifiedPrimes K := by
    rw [mem_ramifiedPrimes_iff_dvd_discr (K := K) (by decide), hdisc]
    norm_num
  let p2 : Ideal ℤ := span {(2 : ℤ)}
  let p3 : Ideal ℤ := span {(3 : ℤ)}
  let p5 : Ideal ℤ := span {(5 : ℤ)}
  let _ : p2.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr
    (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  let _ : p3.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by decide))
  let _ : p5.IsPrime := (Ideal.span_singleton_prime (by norm_num)).mpr
    (Int.prime_iff_natAbs_prime.mpr (by decide))
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨⟨P2, hP2prime, hP2over⟩⟩ :=
    (inferInstance : Nonempty (p2.primesOver (𝓞 K)))
  obtain ⟨⟨P3, hP3prime, hP3over⟩⟩ :=
    (inferInstance : Nonempty (p3.primesOver (𝓞 K)))
  let _ : P2.IsPrime := hP2prime
  let _ : P2.LiesOver p2 := hP2over
  let _ : P3.IsPrime := hP3prime
  let _ : P3.LiesOver p3 := hP3over
  have hP2ne : P2 ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := p2) (by simp [p2]) P2
  have hP3ne : P3 ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := p3) (by simp [p3]) P3
  let P20 : nonZeroDivisors (Ideal (𝓞 K)) :=
    ⟨P2, mem_nonZeroDivisors_of_ne_zero hP2ne⟩
  let P30 : nonZeroDivisors (Ideal (𝓞 K)) :=
    ⟨P3, mem_nonZeroDivisors_of_ne_zero hP3ne⟩
  have hp5ne : p5 ≠ ⊥ := by simp [p5]
  let _ : p5.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp5ne
  let primesFive : Finset (Ideal (𝓞 K)) :=
    IsDedekindDomain.primesOverFinset p5 (𝓞 K)
  let classFive : {P // P ∈ primesFive} → ClassGroup (𝓞 K) := fun P =>
    ClassGroup.mk0 ⟨P.1, mem_nonZeroDivisors_of_ne_zero (by
      have hpdata := (IsDedekindDomain.mem_primesOverFinset_iff hp5ne (𝓞 K)).mp P.2
      let _ : P.1.LiesOver p5 := hpdata.2
      rw [Ideal.zero_eq_bot]
      exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := p5) hp5ne P.1)⟩
  let fiveClasses : Finset (ClassGroup (𝓞 K)) := primesFive.attach.image classFive
  let candidates : Finset (ClassGroup (𝓞 K)) :=
    insert 1 (insert (ClassGroup.mk0 P20) (insert (ClassGroup.mk0 P30) fiveClasses))
  have hclasses : ∀ C : ClassGroup (𝓞 K), C ∈ candidates := by
    intro C
    obtain ⟨I, hIC, hIle⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hIlt : (I.1.absNorm : ℝ) < 6 := hIle.trans_lt (minkowski_bound_lt_six hmin hgen)
    have hIleFive : I.1.absNorm ≤ 5 := by
      exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast hIlt))
    have hIpos : 0 < I.1.absNorm := absNorm_pos_of_nonZeroDivisors I
    interval_cases hnorm : I.1.absNorm <;> simp_all only [Nat.reduceLeDiff]
    · simp only [candidates, Finset.mem_insert]
      left
      rw [← hIC]
      exact (ClassGroup.mk0_eq_one_iff I.2).mpr <| by
        rw [Ideal.absNorm_eq_one_iff.mp hnorm]
        exact top_isPrincipal
    · simp only [candidates, Finset.mem_insert]
      right; left
      rw [← hIC]
      have hIP : I.1 = P2 := eq_primeAbove_of_absNorm_eq Nat.prime_two hfin hram_two P2 I.1 hnorm
      apply congrArg ClassGroup.mk0
      exact Subtype.ext hIP
    · simp only [candidates, Finset.mem_insert]
      right; right; left
      rw [← hIC]
      have hIP : I.1 = P3 :=
        eq_primeAbove_of_absNorm_eq (by decide) hfin hram_three P3 I.1 hnorm
      apply congrArg ClassGroup.mk0
      exact Subtype.ext hIP
    · simp only [candidates, Finset.mem_insert]
      left
      rw [← hIC]
      exact (ClassGroup.mk0_eq_one_iff I.2).mpr
        (isPrincipal_of_absNorm_eq_four hfin hram_two I.1 hnorm)
    · simp only [candidates, Finset.mem_insert]
      right; right; right
      have hprimeNorm : I.1.absNorm.Prime := by rw [hnorm]; decide
      have hprime : I.1.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprimeNorm
      have hover : I.1.LiesOver p5 := ⟨by
        simpa [p5, hnorm, Ideal.under_def] using
          Ideal.span_singleton_absNorm (I := I.1) hprimeNorm⟩
      have hmem : I.1 ∈ primesFive := by
        rw [IsDedekindDomain.mem_primesOverFinset_iff hp5ne]
        exact ⟨hprime, hover⟩
      rw [← hIC]
      refine Finset.mem_image.mpr ⟨⟨I.1, hmem⟩, Finset.mem_attach _ _, ?_⟩
      apply congrArg ClassGroup.mk0
      rfl
  have hupper : NumberField.classNumber K ≤ 5 := by
    rw [NumberField.classNumber]
    calc
      Fintype.card (ClassGroup (𝓞 K)) = Finset.univ.card := by simp
      _ ≤ candidates.card := Finset.card_le_card fun C _ => hclasses C
      _ ≤ 3 + fiveClasses.card := by
        dsimp only [candidates]
        calc
          (insert 1 (insert (ClassGroup.mk0 P20)
              (insert (ClassGroup.mk0 P30) fiveClasses))).card
              ≤ (insert (ClassGroup.mk0 P20)
                  (insert (ClassGroup.mk0 P30) fiveClasses)).card + 1 :=
                Finset.card_insert_le _ _
          _ ≤ ((insert (ClassGroup.mk0 P30) fiveClasses).card + 1) + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ ≤ ((fiveClasses.card + 1) + 1) + 1 :=
            Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
          _ = 3 + fiveClasses.card := by omega
      _ ≤ 3 + primesFive.card := by
        apply Nat.add_le_add_left
        dsimp only [fiveClasses]
        simpa only [Finset.card_attach] using
          (Finset.card_image_le : (primesFive.attach.image classFive).card ≤
            primesFive.attach.card)
      _ ≤ 5 := by
        have hcard : primesFive.card ≤ finrank ℚ K := by
          calc
            primesFive.card = ∑ _q : p5.primesOver (𝓞 K), 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
                ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
                ← IsDedekindDomain.coe_primesOverFinset hp5ne (𝓞 K),
                Set.ncard_coe_finset]
            _ ≤ ∑ q : p5.primesOver (𝓞 K),
                q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
              Finset.sum_le_sum fun q _ => Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
                  (Ideal.inertiaDeg_pos q.1 ℤ).ne')
            _ = finrank ℤ (𝓞 K) :=
              Ideal.sum_ramification_inertia_eq_finrank p5 (𝓞 K)
            _ = finrank ℚ K := NumberField.RingOfIntegers.rank K
        omega
  have hram_card : 3 ≤ (ramifiedPrimes K).ncard := by
    have hsubset : ({2, 3, 7} : Set ℕ) ⊆ ramifiedPrimes K := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact hram_two
      · exact hram_three
      · rw [mem_ramifiedPrimes_iff_dvd_discr (K := K) (by decide), hdisc]
        norm_num
    calc
      3 = ({2, 3, 7} : Set ℕ).ncard := by norm_num
      _ ≤ (ramifiedPrimes K).ncard :=
        Set.ncard_le_ncard hsubset (NumberField.finite_ramifiedPrimes (K := K))
  have hrank : 2 ≤ TauCeti.ClassGroup.twoRank (𝓞 K) :=
    le_trans (by omega : 2 ≤ (ramifiedPrimes K).ncard - 1)
      (TauCeti.Multiquadratic.ncard_ramifiedPrimes_sub_one_le_twoRank
        hmin hgen squarefree_neg_twenty_one (by norm_num))
  have hfourdvd : 4 ∣ NumberField.classNumber K := by
    apply dvd_trans (b := 2 ^ TauCeti.ClassGroup.twoRank (𝓞 K))
    · change 2 ^ 2 ∣ 2 ^ TauCeti.ClassGroup.twoRank (𝓞 K)
      exact pow_dvd_pow 2 hrank
    · exact NumberField.two_pow_classGroupTwoRank_dvd_classNumber K
  have hlower : 4 ≤ NumberField.classNumber K := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ TauCeti.ClassGroup.twoRank (𝓞 K) :=
        pow_le_pow_right' (by norm_num) hrank
      _ ≤ NumberField.classNumber K :=
        NumberField.two_pow_classGroupTwoRank_le_classNumber K
  obtain ⟨n, hn⟩ := hfourdvd
  omega

local instance irreducible_sqrt_neg_twenty_one :
    Fact (Irreducible (X ^ 2 - C (-21 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    (fun q _ => by nlinarith [sq_nonneg q])⟩

/-- **Worked example.** The concrete number field `AdjoinRoot (X² + 21)`, modelling `ℚ(√-21)`,
has class number `4`. -/
@[simp]
theorem classNumber_adjoinRoot_sqrt_neg_twenty_one_eq_four :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (-21 : ℚ))) = 4 := by
  let K := AdjoinRoot (X ^ 2 - C (-21 : ℚ))
  let x : K := AdjoinRoot.root (X ^ 2 - C (-21 : ℚ))
  have hx : x ^ 2 = algebraMap ℤ K (-21 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root (X ^ 2 - C (-21 : ℚ))
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero] at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ K]
    norm_num
  let θ : 𝓞 K := integralSqrt hx
  have hmin : minpoly ℤ θ = X ^ 2 - C (-21 : ℤ) :=
    minpoly_integralSqrt hx (fun ⟨q, hq⟩ => by
      norm_num at hq
      nlinarith [mul_self_nonneg q])
  have hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    have hfne : (X ^ 2 - C (-21 : ℚ)) ≠ 0 :=
      (monic_X_pow_sub_C (-21 : ℚ) (by norm_num)).ne_zero
    have hpb := (AdjoinRoot.powerBasis (f := X ^ 2 - C (-21 : ℚ)) hfne).adjoin_gen_eq_top
    rw [AdjoinRoot.powerBasis_gen] at hpb
    have hθx : (θ : K) = x := algebraMap_integralSqrt hx
    rw [hθx]
    exact hpb
  exact classNumber_eq_four_of_minpoly_eq_X_sq_add_twenty_one hmin hgen

end TauCeti.NumberField
