/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.PrimePsi
public import TauCeti.Algebra.Group.Conj
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# Frobenius von Mangoldt coefficients

For a conjugacy class `C` in the Galois group of a finite Galois extension `L / K`, this file
defines the von Mangoldt coefficient and summatory functions restricted to `C`. A prime power
`𝔭 ^ j` belongs to the `C`-fibre when the `j`-th power of the Artin class of `𝔭` is `C`.
Consequently a prime whose Artin class is not `C` can still contribute through a higher power.

The definitions retain only unramified primes: the Artin symbol is never evaluated at a ramified
prime. The exponent-one terms form `frobeniusTheta`; all higher prime powers are dominated by the
unrestricted higher-prime-power weight from the arithmetic Dirichlet-series development, hence
their contribution is `o(x)`.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimePowerSet`: prime powers selected by the powered Artin
  class.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff`: the corresponding nonnegative arithmetic
  function, regrouped by absolute norm.
* `NumberField.Chebotarev.frobeniusPsi` and `NumberField.Chebotarev.frobeniusTheta`: the weighted
  prime-power and prime summatory functions.

## Main results

* `NumberField.Chebotarev.frobeniusPsi_eq_sum_range`: `frobeniusPsi` is the inclusive partial sum
  of `frobeniusVonMangoldtCoeff`.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory`: their
  difference is exactly the contribution from exponents at least two.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_le`: that difference is bounded by
  the unrestricted higher-prime-power tail.
* `NumberField.Chebotarev.isLittleO_frobeniusPsi_sub_frobeniusTheta`: this difference is `o(x)`.

The coefficient convention follows Neukirch, *Algebraic Number Theory*, Chapter VII. The
construction reuses Tau Ceti's generic prime-power counting and removal estimates.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- The powered-class convention follows `TauCetiRoadmap/Chebotarev/Suggested.lean`.
variable (K L) in
/-- The prime powers whose powered Artin class is `C`. A prime power `𝔭 ^ j` is included when
`𝔭` is unramified in `L` and `(artinSymbol 𝔭) ^ j = C`. -/
def frobeniusPrimePowerSet (C : ConjClasses (L ≃ₐ[K] L)) : Set (IdealPrimePower K) :=
  {A | ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q,
    artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C}

/-- Membership in `frobeniusPrimePowerSet`, unfolded. -/
@[simp]
theorem mem_frobeniusPrimePowerSet_iff {A : IdealPrimePower K}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    A ∈ frobeniusPrimePowerSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
          Algebra.IsUnramifiedAt (𝓞 K) Q,
        artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  Iff.rfl

/-- With an unramifiedness proof fixed, membership in the powered Frobenius fibre is the stated
equality of conjugacy classes. In particular, membership is independent of that proof. -/
theorem mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    A ∈ frobeniusPrimePowerSet K L C ↔
      artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.
/-- At exponent one, the powered Frobenius fibre is the ordinary Frobenius prime set. -/
theorem ofPrime_mem_frobeniusPrimePowerSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    IdealPrimePower.ofPrime 𝔭 ∈ frobeniusPrimePowerSet K L C ↔
      𝔭 ∈ frobeniusPrimeSet K L C := by
  simp only [mem_frobeniusPrimePowerSet_iff, primePowerBase_ofPrime,
    primePowerExponent_ofPrime, ConjClasses.pow_one, mem_frobeniusPrimeSet_iff]

variable (K L) in
/-- The logarithmic weight on prime powers selected by their powered Artin class. -/
noncomputable def frobeniusPrimePowerWeight (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) : ℝ :=
  (frobeniusPrimePowerSet K L C).indicator primePowerWeight A

/-- A prime power in the `C`-fibre has weight `log N(𝔭)`. -/
theorem frobeniusPrimePowerWeight_of_mem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∈ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A := by
  rw [frobeniusPrimePowerWeight, Set.indicator_of_mem hA]

/-- A prime power whose powered Artin class is `C` contributes its full logarithmic weight.
This exposes the power in the filter: the unpowered Artin class need not equal `C`. -/
theorem frobeniusPrimePowerWeight_of_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {C : ConjClasses (L ≃ₐ[K] L)}
    (hC : artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A :=
  frobeniusPrimePowerWeight_of_mem
    ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur C).mpr hC)

/-- A prime power outside the `C`-fibre has weight zero. -/
theorem frobeniusPrimePowerWeight_of_notMem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∉ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = 0 :=
  Set.indicator_of_notMem hA _

/-- The powered Frobenius von Mangoldt weight is nonnegative. -/
theorem frobeniusPrimePowerWeight_nonneg (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) : 0 ≤ frobeniusPrimePowerWeight K L C A :=
  Set.indicator_nonneg (fun _ _ ↦ primePowerWeight_nonneg _) A

/-- The powered Frobenius weight is bounded by the unrestricted von Mangoldt weight. -/
theorem frobeniusPrimePowerWeight_le (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) : frobeniusPrimePowerWeight K L C A ≤ primePowerWeight A :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ primePowerWeight_nonneg A)

/-- On a prime, the powered Frobenius weight is the usual logarithmic indicator of the
unpowered Frobenius prime set. -/
@[simp]
theorem frobeniusPrimePowerWeight_ofPrime (C : ConjClasses (L ≃ₐ[K] L))
    (𝔭 : HeightOneSpectrum (𝓞 K)) :
    frobeniusPrimePowerWeight K L C (IdealPrimePower.ofPrime 𝔭) =
      (frobeniusPrimeSet K L C).indicator
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal)) 𝔭 := by
  by_cases h𝔭 : 𝔭 ∈ frobeniusPrimeSet K L C
  · rw [Set.indicator_of_mem h𝔭,
      frobeniusPrimePowerWeight_of_mem (ofPrime_mem_frobeniusPrimePowerSet_iff.mpr h𝔭),
      primePowerWeight_ofPrime]
  · rw [Set.indicator_of_notMem h𝔭,
      frobeniusPrimePowerWeight_of_notMem (mt ofPrime_mem_frobeniusPrimePowerSet_iff.mp h𝔭)]

variable (K L) in
/-- Chebyshev's `ψ` restricted by powered Frobenius class: the inclusive sum of `log N(𝔭)` over
`𝔭 ^ j` of norm at most `x` for which `(artinSymbol 𝔭) ^ j = C`. -/
noncomputable def frobeniusPsi (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℝ :=
  primePowerSummatory K (frobeniusPrimePowerWeight K L C) x

variable (K L) in
/-- Chebyshev's `ϑ` restricted to the primes whose unpowered Artin class is `C`. -/
noncomputable def frobeniusTheta (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℝ :=
  primeTheta K (frobeniusPrimeSet K L C) x

/-- `frobeniusPsi` as an explicit sum over the inclusive prime-power carrier. -/
theorem frobeniusPsi_apply (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusPsi K L C x =
      ∑ A ∈ primePowersLE K x, frobeniusPrimePowerWeight K L C A := by
  rw [frobeniusPsi, primePowerSummatory_apply]

/-- `frobeniusTheta` as an explicit sum over the inclusive prime carrier. -/
theorem frobeniusTheta_apply (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusTheta K L C x =
      ∑ 𝔭 ∈ primesLE K x, (frobeniusPrimeSet K L C).indicator
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal : ℝ)) 𝔭 := by
  rw [frobeniusTheta, primeTheta_apply]

/-- The Frobenius `ψ` function is nonnegative. -/
theorem frobeniusPsi_nonneg (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    0 ≤ frobeniusPsi K L C x :=
  primePowerSummatory_nonneg K _ (frobeniusPrimePowerWeight_nonneg C) x

/-- The Frobenius `ψ` function is monotone in its inclusive cutoff. -/
theorem frobeniusPsi_mono (C : ConjClasses (L ≃ₐ[K] L)) :
    Monotone (frobeniusPsi K L C) :=
  primePowerSummatory_mono K _ (frobeniusPrimePowerWeight_nonneg C)

/-- The Frobenius `ϑ` function is nonnegative. -/
theorem frobeniusTheta_nonneg (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    0 ≤ frobeniusTheta K L C x :=
  primeTheta_nonneg (frobeniusPrimeSet K L C) x

/-- The Frobenius `ϑ` function is monotone in its inclusive cutoff. -/
theorem frobeniusTheta_mono (C : ConjClasses (L ≃ₐ[K] L)) :
    Monotone (frobeniusTheta K L C) :=
  primeTheta_mono (frobeniusPrimeSet K L C)

variable (K L) in
/-- The powered Frobenius weight on nonzero ideals, extended by zero away from prime powers. -/
noncomputable def frobeniusVonMangoldtWeight (C : ConjClasses (L ≃ₐ[K] L))
    (I : (Ideal (𝓞 K))⁰) : ℝ := by
  classical
  exact if hI : IsPrimePow (I : Ideal (𝓞 K)) then
      frobeniusPrimePowerWeight K L C ⟨I, hI⟩ else 0

/-- On the prime-power carrier, the ideal weight is the powered Frobenius weight. -/
@[simp]
theorem frobeniusVonMangoldtWeight_idealPrimePower (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) :
    frobeniusVonMangoldtWeight K L C (A : (Ideal (𝓞 K))⁰) =
      frobeniusPrimePowerWeight K L C A := by
  simp [frobeniusVonMangoldtWeight, A.2]

/-- The ideal weight vanishes away from prime-power ideals. -/
@[simp]
theorem frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow
    (C : ConjClasses (L ≃ₐ[K] L)) {I : (Ideal (𝓞 K))⁰}
    (hI : ¬ IsPrimePow (I : Ideal (𝓞 K))) : frobeniusVonMangoldtWeight K L C I = 0 := by
  simp [frobeniusVonMangoldtWeight, hI]

/-- The ideal weight is nonnegative. -/
theorem frobeniusVonMangoldtWeight_nonneg (C : ConjClasses (L ≃ₐ[K] L))
    (I : (Ideal (𝓞 K))⁰) : 0 ≤ frobeniusVonMangoldtWeight K L C I := by
  classical
  by_cases hI : IsPrimePow (I : Ideal (𝓞 K))
  · simpa [frobeniusVonMangoldtWeight, hI] using
      frobeniusPrimePowerWeight_nonneg (K := K) (L := L) C ⟨I, hI⟩
  · simp [frobeniusVonMangoldtWeight, hI]

variable (K L) in
/-- The Frobenius von Mangoldt coefficient at `n`: the sum of `log N(𝔭)` over prime powers
`𝔭 ^ j` of absolute norm `n` whose `j`-th powered Artin class is `C`. -/
noncomputable def frobeniusVonMangoldtCoeff (C : ConjClasses (L ≃ₐ[K] L)) :
    ArithmeticFunction ℝ where
  toFun n := ∑ I ∈ normFiber K n, frobeniusVonMangoldtWeight K L C I
  map_zero' := by rw [normFiber_zero, Finset.sum_empty]

/-- The Frobenius von Mangoldt coefficient is the sum of its ideal weights over the norm fibre. -/
theorem frobeniusVonMangoldtCoeff_apply (C : ConjClasses (L ≃ₐ[K] L)) (n : ℕ) :
    frobeniusVonMangoldtCoeff K L C n =
      ∑ I ∈ normFiber K n, frobeniusVonMangoldtWeight K L C I :=
  (rfl)

/-- Frobenius von Mangoldt coefficients are nonnegative. -/
theorem frobeniusVonMangoldtCoeff_nonneg (C : ConjClasses (L ≃ₐ[K] L)) (n : ℕ) :
    0 ≤ frobeniusVonMangoldtCoeff K L C n := by
  rw [frobeniusVonMangoldtCoeff_apply]
  exact Finset.sum_nonneg fun I _ ↦ frobeniusVonMangoldtWeight_nonneg C I

/-- **The order-four class computation, on an explicit group.** In the cyclic group of order four,
written multiplicatively as `Multiplicative (ZMod 4)` and generated by `g`, the generator has order
four and the class of `g ^ 2` — which is the square of the class of `g` — is a *different* class.
A group of exponent two cannot witness this, having no proper nonidentity square.

This is the group-theoretic half of the order-four regression below, discharged concretely, so
that the hypotheses of
`primePowerWeight_le_frobeniusVonMangoldtCoeff_of_artinSymbol_order_four` are known to be
simultaneously satisfiable rather than vacuous. -/
private theorem orderOf_eq_four_and_mk_ne_mk_pow_two_cyclicFour :
    orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 ∧
      ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 =
        ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4) ^ 2) ∧
      ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4)) ≠
        ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4) ^ 2) := by
  refine ⟨by rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one], ConjClasses.mk_pow _ 2, ?_⟩
  -- `Multiplicative (ZMod 4)` is commutative, so distinct elements have distinct classes; the
  -- generator and its square are `ofAdd 1` and `ofAdd 2`.
  rw [Ne, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq, ← ofAdd_nsmul]
  simp only [Multiplicative.ofAdd.apply_eq_iff_eq]
  decide

/-- **The order-four powered-class regression.** If a prime power has exponent two and its
unpowered Artin class is represented by an element `g` of order four, its positive weight occurs
in the coefficient for the class of `g ^ 2`, even though that class differs from the unpowered
class — and the same prime power is given weight zero by the *unpowered* fibre of its own Artin
class, which is exactly the term a definition filtering on `artinSymbol 𝔭 = C` alone would lose.
The conjugacy-class configuration assumed here is realised concretely by
`orderOf_eq_four_and_mk_ne_mk_pow_two_cyclicFour`. -/
private theorem primePowerWeight_le_frobeniusVonMangoldtCoeff_of_artinSymbol_order_four
    {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (g : L ≃ₐ[K] L)
    (hA : primePowerExponent A = 2)
    (hartin : artinSymbol (primePowerBase A).asIdeal hur = ConjClasses.mk g)
    (hg : orderOf g = 4) :
    0 < primePowerWeight A ∧
      primePowerWeight A ≤ frobeniusVonMangoldtCoeff K L (ConjClasses.mk (g ^ 2))
        (Ideal.absNorm (A : Ideal (𝓞 K))) ∧
      artinSymbol (primePowerBase A).asIdeal hur ≠ ConjClasses.mk (g ^ 2) ∧
      frobeniusPrimePowerWeight K L (ConjClasses.mk g) A = 0 := by
  have hpowered :
      artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A =
        ConjClasses.mk (g ^ 2) := by
    rw [hA, hartin, ConjClasses.mk_pow]
  have hne : ConjClasses.mk g ≠ ConjClasses.mk (g ^ 2) := by
    intro hclasses
    obtain ⟨c, hc⟩ := ConjClasses.mk_eq_mk_iff_isConj.mp hclasses
    have horders : orderOf g = orderOf (g ^ 2) :=
      SemiconjBy.orderOf_eq (c : L ≃ₐ[K] L) hc
    have hsquare : orderOf (g ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (hg ▸ by norm_num), hg]
    omega
  refine ⟨primePowerWeight_pos A, ?_, by rw [hartin]; exact hne, ?_⟩
  · rw [frobeniusVonMangoldtCoeff_apply]
    calc
      primePowerWeight A =
          frobeniusVonMangoldtWeight K L (ConjClasses.mk (g ^ 2))
            (A : (Ideal (𝓞 K))⁰) := by
        rw [frobeniusVonMangoldtWeight_idealPrimePower,
          frobeniusPrimePowerWeight_of_artinSymbol_pow_eq hur hpowered]
      _ ≤ ∑ I ∈ normFiber K (Ideal.absNorm (A : Ideal (𝓞 K))),
          frobeniusVonMangoldtWeight K L (ConjClasses.mk (g ^ 2)) I :=
        Finset.single_le_sum
          (fun I _ ↦ frobeniusVonMangoldtWeight_nonneg (ConjClasses.mk (g ^ 2)) I)
          ((mem_normFiber K).mpr rfl)
  · refine frobeniusPrimePowerWeight_of_notMem fun hmem ↦ hne ?_
    exact ((mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur _).mp hmem).symm.trans hpowered

/-- The Frobenius von Mangoldt coefficient vanishes unless its index is a prime power. -/
theorem frobeniusVonMangoldtCoeff_eq_zero_of_not_isPrimePow
    (C : ConjClasses (L ≃ₐ[K] L)) {n : ℕ} (hn : ¬ IsPrimePow n) :
    frobeniusVonMangoldtCoeff K L C n = 0 := by
  rw [frobeniusVonMangoldtCoeff_apply]
  refine Finset.sum_eq_zero fun I hI ↦
    frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow C fun h ↦ hn ?_
  rw [← (mem_normFiber K).mp hI]
  exact isPrimePow_absNorm ⟨I, h⟩

/-- The Frobenius von Mangoldt coefficient vanishes at `1`. -/
@[simp]
theorem frobeniusVonMangoldtCoeff_apply_one (C : ConjClasses (L ≃ₐ[K] L)) :
    frobeniusVonMangoldtCoeff K L C 1 = 0 :=
  frobeniusVonMangoldtCoeff_eq_zero_of_not_isPrimePow C not_isPrimePow_one

/-- Frobenius `ψ` is the inclusive partial sum of the Frobenius von Mangoldt coefficients. -/
theorem frobeniusPsi_eq_sum_range (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusPsi K L C x =
      ∑ n ∈ Finset.range (⌊x⌋₊ + 1), frobeniusVonMangoldtCoeff K L C n := by
  rw [frobeniusPsi,
    ← idealSummatory_eq_primePowerSummatory K (frobeniusVonMangoldtWeight K L C)
      (frobeniusPrimePowerWeight K L C) (frobeniusVonMangoldtWeight_idealPrimePower C)
      (fun _ hI ↦ frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow C hI),
    idealSummatory_eq_sum_range_normFiber]
  exact Finset.sum_congr rfl fun n _ ↦ (frobeniusVonMangoldtCoeff_apply C n).symm

/-- The gap between the Frobenius `ψ` and `ϑ` functions is exactly the sum of the higher
prime-power weight over the `C`-fibre. -/
theorem frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory (C : ConjClasses (L ≃ₐ[K] L))
    (x : ℝ) :
    frobeniusPsi K L C x - frobeniusTheta K L C x =
      primePowerSummatory K
        ((frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight) x := by
  have hsplit : frobeniusPrimePowerWeight K L C =
      (frobeniusPrimePowerWeight K L C -
          (frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight) +
        (frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight := by
    rw [sub_add_cancel]
  have hzero : ∀ A : IdealPrimePower K, ¬ Prime (A : Ideal (𝓞 K)) →
      (frobeniusPrimePowerWeight K L C -
        (frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight) A = 0 := fun A hA ↦ by
    by_cases hA' : A ∈ frobeniusPrimePowerSet K L C
    · rw [Pi.sub_apply, frobeniusPrimePowerWeight_of_mem hA', Set.indicator_of_mem hA',
        higherPrimePowerWeight_of_not_prime hA, sub_self]
    · rw [Pi.sub_apply, frobeniusPrimePowerWeight_of_notMem hA', Set.indicator_of_notMem hA',
        sub_self]
  have hprime : primePowerSummatory K
      (frobeniusPrimePowerWeight K L C -
        (frobeniusPrimePowerSet K L C).indicator higherPrimePowerWeight) x =
        frobeniusTheta K L C x := by
    rw [primePowerSummatory_eq_primeSummatory K _ hzero, primeSummatory_apply,
      frobeniusTheta_apply]
    refine Finset.sum_congr rfl fun 𝔭 _ ↦ ?_
    have hp : Prime ((IdealPrimePower.ofPrime 𝔭 : IdealPrimePower K) : Ideal (𝓞 K)) :=
      IdealPrimePower.prime_ofPrime 𝔭
    rw [Pi.sub_apply, frobeniusPrimePowerWeight_ofPrime,
      Set.indicator_apply_eq_zero.mpr fun _ ↦ higherPrimePowerWeight_of_prime hp, sub_zero]
  rw [frobeniusPsi, hsplit, primePowerSummatory_add, hprime, add_sub_cancel_left]

/-- The higher prime powers make a nonnegative contribution to Frobenius `ψ`. -/
theorem frobeniusTheta_le_frobeniusPsi (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusTheta K L C x ≤ frobeniusPsi K L C x := by
  rw [← sub_nonneg, frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory]
  exact primePowerSummatory_nonneg K _
    (fun A ↦ Set.indicator_nonneg (fun A _ ↦ higherPrimePowerWeight_nonneg A) A) x

/-- **The Frobenius higher-prime-power tail is bounded by the unrestricted one.** The gap
between Frobenius `ψ` and `ϑ` is at most the corresponding gap for all primes. -/
theorem frobeniusPsi_sub_frobeniusTheta_le (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    frobeniusPsi K L C x - frobeniusTheta K L C x ≤
      primePsi K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x -
        primeTheta K (Set.univ : Set (HeightOneSpectrum (𝓞 K))) x := by
  rw [frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory, primePsi_sub_primeTheta,
    primePowerSummatory_apply, primePowerSummatory_apply]
  refine Finset.sum_le_sum fun A _ ↦ ?_
  have huniv : {A : IdealPrimePower K | primePowerBase A ∈ Set.univ}.indicator
      higherPrimePowerWeight A = higherPrimePowerWeight A :=
    Set.indicator_of_mem (Set.mem_univ _) _
  rw [huniv]
  exact Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ higherPrimePowerWeight_nonneg A

/-- The higher-prime-power contribution to Frobenius `ψ` is `o(x)`. -/
theorem isLittleO_frobeniusPsi_sub_frobeniusTheta (C : ConjClasses (L ≃ₐ[K] L)) :
    (fun x ↦ frobeniusPsi K L C x - frobeniusTheta K L C x) =o[atTop]
      fun x : ℝ ↦ x := by
  simpa only [frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory] using
    primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight K zero_le_one fun A ↦ by
      rw [Real.norm_of_nonneg (Set.indicator_nonneg
        (fun A _ ↦ higherPrimePowerWeight_nonneg A) A), one_mul]
      exact Set.indicator_apply_le' (fun _ ↦ le_rfl) fun _ ↦ higherPrimePowerWeight_nonneg A

end NumberField.Chebotarev
