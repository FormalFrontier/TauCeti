/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.NarrowClassGroup
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.ElementaryTwoQuotient

/-!
# Genus characters on the elementary-2 quotient of the narrow class group

A genus character on the narrow class group has values in the two-element group `ℤˣ`, so it is
trivial on squares. It therefore factors canonically through the maximal elementary-2 quotient

```text
Cl⁺(K) / Cl⁺(K)².
```

Writing the quotient and the sign group additively makes the factor a `ZMod 2`-linear functional.
This file also collects the characters indexed by the individual prime discriminants into one
linear map. A character indexed by a subset is the sum of the corresponding singleton
coordinates. Thus the arithmetic characters are organized as the linear family used in the
genus-theoretic computation of the narrow class group's two-rank.

The construction follows the genus-character treatment in Cox, *Primes of the Form `x² + ny²`*,
§3.B, and Lemmermeyer, *Reciprocity Laws*, §2.2. The quotient factorization uses Mathlib's
`ModN.liftEquiv'`, exposed through `TauCeti.elementaryTwoQuotientLinearLiftEquiv`.

## Main results

* `genusCharFunNarrowClassGroupHom_eq_prod_singleton`: a subset-indexed narrow genus character is
  the product of its singleton characters.
* `genusCharFunElementaryTwoQuotientLinearMap`: the genus character as a linear functional on
  `Cl⁺(K) / Cl⁺(K)²`.
* `genusCharFunElementaryTwoQuotientFamilyLinearMap`: the linear map collecting all singleton
  genus characters.
* `genusCharFunElementaryTwoQuotientLinearMap_apply_eq_sum_singleton`: a subset character is the
  sum of its singleton linear functionals.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- A genus character indexed by a set `t` of prime discriminants is the product of the
characters indexed by the singletons in `t`.

Although this is immediate for the arithmetic function `genusCharFun`, the narrow-class-group
characters are defined using coprime representatives. The statement records that their descent
preserves the same product decomposition. -/
theorem genusCharFunNarrowClassGroupHom_eq_prod_singleton
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) (A : NumberField.NarrowClassGroup K) :
    genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts A =
      ∏ P : ↥t, genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr (hts P.2)) A := by
  have hm : (∏ P ∈ t, P) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro P hP
    exact (hs P (hts hP)).isFundamentalDiscriminant.ne_zero
  obtain ⟨I, hIA, hIcop⟩ :=
    NumberField.NarrowClassGroup.exists_mk0_eq_and_isCoprime_absNorm A hm
  let It : genusCharFunCoprimeIdealSubmonoid (K := K) t := ⟨I, by
    simpa only [mem_genusCharFunCoprimeIdealSubmonoid_iff] using hIcop⟩
  rw [← hIA]
  -- `It` and `I` carry the same ideal; expose that equality to use the quotient computation rule.
  rw [← show NumberField.NarrowClassGroup.mk0 It.1 =
      NumberField.NarrowClassGroup.mk0 I from rfl,
    genusCharFunNarrowClassGroupHom_mk0]
  apply Units.ext
  rw [genusCharFunCoprimeIdealHom_apply, genusCharFun_def, Units.coe_prod]
  -- Coercing the product of unit-valued characters leaves a product of their integer values.
  change _ = ∏ P : ↥t,
    ((genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
      (Finset.singleton_subset_iff.mpr (hts P.2))
      (NumberField.NarrowClassGroup.mk0 It.1) : ℤˣ) : ℤ)
  rw [Finset.prod_subtype t (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro P _
  let IP : genusCharFunCoprimeIdealSubmonoid (K := K) {P.1} := ⟨I, by
    rw [mem_genusCharFunCoprimeIdealSubmonoid_iff]
    simpa using (IsCoprime.prod_right_iff.mp hIcop) P P.2⟩
  -- `IP` only equips the same ideal with the weaker singleton coprimality property.
  rw [show NumberField.NarrowClassGroup.mk0 I =
      NumberField.NarrowClassGroup.mk0 IP.1 from rfl,
    genusCharFunNarrowClassGroupHom_mk0, genusCharFunCoprimeIdealHom_apply,
    genusCharFun_singleton]

/-- The genus character as a `ZMod 2`-linear functional on the maximal elementary-2 quotient
`Cl⁺(K) / Cl⁺(K)²` of the narrow class group.

The target is written as `Additive ℤˣ`: multiplication of signs is addition in this two-element
`ZMod 2`-module. -/
noncomputable def genusCharFunElementaryTwoQuotientLinearMap
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) :
    NumberField.NarrowClassGroup.ElementaryTwoQuotient K →ₗ[ZMod 2] Additive ℤˣ :=
  (TauCeti.elementaryTwoQuotientLinearLiftEquiv
      (G := NumberField.NarrowClassGroup K) (H := Additive ℤˣ)).symm
    ⟨(genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts).toAdditive,
      fun C => by
        apply Additive.toMul.injective
        simp [two_nsmul, Int.units_mul_self]⟩

/-- Evaluating the factored linear genus character on the class of a narrow ideal class recovers
the original narrow-class-group character. -/
@[simp] theorem genusCharFunElementaryTwoQuotientLinearMap_mk
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) (A : NumberField.NarrowClassGroup K) :
    genusCharFunElementaryTwoQuotientLinearMap hs heven hprod hmin hgen hsf hts
        (TauCeti.elementaryTwoQuotientMk A) =
      Additive.ofMul (genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts A) := by
  unfold genusCharFunElementaryTwoQuotientLinearMap
  rw [TauCeti.elementaryTwoQuotientLinearLiftEquiv_symm_mk]
  rfl

/-- The linear family of singleton genus characters, with one coordinate for each prime
discriminant in `s`. -/
noncomputable def genusCharFunElementaryTwoQuotientFamilyLinearMap
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) :
    NumberField.NarrowClassGroup.ElementaryTwoQuotient K →ₗ[ZMod 2]
      ((P : ↥s) → Additive ℤˣ) :=
  LinearMap.pi fun P => genusCharFunElementaryTwoQuotientLinearMap
    hs heven hprod hmin hgen hsf (Finset.singleton_subset_iff.mpr P.2)

/-- A coordinate of the family map is the linear genus character indexed by the corresponding
singleton prime discriminant. -/
@[simp] theorem genusCharFunElementaryTwoQuotientFamilyLinearMap_apply
    {s : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (x : NumberField.NarrowClassGroup.ElementaryTwoQuotient K)
    (P : ↥s) :
    genusCharFunElementaryTwoQuotientFamilyLinearMap hs heven hprod hmin hgen hsf x P =
      genusCharFunElementaryTwoQuotientLinearMap hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr P.2) x := by
  rfl

/-- The linear functional of a subset-indexed genus character is the sum of the singleton
functionals indexed by that subset. -/
theorem genusCharFunElementaryTwoQuotientLinearMap_apply_eq_sum_singleton
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s)
    (x : NumberField.NarrowClassGroup.ElementaryTwoQuotient K) :
    genusCharFunElementaryTwoQuotientLinearMap hs heven hprod hmin hgen hsf hts x =
      ∑ P : ↥t, genusCharFunElementaryTwoQuotientLinearMap
        hs heven hprod hmin hgen hsf (Finset.singleton_subset_iff.mpr (hts P.2)) x := by
  obtain ⟨A, rfl⟩ := TauCeti.elementaryTwoQuotientMk_surjective
    (G := NumberField.NarrowClassGroup K) x
  apply Additive.toMul.injective
  simpa using genusCharFunNarrowClassGroupHom_eq_prod_singleton
    hs heven hprod hmin hgen hsf hts A

end TauCeti.Multiquadratic
