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

* `genusCharFunElementaryTwoQuotientLinearMap`: the genus character as a linear functional on
  `Cl⁺(K) / Cl⁺(K)²`.
* `genusCharFunElementaryTwoQuotientFamilyLinearMap`: the linear map collecting all singleton
  genus characters.
* `genusCharFunElementaryTwoQuotientLinearMap_eq_sum_singleton`: a subset character is the
  sum of its singleton linear functionals.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

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
theorem genusCharFunElementaryTwoQuotientLinearMap_eq_sum_singleton
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) :
    genusCharFunElementaryTwoQuotientLinearMap hs heven hprod hmin hgen hsf hts =
      ∑ P : ↥t, genusCharFunElementaryTwoQuotientLinearMap
        hs heven hprod hmin hgen hsf (Finset.singleton_subset_iff.mpr (hts P.2)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨A, rfl⟩ := TauCeti.elementaryTwoQuotientMk_surjective
    (G := NumberField.NarrowClassGroup K) x
  apply Additive.toMul.injective
  simpa using DFunLike.congr_fun
    (genusCharFunNarrowClassGroupHom_eq_prod_singleton
      hs heven hprod hmin hgen hsf hts) A

end TauCeti.Multiquadratic
