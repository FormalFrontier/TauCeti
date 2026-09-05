/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.Narrow
public import TauCeti.NumberTheory.NumberField.NarrowClassGroup.CoprimeRepresentative
import Mathlib.GroupTheory.Congruence.Basic

/-!
# Genus characters on the narrow class group

The genus character of a quadratic field is initially defined only on ideals whose absolute norm
is coprime to a chosen product of prime discriminants. This file uses coprime representatives to
descend that arithmetic character to the whole narrow class group. The resulting homomorphism is
the character package needed for the lower bound in the real quadratic genus-theory formula.

The construction follows Cox, *Primes of the Form `x² + ny²`*, §3.B, and Lemmermeyer,
*Reciprocity Laws*, §2.2. The coprime-ideal character and the strong-approximation representative
theorem used here are developed in the preceding Tau Ceti modules.

## Main results

* `genusCharFunCoprimeIdealHom_eq_of_mk0_eq`: the coprime-ideal character is constant on fibres of
  the map to the narrow class group.
* `genusCharFunNarrowClassGroupHom`: the descended genus character on `Cl⁺(K)`.
* `genusCharFunNarrowClassGroupHom_mk0`: its computation on a coprime integral ideal.
* `genusCharFunNarrowClassGroupHom_eq_prod_singleton`: a subset-indexed narrow genus character is
  the product of its singleton characters.
-/

public section

open Polynomial
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

open NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The map from ideals coprime to a modulus to their narrow ideal classes. -/
private noncomputable def genusCharFunCoprimeIdealClassMap (t : Finset ℤ) :
    genusCharFunCoprimeIdealSubmonoid (K := K) t →* NumberField.NarrowClassGroup K :=
  (NumberField.NarrowClassGroup.mk0 (K := K)).comp
    (genusCharFunCoprimeIdealSubmonoid (K := K) t).subtype

/-- Every narrow class has a representative in the coprime-ideal submonoid. -/
private theorem genusCharFunCoprimeIdealClassMap_surjective {t : Finset ℤ}
    (hm : (∏ P ∈ t, P) ≠ 0) :
    Function.Surjective
      (genusCharFunCoprimeIdealClassMap (K := K) t) := by
  intro C
  obtain ⟨I, hIC, hcop⟩ := NumberField.NarrowClassGroup.exists_mk0_eq_and_isCoprime_absNorm C hm
  refine ⟨⟨I, ?_⟩, hIC⟩
  simpa only [mem_genusCharFunCoprimeIdealSubmonoid_iff] using hcop

variable {θ : 𝓞 K} {d : ℤ}

/-- **Coprime genus characters are constant on narrow-class fibres.**

The character has the same value on any two coprime integral ideals with the same narrow ideal
class. This fibre invariance is what allows the character to descend from coprime ideals to the
full narrow class group.
-/
theorem genusCharFunCoprimeIdealHom_eq_of_mk0_eq
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s)
    {I J : genusCharFunCoprimeIdealSubmonoid (K := K) t}
    (hIJ : NumberField.NarrowClassGroup.mk0 I.1 =
      NumberField.NarrowClassGroup.mk0 J.1) :
    genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) I =
      genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) J := by
  let m : ℤ := ∏ P ∈ t, P
  have hm : m ≠ 0 := by
    -- Unfold the local modulus before applying the product nonvanishing lemma.
    change (∏ P ∈ t, P) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro P hP
    exact (hs P (hts hP)).isFundamentalDiscriminant.ne_zero
  obtain ⟨A, hAC, hAcop⟩ :=
    NumberField.NarrowClassGroup.exists_mk0_eq_and_isCoprime_absNorm
      (NumberField.NarrowClassGroup.mk0 I.1)⁻¹ hm
  let A' : genusCharFunCoprimeIdealSubmonoid (K := K) t := ⟨A, by
    simpa only [mem_genusCharFunCoprimeIdealSubmonoid_iff] using hAcop⟩
  have hAC' : NumberField.NarrowClassGroup.mk0 A'.1 =
      (NumberField.NarrowClassGroup.mk0 I.1)⁻¹ := by
    simpa [A'] using hAC
  let IA : genusCharFunCoprimeIdealSubmonoid (K := K) t := I * A'
  let JA : genusCharFunCoprimeIdealSubmonoid (K := K) t := J * A'
  have hIA : NumberField.NarrowClassGroup.mk0 IA.1 = 1 := by
    -- Expose the product carrier so the class-group homomorphism can rewrite it.
    change NumberField.NarrowClassGroup.mk0 (I.1 * A'.1) = 1
    rw [map_mul, hAC']
    simp
  have hJA : NumberField.NarrowClassGroup.mk0 JA.1 = 1 := by
    -- As above, make the product visible before using the equality of the original classes.
    change NumberField.NarrowClassGroup.mk0 (J.1 * A'.1) = 1
    rw [map_mul, ← hIJ, hAC']
    simp
  obtain ⟨a, ha, hapos, hIAspan⟩ :=
    (NumberField.NarrowClassGroup.mk0_eq_one_iff.mp hIA)
  obtain ⟨b, hb, hbpos, hJAspan⟩ :=
    (NumberField.NarrowClassGroup.mk0_eq_one_iff.mp hJA)
  have hcharIA := genusCharFunCoprimeIdealHom_eq_one_of_eq_span_singleton
    hs heven hprod hmin hgen hsf hts (I := IA) hapos hIAspan
  have hcharJA := genusCharFunCoprimeIdealHom_eq_one_of_eq_span_singleton
    hs heven hprod hmin hgen hsf hts (I := JA) hbpos hJAspan
  have hprodIA :
      genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) I *
        genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) A' = 1 := by
    simpa only [IA, map_mul] using hcharIA
  have hprodJA :
      genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) J *
        genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) A' = 1 := by
    simpa only [JA, map_mul] using hcharJA
  exact mul_right_cancel (hprodIA.trans hprodJA.symm)

/-- **The genus character on the narrow class group.**

For a factor `t` of a prime-discriminant factorization, this is the homomorphism
`Cl⁺(K) → ℤˣ` obtained by evaluating a coprime integral representative. Its definition is
independent of the representative by `genusCharFunCoprimeIdealHom_eq_of_mk0_eq`.
-/
noncomputable def genusCharFunNarrowClassGroupHom
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s) :
    NumberField.NarrowClassGroup K →* ℤˣ :=
  let q := genusCharFunCoprimeIdealClassMap (K := K) t
  let χ := genusCharFunCoprimeIdealHom (K := K) (fun P hP => hs P (hts hP))
  ((Con.ker q).lift χ (fun I J h =>
      genusCharFunCoprimeIdealHom_eq_of_mk0_eq hs heven hprod hmin hgen hsf hts
        -- The congruence kernel is exactly equality after applying `mk0`.
        (show NumberField.NarrowClassGroup.mk0 I.1 =
          NumberField.NarrowClassGroup.mk0 J.1 from h))).comp
    (Con.quotientKerEquivOfSurjective q
      (genusCharFunCoprimeIdealClassMap_surjective
        (by
          rw [Finset.prod_ne_zero_iff]
          intro P hP
          exact (hs P (hts hP)).isFundamentalDiscriminant.ne_zero))).symm.toMonoidHom

/-- The descended genus character evaluates on a coprime ideal as the original ideal character. -/
@[simp] theorem genusCharFunNarrowClassGroupHom_mk0
    {s t : Finset ℤ} (hs : ∀ P ∈ s, IsPrimeDiscriminant P)
    (heven : ∀ P ∈ s, ∀ P' ∈ s,
      IsEvenPrimeDiscriminant P → IsEvenPrimeDiscriminant P' → P = P')
    (hprod : ∏ P ∈ s, P = fundamentalDiscriminant d)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (hsf : Squarefree d) (hts : t ⊆ s)
    (I : genusCharFunCoprimeIdealSubmonoid (K := K) t) :
    genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts
        (NumberField.NarrowClassGroup.mk0 I.1) =
      genusCharFunCoprimeIdealHom (fun P hP => hs P (hts hP)) I := by
  let q := genusCharFunCoprimeIdealClassMap (K := K) t
  let χ := genusCharFunCoprimeIdealHom (K := K) (fun P hP => hs P (hts hP))
  have hχ : Con.ker q ≤ Con.ker χ := fun A B h =>
    genusCharFunCoprimeIdealHom_eq_of_mk0_eq hs heven hprod hmin hgen hsf hts
      -- Make the kernel relation explicit for the comparison theorem.
      (show NumberField.NarrowClassGroup.mk0 A.1 =
        NumberField.NarrowClassGroup.mk0 B.1 from h)
  let e := Con.quotientKerEquivOfSurjective q
      (genusCharFunCoprimeIdealClassMap_surjective (by
        rw [Finset.prod_ne_zero_iff]
        intro P hP
        exact (hs P (hts hP)).isFundamentalDiscriminant.ne_zero))
  -- Unfold the quotient definition only far enough to expose its computation map.
  change (Con.ker q).lift χ hχ (e.symm (q I)) = χ I
  have he : e.symm (q I) = (I : (Con.ker q).Quotient) := by
    apply (MulEquiv.symm_apply_eq e).mpr
    exact (Con.kerLift_mk (f := q) I).symm
  rw [he]
  exact Con.lift_mk' hχ I

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
    (hsf : Squarefree d) (hts : t ⊆ s) :
    genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf hts =
      ∏ P : ↥t, genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr (hts P.2)) := by
  apply MonoidHom.ext
  intro A
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
  have h_eval :
      (∏ P : ↥t, genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
        (Finset.singleton_subset_iff.mpr (hts P.2)))
          (NumberField.NarrowClassGroup.mk0 It.1) =
        ∏ P : ↥t, genusCharFunNarrowClassGroupHom hs heven hprod hmin hgen hsf
          (Finset.singleton_subset_iff.mpr (hts P.2))
          (NumberField.NarrowClassGroup.mk0 It.1) := by
    simp
  rw [h_eval]
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

end TauCeti.Multiquadratic
