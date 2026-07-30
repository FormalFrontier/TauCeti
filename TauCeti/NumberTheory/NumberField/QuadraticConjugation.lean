/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.PowerBasis
public import TauCeti.NumberTheory.ClassGroup.Equiv

/-!
# Quadratic conjugation on a quadratic number field

For a quadratic number field `K` — presented by an algebraic integer `θ : 𝓞 K` generating `K`
over `ℚ` whose minimal polynomial over `ℤ` is `X² - d` — this file constructs the nontrivial
`ℚ`-algebra automorphism `σ : K ≃ₐ[ℚ] K`, characterised by `σ θ = -θ`. It is the field-theoretic
conjugation of `ℚ(√d)`; its restriction to the ring of integers and its action on the class group
(by inversion, the genus-theoretic fact `I · σI` principal) are developed downstream.

## Main definitions and results

* `TauCeti.NumberField.quadConj`: the conjugation `K ≃ₐ[ℚ] K`, sending `θ ↦ -θ`.
* `TauCeti.NumberField.quadConj_gen`: `quadConj θ = -θ`.
* `TauCeti.NumberField.quadConj_involutive`: `quadConj` is an involution.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- The minimal polynomial of `θ` over `ℚ` is `X² - d`, lifted from its minimal polynomial over
`ℤ` through the integrally closed base `ℤ ⊆ 𝓞 K`. -/
theorem minpoly_rat_of_int (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    minpoly ℚ (θ : K) = X ^ 2 - C ((d : ℤ) : ℚ) := by
  rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ K (IsIntegralClosure.isIntegral ℤ K θ),
    hmin]
  simp

/-- `θ` squares to `d` in `K`. -/
theorem sq_eq_of_minpoly (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    (θ : K) ^ 2 = ((d : ℤ) : ℚ) := by
  have h := minpoly.aeval ℚ (θ : K)
  rw [minpoly_rat_of_int hmin] at h
  simpa [sub_eq_zero] using h

/-- The power basis `1, θ` of the quadratic field `K` over `ℚ`. -/
noncomputable def quadPowerBasis (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop' θ.isIntegral_coe.tower_top hgen

@[simp] theorem quadPowerBasis_gen (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (quadPowerBasis hgen).gen = (θ : K) :=
  PowerBasis.ofAdjoinEqTop'_gen _ hgen

/-- `-θ` (as `-pb.gen`) is a root of the minimal polynomial of `θ`, so it is a valid conjugation
target. Kept in terms of the power-basis generator to avoid dependent rewrites downstream. -/
theorem aeval_neg_gen_minpoly (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    aeval (-(quadPowerBasis hgen).gen) (minpoly ℚ (quadPowerBasis hgen).gen) = 0 := by
  rw [quadPowerBasis_gen, minpoly_rat_of_int hmin]
  simp [sq_eq_of_minpoly hmin]

/-- **Quadratic conjugation.** The nontrivial `ℚ`-automorphism of the quadratic field `K = ℚ(√d)`,
characterised by `θ ↦ -θ`. Built as a self-inverse algebra homomorphism using the power basis
`1, θ`. -/
noncomputable def quadConj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : K ≃ₐ[ℚ] K :=
  AlgEquiv.ofAlgHom
    ((quadPowerBasis hgen).lift (-(quadPowerBasis hgen).gen) (aeval_neg_gen_minpoly hmin hgen))
    ((quadPowerBasis hgen).lift (-(quadPowerBasis hgen).gen) (aeval_neg_gen_minpoly hmin hgen))
    ((quadPowerBasis hgen).algHom_ext (by
      rw [AlgHom.comp_apply, PowerBasis.lift_gen, map_neg, PowerBasis.lift_gen, neg_neg,
        AlgHom.id_apply]))
    ((quadPowerBasis hgen).algHom_ext (by
      rw [AlgHom.comp_apply, PowerBasis.lift_gen, map_neg, PowerBasis.lift_gen, neg_neg,
        AlgHom.id_apply]))

@[simp] theorem quadConj_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    quadConj hmin hgen (θ : K) = -(θ : K) := by
  rw [quadConj, AlgEquiv.ofAlgHom_apply]
  nth_rewrite 1 [← quadPowerBasis_gen hgen]
  rw [PowerBasis.lift_gen, quadPowerBasis_gen]

theorem quadConj_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (quadConj hmin hgen) := by
  have hext : (quadConj hmin hgen).toAlgHom.comp (quadConj hmin hgen).toAlgHom
      = AlgHom.id ℚ K := by
    apply (quadPowerBasis hgen).algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, quadPowerBasis_gen, quadConj_gen,
      map_neg, neg_neg, AlgHom.id_apply]
  intro x
  have := AlgHom.congr_fun hext x
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.id_apply] using this

/-- **Quadratic conjugation on the ring of integers.** The restriction of `quadConj` to `𝓞 K`, a
ring automorphism `𝓞 K ≃+* 𝓞 K`. This is the automorphism whose action on `ClassGroup (𝓞 K)` is by
inversion (the genus-theoretic fact that `I · σI` is principal). -/
noncomputable def quadConjInt (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (quadConj hmin hgen).toRingEquiv

@[simp] theorem quadConjInt_coe (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : 𝓞 K) :
    (quadConjInt hmin hgen x : K) = quadConj hmin hgen (x : K) := by
  rw [quadConjInt, RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_ringEquiv]

theorem quadConjInt_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (quadConjInt hmin hgen) := by
  intro x
  have h : (quadConjInt hmin hgen (quadConjInt hmin hgen x) : K) = (x : K) := by
    rw [quadConjInt_coe, quadConjInt_coe]
    exact quadConj_involutive hmin hgen (x : K)
  exact RingOfIntegers.coe_injective h

/-- Quadratic conjugation acts as an **involution on the class group** `Cl(𝓞 K)`. This is the
group-action shadow of `quadConjInt_involutive`, and the first step towards the genus-theoretic
fact that the induced action is inversion (hence trivial on `Cl/Cl²`). -/
theorem mulEquiv_quadConjInt_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (ClassGroup.mulEquiv (quadConjInt hmin hgen)) :=
  ClassGroup.mulEquiv_involutive (quadConjInt_involutive hmin hgen)

end TauCeti.NumberField
