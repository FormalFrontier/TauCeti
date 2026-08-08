/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Basic

/-!
# Effective divisors and integral fractional ideals

For a Dedekind domain `R` with fraction field `K`,
`fractionalIdealDivisorAddEquiv R K` identifies invertible fractional ideals with Weil divisors
on the height-one spectrum of `R`. This file proves that the equivalence respects the positive
parts on both sides: a fractional ideal is contained in `R` exactly when all of its
height-one multiplicities are nonnegative.

Thus the affine Weil--Cartier dictionary restricts to an additive equivalence between integral
invertible fractional ideals and effective Weil divisors. This directly advances the
`Weil ≃ Cartier` divisor dictionary in Layer A of
`TauCetiRoadmap/JacobianChallenge/README.md`.

The reverse implication uses Mathlib's factorization of a nonzero fractional ideal as the
finite product of its height-one prime powers. No external formalization is copied.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

section

variable (R : Type*) [CommRing R]
variable (K : Type*) [CommRing K] [Algebra R K]

/-- The additive submonoid of invertible fractional ideals contained in `R`. -/
def integralFractionalIdealSubmonoid :
    AddSubmonoid (Additive (FractionalIdeal R⁰ K)ˣ) where
  carrier := {I | Units.val (Additive.toMul I) ≤ 1}
  zero_mem' := by simp
  add_mem' {I J} hI hJ := by
    simpa only [Set.mem_ofPred_eq, toMul_add, Units.val_mul] using mul_le_one' hI hJ

/-- Membership in `integralFractionalIdealSubmonoid` means that the fractional ideal is contained
in the base ring. -/
@[simp]
lemma mem_integralFractionalIdealSubmonoid (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    I ∈ integralFractionalIdealSubmonoid R K ↔
      Units.val (Additive.toMul I) ≤ 1 :=
  Iff.rfl

end

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

variable {R K}

/-- The divisor of an integral fractional ideal (one contained in `R`, i.e. `≤ 1`) is effective:
integral ideals have no poles, only zeros. This is the affine "effective divisor ↔ integral ideal"
half of the dictionary. -/
lemma isEffective_fractionalIdealDivisor_of_le_one (I : Additive (FractionalIdeal R⁰ K)ˣ)
    (hI : Units.val (Additive.toMul I) ≤ 1) :
    IsEffective (fractionalIdealDivisor R K I) := by
  rw [isEffective_iff]
  intro v
  rw [coeff_fractionalIdealDivisor]
  obtain ⟨J, hJ⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hI
  rw [← hJ]
  exact FractionalIdeal.count_coe_nonneg K v J

/-- If the divisor of an invertible fractional ideal is effective, then the fractional ideal is
integral. This is the converse of `isEffective_fractionalIdealDivisor_of_le_one`. -/
lemma le_one_of_isEffective_fractionalIdealDivisor (I : Additive (FractionalIdeal R⁰ K)ˣ)
    (hI : IsEffective (fractionalIdealDivisor R K I)) :
    Units.val (Additive.toMul I) ≤ 1 := by
  have hcount :
      ∀ v : HeightOneSpectrum R,
        0 ≤ FractionalIdeal.count K v (Units.val (Additive.toMul I)) := by
    intro v
    simpa only [coeff_fractionalIdealDivisor] using (isEffective_iff _).mp hI v
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
    (Units.ne_zero (Additive.toMul I))]
  exact finprod_induction (· ≤ 1) le_rfl (fun _ _ ↦ mul_le_one') fun v ↦
    zpow_le_one₀
      (bot_lt_iff_ne_bot.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))
      FractionalIdeal.coeIdeal_le_one (hcount v)

/-- An invertible fractional ideal is integral exactly when its associated Weil divisor is
effective. -/
@[simp]
lemma isEffective_fractionalIdealDivisor_iff (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    IsEffective (fractionalIdealDivisor R K I) ↔
      Units.val (Additive.toMul I) ≤ 1 :=
  ⟨le_one_of_isEffective_fractionalIdealDivisor I,
    isEffective_fractionalIdealDivisor_of_le_one I⟩

/-- The divisor of an invertible fractional ideal is effective exactly when that ideal belongs to
the integral fractional-ideal submonoid. -/
lemma isEffective_fractionalIdealDivisor_iff_mem (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    IsEffective (fractionalIdealDivisor R K I) ↔
      I ∈ integralFractionalIdealSubmonoid R K := by
  rw [mem_integralFractionalIdealSubmonoid, isEffective_fractionalIdealDivisor_iff]

variable (R K)

/-- The affine Weil--Cartier equivalence restricted to positive objects: integral invertible
fractional ideals correspond exactly to effective Weil divisors. -/
noncomputable def integralFractionalIdealDivisorAddEquiv :
    integralFractionalIdealSubmonoid R K ≃+
      effectiveSubmonoid (HeightOneSpectrum R) :=
  ((fractionalIdealDivisorAddEquiv R K).addSubmonoidMap
    (integralFractionalIdealSubmonoid R K)).trans
      (AddEquiv.addSubmonoidCongr <| by
        ext D
        constructor
        · rintro ⟨I, hI, rfl⟩
          exact (mem_effectiveSubmonoid _).mpr <| by
            simpa only [fractionalIdealDivisorAddEquiv_apply] using
              (isEffective_fractionalIdealDivisor_iff_mem
                (R := R) (K := K) I).mpr hI
        · intro hD
          refine ⟨(fractionalIdealDivisorAddEquiv R K).symm D, ?_, ?_⟩
          · exact (isEffective_fractionalIdealDivisor_iff_mem
              (R := R) (K := K)
              ((fractionalIdealDivisorAddEquiv R K).symm D)).mp <| by
                simpa only [← fractionalIdealDivisorAddEquiv_apply,
                  AddEquiv.apply_symm_apply] using
                    (mem_effectiveSubmonoid D).mp hD
          · exact (fractionalIdealDivisorAddEquiv R K).apply_symm_apply D)

/-- The restricted equivalence agrees with `fractionalIdealDivisor` after forgetting
effectivity. -/
@[simp]
lemma coe_integralFractionalIdealDivisorAddEquiv (I : integralFractionalIdealSubmonoid R K) :
    ((integralFractionalIdealDivisorAddEquiv R K I :
        effectiveSubmonoid (HeightOneSpectrum R)) :
      WeilDivisor (HeightOneSpectrum R)) =
      fractionalIdealDivisor R K I :=
  fractionalIdealDivisorAddEquiv_apply
    (R := R) (K := K) (I : Additive (FractionalIdeal R⁰ K)ˣ)

/-- The inverse restricted equivalence agrees with the unrestricted inverse after forgetting
integrality. -/
@[simp]
lemma coe_integralFractionalIdealDivisorAddEquiv_symm
    (D : effectiveSubmonoid (HeightOneSpectrum R)) :
    (((integralFractionalIdealDivisorAddEquiv R K).symm D :
        integralFractionalIdealSubmonoid R K) :
      Additive (FractionalIdeal R⁰ K)ˣ) =
      (fractionalIdealDivisorAddEquiv R K).symm D := by
  apply (fractionalIdealDivisorAddEquiv R K).injective
  rw [AddEquiv.apply_symm_apply]
  simpa only [coe_integralFractionalIdealDivisorAddEquiv,
    fractionalIdealDivisorAddEquiv_apply] using
    congrArg Subtype.val
      ((integralFractionalIdealDivisorAddEquiv R K).apply_symm_apply D)

end WeilDivisor

end AlgebraicGeometry

end TauCeti
