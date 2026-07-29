/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor

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

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The additive submonoid of invertible fractional ideals contained in `R`. -/
def integralFractionalIdealSubmonoid :
    AddSubmonoid (Additive (FractionalIdeal R⁰ K)ˣ) where
  carrier := {I | Units.val (Additive.toMul I) ≤ 1}
  zero_mem' := by simp
  add_mem' {I J} hI hJ := by
    simpa only [Set.mem_setOf_eq, toMul_add, Units.val_mul] using mul_le_one' hI hJ

/-- Membership in `integralFractionalIdealSubmonoid` means that the fractional ideal is contained
in the base ring. -/
@[simp]
lemma mem_integralFractionalIdealSubmonoid
    (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    I ∈ integralFractionalIdealSubmonoid R K ↔
      Units.val (Additive.toMul I) ≤ 1 :=
  Iff.rfl

variable {R K}

/-- If the divisor of an invertible fractional ideal is effective, then the fractional ideal is
integral. This is the converse of `isEffective_fractionalIdealDivisor_of_le_one`. -/
lemma le_one_of_isEffective_fractionalIdealDivisor
    (I : Additive (FractionalIdeal R⁰ K)ˣ)
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
lemma isEffective_fractionalIdealDivisor_iff
    (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    IsEffective (fractionalIdealDivisor R K I) ↔
      Units.val (Additive.toMul I) ≤ 1 :=
  ⟨le_one_of_isEffective_fractionalIdealDivisor I,
    isEffective_fractionalIdealDivisor_of_le_one I⟩

/-- The divisor of an invertible fractional ideal is effective exactly when that ideal belongs to
the integral fractional-ideal submonoid. -/
lemma isEffective_fractionalIdealDivisor_iff_mem
    (I : Additive (FractionalIdeal R⁰ K)ˣ) :
    IsEffective (fractionalIdealDivisor R K I) ↔
      I ∈ integralFractionalIdealSubmonoid R K := by
  rw [mem_integralFractionalIdealSubmonoid, isEffective_fractionalIdealDivisor_iff]

variable (R K)

/-- The affine Weil--Cartier equivalence restricted to positive objects: integral invertible
fractional ideals correspond exactly to effective Weil divisors. -/
@[expose] noncomputable def integralFractionalIdealDivisorAddEquiv :
    integralFractionalIdealSubmonoid R K ≃+
      effectiveSubmonoid (HeightOneSpectrum R) where
  toFun I :=
    ⟨fractionalIdealDivisorAddEquiv R K I,
      (mem_effectiveSubmonoid _).mpr <| by
        simpa only [fractionalIdealDivisorAddEquiv_apply] using
          (isEffective_fractionalIdealDivisor_iff_mem
            (R := R) (K := K) (I : Additive (FractionalIdeal R⁰ K)ˣ)).mpr I.property⟩
  invFun D :=
    ⟨(fractionalIdealDivisorAddEquiv R K).symm D,
      (isEffective_fractionalIdealDivisor_iff_mem
        (R := R) (K := K)
        ((fractionalIdealDivisorAddEquiv R K).symm D)).mp <| by
        simpa only [← fractionalIdealDivisorAddEquiv_apply, AddEquiv.apply_symm_apply]
          using (mem_effectiveSubmonoid (D : WeilDivisor (HeightOneSpectrum R))).mp D.property⟩
  left_inv I := Subtype.ext <| (fractionalIdealDivisorAddEquiv R K).symm_apply_apply I
  right_inv D := Subtype.ext <| (fractionalIdealDivisorAddEquiv R K).apply_symm_apply D
  map_add' I J := Subtype.ext <|
    (fractionalIdealDivisorAddEquiv R K).map_add
      (I : Additive (FractionalIdeal R⁰ K)ˣ) J

/-- The restricted equivalence agrees with `fractionalIdealDivisor` after forgetting
effectivity. -/
@[simp]
lemma coe_integralFractionalIdealDivisorAddEquiv
    (I : integralFractionalIdealSubmonoid R K) :
    ((integralFractionalIdealDivisorAddEquiv R K I :
        effectiveSubmonoid (HeightOneSpectrum R)) :
      WeilDivisor (HeightOneSpectrum R)) =
      fractionalIdealDivisor R K I :=
  fractionalIdealDivisorAddEquiv_apply
    (R := R) (K := K) (I : Additive (FractionalIdeal R⁰ K)ˣ)

end WeilDivisor

end AlgebraicGeometry

end TauCeti
