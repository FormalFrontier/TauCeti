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
    change Units.val (Additive.toMul I) ≤ 1 at hI
    change Units.val (Additive.toMul J) ≤ 1 at hJ
    change Units.val (Additive.toMul (I + J)) ≤ 1
    simpa only [toMul_add, Units.val_mul] using mul_le_one' hI hJ

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

variable (R K)

private lemma map_integralFractionalIdealSubmonoid :
    AddSubmonoid.map (fractionalIdealDivisorAddEquiv R K).toAddMonoidHom
        (integralFractionalIdealSubmonoid R K) =
      effectiveSubmonoid (HeightOneSpectrum R) := by
  ext D
  constructor
  · rintro ⟨I, hI, rfl⟩
    rw [mem_effectiveSubmonoid]
    change IsEffective (fractionalIdealDivisorAddEquiv R K I)
    rw [fractionalIdealDivisorAddEquiv_apply, isEffective_fractionalIdealDivisor_iff]
    change Units.val (Additive.toMul I) ≤ 1 at hI
    exact hI
  · intro hD
    rw [mem_effectiveSubmonoid] at hD
    obtain ⟨I, rfl⟩ := fractionalIdealDivisor_surjective R K D
    refine ⟨I, ?_, ?_⟩
    · change Units.val (Additive.toMul I) ≤ 1
      exact (isEffective_fractionalIdealDivisor_iff I).mp hD
    · change fractionalIdealDivisorAddEquiv R K I = fractionalIdealDivisor R K I
      exact fractionalIdealDivisorAddEquiv_apply (R := R) (K := K) I

/-- The affine Weil--Cartier equivalence restricted to positive objects: integral invertible
fractional ideals correspond exactly to effective Weil divisors. -/
noncomputable def integralFractionalIdealDivisorAddEquiv :
    integralFractionalIdealSubmonoid R K ≃+
      effectiveSubmonoid (HeightOneSpectrum R) :=
  ((fractionalIdealDivisorAddEquiv R K).addSubmonoidMap
      (integralFractionalIdealSubmonoid R K)).trans
    (AddEquiv.addSubmonoidCongr (map_integralFractionalIdealSubmonoid R K))

/-- The restricted equivalence agrees with `fractionalIdealDivisor` after forgetting
effectivity. -/
@[simp]
lemma coe_integralFractionalIdealDivisorAddEquiv
    (I : integralFractionalIdealSubmonoid R K) :
    ((integralFractionalIdealDivisorAddEquiv R K I :
        effectiveSubmonoid (HeightOneSpectrum R)) :
      WeilDivisor (HeightOneSpectrum R)) =
      fractionalIdealDivisor R K I := by
  rw [integralFractionalIdealDivisorAddEquiv, AddEquiv.trans_apply]
  change fractionalIdealDivisorAddEquiv R K I = fractionalIdealDivisor R K I
  rw [fractionalIdealDivisorAddEquiv_apply]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
