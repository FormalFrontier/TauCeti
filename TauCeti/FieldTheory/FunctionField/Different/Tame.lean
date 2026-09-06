/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Divisor
public import TauCeti.RingTheory.DedekindDomain.Different

/-!
# The different exponent of a tame place

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable, and let `P'` be a place of `F' / k'` over `P = P'.restrict k F`.  Dedekind's different
theorem (Stichtenoth, Theorem 3.5.1) says that `d(P' ∣ P) ≥ e(P' ∣ P) - 1` always, with equality
exactly when the place is **tame**.  The inequality is
`TauCeti.Place.ramificationIdx_le_differentExponent_add_one`; this file supplies the equality,
`e(P' ∣ P) = d(P' ∣ P) + 1`, at a place where the residue extension of the local model is
separable and the residue characteristic does not divide `e(P' ∣ P)`.

Everything is read on the local model `𝒪_P ⊆ 𝒪'_P` of
`TauCeti/FieldTheory/FunctionField/Different/Basic.lean`, where the different exponent lives, so
the two hypotheses are stated for the centre `𝔓` of `P'` on `𝒪'_P` and a maximal ideal `𝔭` of
`𝒪_P` that `𝔓` lies over — necessarily the maximal ideal of the discrete valuation ring `𝒪_P`,
whose residue ring is the residue field of `P`.  This is the same ideal-theoretic reading of the
residue extension that `TauCeti.Place.differentExponent_eq_zero_iff` uses for unramifiedness.  The
theorem behind it is `TauCeti.not_pow_ramificationIdx_dvd_differentIdeal`.

Tameness is genuinely needed, and so is residue separability: `d = e - 1` fails in the wild case
(Stichtenoth, Corollary 3.5.5 records `d ≥ e` there), and over an imperfect residue field an
unramified-looking place with inseparable residue extension already has `d > 0`.

## Main results

* `TauCeti.Place.ramificationIdx_eq_differentExponent_add_one`: **Dedekind's different theorem in
  the tame case** (Stichtenoth, Theorem 3.5.1(b)), in the subtraction-free form
  `e(P' ∣ P) = d(P' ∣ P) + 1`.
* `TauCeti.Divisor.coeff_different_add_one_eq_ramificationIdx`: the same statement read on the
  different divisor.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1 and Corollary 3.5.5.
-/

public section

open IsDedekindDomain

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k F] [Algebra F F'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F']

attribute [local instance 10] Place.algebraIntegersExtension
  Place.isScalarTowerIntegersExtension

namespace Place

variable (k F) (P' : Place k' F')

/-- **The prime of `𝒪_P` below the centre of `P'` on the local model is the maximal ideal of
`𝒪_P`**: the residue extension that the different exponent reads is the residue-field extension of
the two places. -/
theorem center_restrict_asIdeal_eq_maximalIdeal :
    ((P'.restrict k F).center (algebraMap_mem_integers_restrict
        (R := ((P'.restrict k F).integers)) k F P'
        (algebraMap_mem_integers_of_mem_integralClosure k F P'))).asIdeal
      = IsLocalRing.maximalIdeal ((P'.restrict k F).integers) := by
  ext f
  rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
  exact Iff.rfl

/-- The centre of `P'` on the local model lies over the maximal ideal of `𝒪_P`, so the hypotheses
of `TauCeti.Place.ramificationIdx_eq_differentExponent_add_one` can always be read at
`𝔭 = 𝔪_P`. -/
instance centerIntegralClosure_liesOver_maximalIdeal :
    (centerIntegralClosure k F P').asIdeal.LiesOver
      (IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) := by
  rw [← center_restrict_asIdeal_eq_maximalIdeal k F P', centerIntegralClosure_def]
  exact center_liesOver k F P' _

/-- **Dedekind's different theorem in the tame case** (Stichtenoth, Theorem 3.5.1(b)): at a place
`P'` whose local model has separable residue extension and whose ramification index is invertible
in the residue ring of the prime below, the different exponent is exactly one less than the
ramification index.  It is stated as `e(P' ∣ P) = d(P' ∣ P) + 1` so that no truncated subtraction
of natural numbers appears.

The ideal `𝔭` is the maximal ideal of the discrete valuation ring `𝒪_P`; the `LiesOver` hypothesis
identifies it as the prime of `𝒪_P` below the centre of `P'` on the local model, and
`𝒪_P ⧸ 𝔭` is then the residue field of `P`.  Both hypotheses are essential: without tameness the
place is wild and `d(P' ∣ P) ≥ e(P' ∣ P)`, and without residue separability
`TauCeti.Place.differentExponent_eq_zero_iff` already fails at `e = 1`. -/
theorem ramificationIdx_eq_differentExponent_add_one
    (𝔭 : Ideal ((P'.restrict k F).integers)) [𝔭.IsMaximal]
    [(centerIntegralClosure k F P').asIdeal.LiesOver 𝔭]
    [Algebra.IsSeparable (((P'.restrict k F).integers) ⧸ 𝔭)
      (integralClosure ((P'.restrict k F).integers) F' ⧸ (centerIntegralClosure k F P').asIdeal)]
    (htame : ((ramificationIdx F P' : ℕ) : ((P'.restrict k F).integers) ⧸ 𝔭) ≠ 0) :
    ramificationIdx F P' = differentExponent k F P' + 1 := by
  have hS := algebraMap_mem_integers_of_mem_integralClosure k F P'
  have hpbot : 𝔭 ≠ ⊥ := by
    rw [IsLocalRing.eq_maximalIdeal ‹𝔭.IsMaximal›]
    exact IsDiscreteValuationRing.not_a_field _
  have hmax : (centerIntegralClosure k F P').asIdeal.IsMaximal :=
    (centerIntegralClosure k F P').isPrime.isMaximal (centerIntegralClosure k F P').ne_bot
  have hidx : (centerIntegralClosure k F P').asIdeal.ramificationIdx
      ((P'.restrict k F).integers) = ramificationIdx F P' := by
    rw [centerIntegralClosure_def]
    exact (ramificationIdx_eq_ramificationIdx_center
      (R := ((P'.restrict k F).integers)) k F P' hS).symm
  have hnot := not_pow_ramificationIdx_dvd_differentIdeal ((P'.restrict k F).integers) hpbot
    (centerIntegralClosure k F P').asIdeal (by rwa [hidx])
  rw [hidx] at hnot
  have hle := ramificationIdx_le_differentExponent_add_one k F P'
  have hlt : ¬ ramificationIdx F P' ≤ differentExponent k F P' := fun h ↦
    hnot ((pow_dvd_differentIdeal_iff_le_differentExponent k F P').mpr h)
  omega

end Place

namespace Divisor

/-- **The different divisor at a tame place** (Stichtenoth, Theorem 3.5.1(b) and Remark 3.4.4):
the coefficient of a tame place `P'` in `Diff(F'/F)` is `e(P' ∣ P) - 1`, stated without
subtraction. -/
theorem coeff_different_add_one_eq_ramificationIdx (hF : IsFunctionField k F) (P' : Place k' F')
    (𝔭 : Ideal ((P'.restrict k F).integers)) [𝔭.IsMaximal]
    [(Place.centerIntegralClosure k F P').asIdeal.LiesOver 𝔭]
    [Algebra.IsSeparable (((P'.restrict k F).integers) ⧸ 𝔭)
      (integralClosure ((P'.restrict k F).integers) F' ⧸
        (Place.centerIntegralClosure k F P').asIdeal)]
    (htame : ((Place.ramificationIdx F P' : ℕ) : ((P'.restrict k F).integers) ⧸ 𝔭) ≠ 0) :
    (different k' F' hF).coeff P' + 1 = (Place.ramificationIdx F P' : ℤ) := by
  rw [coeff_different]
  exact_mod_cast
    (Place.ramificationIdx_eq_differentExponent_add_one k F P' 𝔭 htame).symm

end Divisor

end TauCeti
