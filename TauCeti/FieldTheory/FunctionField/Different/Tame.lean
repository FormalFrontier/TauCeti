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
the two hypotheses are stated for the centre `𝔓` of `P'` on `𝒪'_P` over the maximal ideal of the
discrete valuation ring `𝒪_P`, whose residue ring is the residue field of `P`
(`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal`).  This is the same ideal-theoretic
reading of the residue extension that `TauCeti.Place.differentExponent_eq_zero_iff` uses for
unramifiedness.  The theorem behind it is `TauCeti.not_pow_ramificationIdx_dvd_differentIdeal`.

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

/-- **Dedekind's different theorem in the tame case** (Stichtenoth, Theorem 3.5.1(b)): at a place
`P'` whose local model has separable residue extension and whose ramification index is invertible
in the residue field of `P`, the different exponent is exactly one less than the ramification
index.  It is stated as `e(P' ∣ P) = d(P' ∣ P) + 1` so that no truncated subtraction of natural
numbers appears.

The residue extension is read on the local model, between the residue ring of the maximal ideal of
the discrete valuation ring `𝒪_P` — which is the residue field of `P`, by
`TauCeti.Place.center_restrict_asIdeal_eq_maximalIdeal` — and the residue ring of the centre of
`P'` on `𝒪'_P`.  Both hypotheses are essential: without tameness the place is wild and
`d(P' ∣ P) ≥ e(P' ∣ P)`, and without residue separability
`TauCeti.Place.differentExponent_eq_zero_iff` already fails at `e = 1`. -/
theorem ramificationIdx_eq_differentExponent_add_one
    [Algebra.IsSeparable
      (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
      (integralClosure ((P'.restrict k F).integers) F' ⧸ (centerIntegralClosure k F P').asIdeal)]
    (htame : ((ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠ 0) :
    ramificationIdx F P' = differentExponent k F P' + 1 := by
  have hS := algebraMap_mem_integers_of_mem_integralClosure k F P'
  have hpbot : IsLocalRing.maximalIdeal ((P'.restrict k F).integers) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field _
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
    [Algebra.IsSeparable
      (((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers))
      (integralClosure ((P'.restrict k F).integers) F' ⧸
        (Place.centerIntegralClosure k F P').asIdeal)]
    (htame : ((Place.ramificationIdx F P' : ℕ) :
      ((P'.restrict k F).integers) ⧸ IsLocalRing.maximalIdeal ((P'.restrict k F).integers)) ≠ 0) :
    (different k' F' hF).coeff P' + 1 = (Place.ramificationIdx F P' : ℤ) := by
  rw [coeff_different]
  exact_mod_cast (Place.ramificationIdx_eq_differentExponent_add_one k F P' htame).symm

end Divisor

end TauCeti
