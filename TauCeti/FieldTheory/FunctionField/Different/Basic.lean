/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension

/-!
# The different exponent of a place

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite and
separable, and let `P'` be a place of `F' / k'` lying over the place `P = P'.restrict k F` of
`F / k`.  Stichtenoth attaches to that pair the **different exponent** `d(P' ∣ P)`, read off the
complementary module of the local extension `𝒪_P ⊆ 𝒪'_P`, where `𝒪_P` is the valuation ring of `P`
and `𝒪'_P` its integral closure in `F'`.  This file defines it and proves the two facts that make
it a divisor-theoretic invariant: **Dedekind's different theorem**, `d(P' ∣ P) ≥ e(P' ∣ P) - 1`,
and the vanishing criterion that singles out the unramified places.

The complementary module `C_P = {z | Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P}` is an invertible fractional
`𝒪'_P`-ideal whose inverse is Mathlib's `differentIdeal 𝒪_P 𝒪'_P`, so Stichtenoth's `-v_{P'}(t)`
for a generator `t` of `C_P` is the multiplicity of the centre of `P'` on `𝒪'_P` in that ideal.
That multiplicity is the definition used here, and no complementary module is rebuilt.

The local model `𝒪_P ⊆ 𝒪'_P` is a pair of affine models in the sense of
`TauCeti/FieldTheory/FunctionField/AffineModel/`, the smallest one that sees `P`: `𝒪_P` is a
discrete valuation ring with fraction field `F`, and `𝒪'_P` is a Dedekind domain, module-finite
over it, with fraction field `F'`.  The identification of the extension-theoretic data of `P'`
with the ideal-theoretic data of its centre on `𝒪'_P` is then the affine-model dictionary of
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean`.  The action of `𝒪_P` on `F'` is
deliberately not a global instance — for `F' = F` it would compete with the action of a valuation
subring on its own field — so it, and the scalar tower it sits in, are provided as `local`
instances to be reinstalled by consumers.

Separability of `F' / F` is the hypothesis of record for the different: without it the
complementary module degenerates.  Nothing here needs an exactness hypothesis on the constant
fields, and nothing needs `k` perfect.

## Main definitions

* `TauCeti.Place.algebraIntegersExtension` and `TauCeti.Place.isScalarTowerIntegersExtension`: the
  action of the valuation ring of a place of `F / k` on an extension field `F'`, to be installed
  with `attribute [local instance 10]`.
* `TauCeti.Place.centerIntegralClosure`: the centre of `P'` on the local model `𝒪'_P`.
* `TauCeti.Place.differentExponent`: the different exponent `d(P' ∣ P)` (Stichtenoth,
  Definition 3.4.3).

## Main results

* `TauCeti.Place.pow_dvd_differentIdeal_iff_le_differentExponent`: the characteristic property of
  the different exponent, `𝔓'^n ∣ differentIdeal 𝒪_P 𝒪'_P ↔ n ≤ d(P' ∣ P)`.
* `TauCeti.Place.ramificationIdx_le_differentExponent_add_one`: **Dedekind's different theorem**
  (Stichtenoth, Theorem 3.5.1(a)), in the subtraction-free form `e(P' ∣ P) ≤ d(P' ∣ P) + 1`.
* `TauCeti.Place.differentExponent_pos_of_one_lt_ramificationIdx`: a ramified place has positive
  different exponent — the direction of Stichtenoth's Corollary 3.5.5 that needs no hypothesis on
  the residue extension.
* `TauCeti.Place.differentExponent_eq_zero_iff`: the different exponent vanishes exactly at the
  places where the local model is unramified, in Mathlib's `Algebra.IsUnramifiedAt` sense, which
  asks for a separable residue extension as well as `e(P' ∣ P) = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.4.1, Proposition 3.4.2, Definition 3.4.3, Theorem 3.5.1 and Corollary 3.5.5.
-/

public section

open IsDedekindDomain

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra F F']

section LocalModel

variable (F') (P : Place k F)

/-- **The valuation ring of a place of `F / k` acts on an extension field `F'`**, through `F`.

This is not a global instance: for `F' = F` it would compete with the action of a valuation
subring on its own field.  Install it, together with
`TauCeti.Place.isScalarTowerIntegersExtension`, with `attribute [local instance 10]` in any file
that works with the local model of the extension at `P` — at low priority, so that the case
`F' = F` still resolves to the valuation subring's own action, as the fraction-field instances
expect. -/
@[instance_reducible]
noncomputable def algebraIntegersExtension : Algebra (P.integers) F' :=
  ((algebraMap F F').comp (algebraMap (P.integers) F)).toAlgebra

attribute [local instance 10] algebraIntegersExtension

/-- The action of `TauCeti.Place.algebraIntegersExtension` on `F'` factors through `F`. -/
theorem isScalarTowerIntegersExtension : IsScalarTower (P.integers) F F' :=
  .of_algebraMap_eq fun _ ↦ rfl

attribute [local instance 10] isScalarTowerIntegersExtension

theorem algebraMap_integersExtension_injective :
    Function.Injective (algebraMap (P.integers) F') := by
  rw [IsScalarTower.algebraMap_eq (P.integers) F F', RingHom.coe_comp]
  exact (algebraMap F F').injective.comp (FaithfulSMul.algebraMap_injective (P.integers) F)

instance isTorsionFree_integersExtension : Module.IsTorsionFree (P.integers) F' :=
  Module.IsTorsionFree.comap (M := F') (algebraMap (P.integers) F')
    (fun _ hr ↦ isRegular_iff_ne_zero'.mpr fun h ↦ isRegular_iff_ne_zero'.mp hr
      (algebraMap_integersExtension_injective F' P (by simpa using h)))
    (fun r m ↦ (Algebra.smul_def r m).symm)

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- The local model `𝒪'_P` — the integral closure of `𝒪_P` in `F'` — has fraction field `F'`. -/
instance isFractionRing_integralClosure :
    IsFractionRing (integralClosure (P.integers) F') F' :=
  IsIntegralClosure.isFractionRing_of_finite_extension (P.integers) F F' _

/-- The local model `𝒪'_P` is a Dedekind domain. -/
instance isDedekindDomain_integralClosure :
    IsDedekindDomain (integralClosure (P.integers) F') :=
  integralClosure.isDedekindDomain (A := P.integers) (K := F) (L := F')

/-- The local model `𝒪'_P` is module-finite over `𝒪_P`. -/
instance moduleFinite_integralClosure :
    Module.Finite (P.integers) (integralClosure (P.integers) F') :=
  IsIntegralClosure.finite (A := P.integers) (K := F) (L := F') _

/-- Separability of `F' / F`, transported to the fraction fields over which Mathlib states the
different ideal. -/
instance isSeparable_fractionRing_integralClosure :
    Algebra.IsSeparable (FractionRing (P.integers))
      (FractionRing (integralClosure (P.integers) F')) := by
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (P.integers) F).symm.toRingEquiv
    (FractionRing.algEquiv (integralClosure (P.integers) F') F').symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext (P.integers)⁰
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply (P.integers) (integralClosure (P.integers) F') F',
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

end LocalModel

section DifferentExponent

variable [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']

variable (k F) (P' : Place k' F')

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The local model `𝒪'_P` of `F' / k'` at `P'` consists of functions regular at `P'`**: its
elements are integral over `𝒪_P`, whose functions are regular at `P'`. -/
theorem algebraMap_mem_integers_of_mem_integralClosure
    (b : integralClosure ((P'.restrict k F).integers) F') :
    algebraMap (integralClosure ((P'.restrict k F).integers) F') F' b ∈ P'.integers := by
  rw [Subalgebra.algebraMap_eq]
  exact P'.mem_integers_of_isIntegral (R := ((P'.restrict k F).integers))
    (fun a ↦ (mem_integers_restrict_iff k F P' (a : F)).mp a.2) b.2

variable [Algebra.IsSeparable F F']

/-- **The centre of `P'` on the local model `𝒪'_P`**: the height one prime of the integral closure
of `𝒪_P` in `F'` consisting of the functions that vanish at `P'`. -/
noncomputable def centerIntegralClosure :
    HeightOneSpectrum (integralClosure ((P'.restrict k F).integers) F') :=
  P'.center (algebraMap_mem_integers_of_mem_integralClosure k F P')

theorem centerIntegralClosure_def : centerIntegralClosure k F P' =
    P'.center (algebraMap_mem_integers_of_mem_integralClosure k F P') := (rfl)

/-- **The different exponent `d(P' ∣ P)`** of a place `P'` of `F' / k'` over the place
`P = P'.restrict k F` of `F / k` (Stichtenoth, Definition 3.4.3), for `F' / F` finite and
separable: the multiplicity with which the centre of `P'` on the local model `𝒪'_P` divides the
different ideal of `𝒪'_P` over `𝒪_P`.

Stichtenoth defines it as `-v_{P'}(t)` for a generator `t` of the complementary module
`C_P = {z | Tr_{F'/F} (z · 𝒪'_P) ⊆ 𝒪_P}`; that module is the inverse of the different ideal, so
the two readings agree. -/
noncomputable def differentExponent : ℕ :=
  multiplicity (centerIntegralClosure k F P').asIdeal
    (differentIdeal ((P'.restrict k F).integers) (integralClosure ((P'.restrict k F).integers) F'))

theorem differentExponent_def : differentExponent k F P' =
    multiplicity (centerIntegralClosure k F P').asIdeal (differentIdeal
      ((P'.restrict k F).integers) (integralClosure ((P'.restrict k F).integers) F')) := (rfl)

/-- **The characteristic property of the different exponent**: the `n`-th power of the centre of
`P'` divides the different ideal of the local model exactly when `n ≤ d(P' ∣ P)`. -/
theorem pow_dvd_differentIdeal_iff_le_differentExponent {n : ℕ} :
    (centerIntegralClosure k F P').asIdeal ^ n ∣ differentIdeal ((P'.restrict k F).integers)
        (integralClosure ((P'.restrict k F).integers) F') ↔ n ≤ differentExponent k F P' :=
  (FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (centerIntegralClosure k F P').ne_bot
      (centerIntegralClosure k F P').isPrime) differentIdeal_ne_bot).pow_dvd_iff_le_multiplicity

/-- **Dedekind's different theorem, first part** (Stichtenoth, Theorem 3.5.1(a)): the different
exponent of a place is at least one less than its ramification index.  It is stated as
`e(P' ∣ P) ≤ d(P' ∣ P) + 1` so that no truncated subtraction of natural numbers appears.

Unlike the second part of that theorem — equality exactly in the tame case — this half needs no
hypothesis beyond separability of `F' / F`, and in particular none on the residue extension. -/
theorem ramificationIdx_le_differentExponent_add_one :
    ramificationIdx F P' ≤ differentExponent k F P' + 1 := by
  have hS := algebraMap_mem_integers_of_mem_integralClosure k F P'
  set 𝔭 := (P'.restrict k F).center
    (algebraMap_mem_integers_restrict (R := ((P'.restrict k F).integers)) k F P' hS)
  set 𝔓 := centerIntegralClosure k F P' with h𝔓
  have hlies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
    center_liesOver (R := ((P'.restrict k F).integers)) k F P' hS
  have hmax : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  -- the ramification index of `P'` over `P` is the ramification index of the centres
  have hidx : Ideal.ramificationIdx' (S := (integralClosure ((P'.restrict k F).integers) F'))
      𝔭.asIdeal 𝔓.asIdeal = ramificationIdx F P' := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔭.asIdeal 𝔓.asIdeal 𝔭.ne_bot,
      ramificationIdx_eq_ramificationIdx_center (R := ((P'.restrict k F).integers)) k F P' hS,
      h𝔓, centerIntegralClosure_def]
  -- Mathlib's `𝔓^(e-1) ∣ 𝔡` for the extension of Dedekind domains `𝒪_P ⊆ 𝒪'_P`
  have hdvd : 𝔓.asIdeal ^ (ramificationIdx F P' - 1) ∣ differentIdeal
      ((P'.restrict k F).integers) (integralClosure ((P'.restrict k F).integers) F') :=
    pow_sub_one_dvd_differentIdeal _ 𝔓.asIdeal _ 𝔭.ne_bot
      (Ideal.dvd_iff_le.mpr (hidx ▸ Ideal.le_pow_ramificationIdx'))
  have := (pow_dvd_differentIdeal_iff_le_differentExponent k F P').mp hdvd
  have hpos := ramificationIdx_pos F P'
  omega

/-- **A ramified place has a positive different exponent**, so it lies in the support of the
different divisor (Stichtenoth, Corollary 3.5.5; this direction needs no hypothesis on the residue
extension). -/
theorem differentExponent_pos_of_one_lt_ramificationIdx (h : 1 < ramificationIdx F P') :
    0 < differentExponent k F P' := by
  have := ramificationIdx_le_differentExponent_add_one k F P'
  omega

/-- **The different exponent of `P'` vanishes exactly at the unramified places** (Stichtenoth,
Corollary 3.5.5).  Unramifiedness is Mathlib's `Algebra.IsUnramifiedAt` for the local model at the
centre of `P'`, which asks for a separable residue extension as well as `e(P' ∣ P) = 1`; over an
imperfect residue field the two conditions genuinely differ, and
`TauCeti.Place.differentExponent_pos_of_one_lt_ramificationIdx` is the half that survives without
the separability. -/
theorem differentExponent_eq_zero_iff :
    differentExponent k F P' = 0 ↔ Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (centerIntegralClosure k F P').asIdeal := by
  have : (centerIntegralClosure k F P').asIdeal.IsPrime := (centerIntegralClosure k F P').isPrime
  have h := pow_dvd_differentIdeal_iff_le_differentExponent (n := 1) k F P'
  rw [pow_one] at h
  rw [← not_dvd_differentIdeal_iff, h]
  omega

end DifferentExponent

end Place

end TauCeti

end
