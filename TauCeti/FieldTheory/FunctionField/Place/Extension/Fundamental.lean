/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension

/-!
# The fundamental identity at an arbitrary place

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite and
separable; of the constant fields only integrality of `k' / k` is asked.  This file proves
**the fundamental identity**

`∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`

at **every** place `P` of `F / k`, upgrading the inequality of
`TauCeti/FieldTheory/FunctionField/Place/Extension/Fibre.lean` and removing the restriction of
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean` to the places of a chosen finite
chart.

The affine model used is the smallest one that sees `P`: its own valuation ring `𝒪_P`, which is a
discrete valuation ring with fraction field `F`, together with the integral closure of `𝒪_P` in
`F'`.  Separability of `F' / F` enters exactly once, to make that integral closure a finite
`𝒪_P`-module — the hypothesis of Mathlib's `Ideal.sum_ramification_inertia_eq_finrank`, which the
affine-model reconciliation consumes.  No separability-free finiteness of a normalization is
available, so the unconditional form of Stichtenoth's Theorem 3.1.11 waits on one.

## Main result

* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`: the
  fundamental identity at an arbitrary place, for a separable extension (Stichtenoth,
  Theorem 3.1.11).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.1.11.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [Algebra.IsIntegral k k']

variable (k F)

/-- **The fundamental identity** (Stichtenoth, Theorem 3.1.11) at an arbitrary place `P` of
`F / k`, for an extension `F' / k'` whose extension of function fields `F' / F` is finite and
**separable**: the ramification indices and relative degrees of the places of `F' / k'` lying
over `P` satisfy `∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`, which is finite by
`TauCeti.Place.finite_setOf_restrict_eq`.

Separability is the hypothesis of Mathlib's finiteness theorem for integral closures, and is used
only there; the identity itself holds for every finite extension. -/
theorem sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable (P : Place k F)
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  -- The valuation ring of `P` is an affine model of `F / k` carrying `P` itself: it is a discrete
  -- valuation ring, hence Dedekind, and `F` is its fraction field.
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ by
    rw [ValuationSubring.algebraMap_apply]
    exact r.2
  let _ : Algebra P.integers F' := ((algebraMap F F').comp (algebraMap P.integers F)).toAlgebra
  have : IsScalarTower P.integers F F' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  -- The integral closure `S` of `𝒪_P` in `F'` is the matching affine model of `F' / k'`: it
  -- contains the constants `k'`, because they are integral over `k ⊆ 𝒪_P`.
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsFractionRing (integralClosure P.integers F') F' :=
    IsIntegralClosure.isFractionRing_of_finite_extension P.integers F F' _
  have : IsDedekindDomain (integralClosure P.integers F') :=
    integralClosure.isDedekindDomain (A := P.integers) (K := F) (L := F')
  have : Module.Finite P.integers (integralClosure P.integers F') :=
    IsIntegralClosure.finite (A := P.integers) (K := F) (L := F') _
  -- `P` is the place of the maximal ideal of `𝒪_P`, so the affine-model identity applies to it.
  refine sum_ramificationIdx_mul_relativeDegree_eq_finrank (S := integralClosure P.integers F')
    k F (P.center hR) fun P' ↦ ?_
  rw [hs P', ofPrime_center]

end Place

end TauCeti
