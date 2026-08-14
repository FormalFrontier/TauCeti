/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Conjugating automorphism groups along a linear equivalence

Mathlib conjugates general linear groups with
`LinearMap.GeneralLinearGroup.congrLinearEquiv : GL R M₁ ≃* GL R M₂`, and identifies `GL R M` with
the automorphisms `M ≃ₗ[R] M` through `LinearMap.GeneralLinearGroup.generalLinearEquiv`. Groups of
linear automorphisms cut out by a structure they preserve — an orthogonal group, an isometry
group — are subgroups of `M ≃ₗ[R] M` rather than of `GL R M`, so what they need is the composite of
those two, which this file records as `TauCeti.LinearEquiv.congrAut`.

## Main definitions

* `TauCeti.LinearEquiv.congrAut`: conjugation by `e : M₁ ≃ₗ[R] M₂`, as an isomorphism
  `(M₁ ≃ₗ[R] M₁) ≃* (M₂ ≃ₗ[R] M₂)`.
-/

public section

namespace TauCeti

namespace LinearEquiv

open LinearMap.GeneralLinearGroup

variable {R M₁ M₂ : Type*} [CommSemiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂]

/-- Conjugation by a linear equivalence `e : M₁ ≃ₗ[R] M₂`, as an isomorphism of automorphism
groups: Mathlib's `LinearMap.GeneralLinearGroup.congrLinearEquiv` read through
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.

The two evaluation lemmas below are its characteristic API. -/
def congrAut (e : M₁ ≃ₗ[R] M₂) : (M₁ ≃ₗ[R] M₁) ≃* (M₂ ≃ₗ[R] M₂) :=
  ((generalLinearEquiv R M₁).symm.trans (congrLinearEquiv e)).trans (generalLinearEquiv R M₂)

@[simp]
theorem congrAut_apply (e : M₁ ≃ₗ[R] M₂) (f : M₁ ≃ₗ[R] M₁) (m : M₂) :
    congrAut e f m = e (f (e.symm m)) := by
  change (generalLinearEquiv R M₂
    (congrLinearEquiv e ((generalLinearEquiv R M₁).symm f))) m = _
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply]
  rw [show ((generalLinearEquiv R M₁).symm f).toLinearEquiv = f from
    (generalLinearEquiv R M₁).apply_symm_apply f]

@[simp]
theorem congrAut_symm_apply (e : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₂) (m : M₁) :
    (congrAut e).symm g m = e.symm (g (e m)) := by
  change (generalLinearEquiv R M₁
    ((congrLinearEquiv e).symm ((generalLinearEquiv R M₂).symm g))) m = _
  rw [congrLinearEquiv_symm]
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rw [show ((generalLinearEquiv R M₂).symm g).toLinearEquiv = g from
    (generalLinearEquiv R M₂).apply_symm_apply g]

end LinearEquiv

end TauCeti
