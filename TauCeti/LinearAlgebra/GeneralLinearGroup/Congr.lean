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

variable {R M M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M₁]
  [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- The linear automorphism underlying the general linear group element
`(generalLinearEquiv R M).symm f` is `f` itself.

Mathlib records how `generalLinearEquiv` computes on coercions (`coeFn_generalLinearEquiv`,
`coe_toLinearEquiv`) rather than at the level of `M ≃ₗ[R] M`, so both evaluation lemmas for
`congrAut` below need this bridge; it is stated once here. -/
private theorem toLinearEquiv_generalLinearEquiv_symm (f : M ≃ₗ[R] M) :
    ((generalLinearEquiv R M).symm f).toLinearEquiv = f := by
  ext m
  rw [coe_toLinearEquiv, ← coeFn_generalLinearEquiv]
  exact DFunLike.congr_fun ((generalLinearEquiv R M).apply_symm_apply f) m

/-- Conjugation by a linear equivalence `e : M₁ ≃ₗ[R] M₂`, as an isomorphism of automorphism
groups: Mathlib's `LinearMap.GeneralLinearGroup.congrLinearEquiv` read through
`LinearMap.GeneralLinearGroup.generalLinearEquiv`.

The two evaluation lemmas below are its characteristic API. -/
def congrAut (e : M₁ ≃ₗ[R] M₂) : (M₁ ≃ₗ[R] M₁) ≃* (M₂ ≃ₗ[R] M₂) :=
  ((generalLinearEquiv R M₁).symm.trans (congrLinearEquiv e)).trans (generalLinearEquiv R M₂)

/-- Conjugating `f` by `e` sends `m` to `e (f (e.symm m))`. -/
@[simp]
theorem congrAut_apply (e : M₁ ≃ₗ[R] M₂) (f : M₁ ≃ₗ[R] M₁) (m : M₂) :
    congrAut e f m = e (f (e.symm m)) := by
  rw [congrAut, MulEquiv.trans_apply, MulEquiv.trans_apply]
  simp only [congrLinearEquiv_apply, coeFn_generalLinearEquiv, coe_ofLinearEquiv,
    LinearEquiv.trans_apply, toLinearEquiv_generalLinearEquiv_symm]

/-- Inverse conjugation by `e` sends `m` to `e.symm (g (e m))`. -/
@[simp]
theorem congrAut_symm_apply (e : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₂) (m : M₁) :
    (congrAut e).symm g m = e.symm (g (e m)) := by
  rw [congrAut, MulEquiv.symm_trans_apply, MulEquiv.symm_trans_apply, congrLinearEquiv_symm]
  simp only [congrLinearEquiv_apply, MulEquiv.symm_symm, coeFn_generalLinearEquiv,
    coe_ofLinearEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    toLinearEquiv_generalLinearEquiv_symm]

end LinearEquiv

end TauCeti
