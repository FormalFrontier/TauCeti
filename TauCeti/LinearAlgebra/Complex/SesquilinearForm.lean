/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Balancing a complex sesquilinear form against a conjugate-linear map

A sesquilinear form `H` on a complex vector space and a conjugate-linear map `K` of that space are
unrelated data.  This file makes them compatible: the **balanced** form

`balance H K x y = H x y + conj (H (K x) (K y))`

is again sesquilinear -- each argument of the second summand picks up a conjugation from `K`, and
the outer conjugation restores the shape -- and it satisfies

`balance H K (K x) (K y) = conj (balance H K x y)`

as soon as `K ∘ K` is a scalar of modulus one, which an arbitrary `H` need not.  That is the
only property balancing adds: being Hermitian, nonnegative, and definite off the origin all pass
from `H` to `balance H K` unchanged.

## Main definitions

* `LinearMap.balance`: the balanced form `x, y ↦ H x y + conj (H (K x) (K y))`.

## Main results

* `LinearMap.balance_apply`: the defining formula of the balanced form.
* `LinearMap.balance_map_map`: the balanced form is compatible with the map it was balanced
  against, once that map squares to a scalar of modulus one.
* `LinearMap.isSymm_balance`, `LinearMap.isNonneg_balance` and
  `LinearMap.balance_apply_self_ne_zero`: balancing preserves Hermitian symmetry, nonnegativity,
  and definiteness off the origin.
-/

public section

open scoped ComplexOrder

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The **balanced** form of a sesquilinear form `H` against a conjugate-linear map `K`:
`x, y ↦ H x y + conj (H (K x) (K y))`.  Each argument of the second summand picks up a conjugation
from `K`, and the outer conjugation restores the shape of a sesquilinear form, conjugate-linear in
the first argument and linear in the second.  Adding it to `H` is what forces the compatibility
`balance H K (K x) (K y) = conj (balance H K x y)` whenever `K ∘ K` is a scalar of modulus
one. -/
noncomputable def balance (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : V →ₛₗ[starRingEnd ℂ] V) :
    V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => H x y + (starRingEnd ℂ) (H (K x) (K y))
      map_add' := fun y z => by simp only [map_add]; ring
      map_smul' := fun c y => by
        simp only [map_smulₛₗ, RingHom.id_apply, smul_eq_mul, map_mul, Complex.conj_conj]
        ring }
  map_add' x y := by
    ext z
    simp only [map_add, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  map_smul' c x := by
    ext z
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj,
      LinearMap.coe_mk, AddHom.coe_mk]
    ring

/-- The defining formula of the balanced form. -/
@[simp]
theorem balance_apply (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (K : V →ₛₗ[starRingEnd ℂ] V) (x y : V) :
    balance H K x y = H x y + (starRingEnd ℂ) (H (K x) (K y)) := (rfl)

/-- **The balanced form is compatible with the map it was balanced against**: replacing both
arguments by their `K`-images conjugates the value, as soon as `K ∘ K` is a scalar `ε` of modulus
one.  The conjugation of the first argument of `H` turns the two `ε`-factors into `conj ε * ε`, so
no more than `star ε * ε = 1` is used; the real signs `ε = 1` and `ε = -1` -- an involution, or a
quaternionic structure -- are the cases the representation theory needs.  This is the only property
of `balance` that `H` alone does not already have, and the whole point of the construction. -/
theorem balance_map_map {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {K : V →ₛₗ[starRingEnd ℂ] V} {ε : ℂ}
    (hε : star ε * ε = 1) (hK : ∀ x : V, K (K x) = ε • x) (x y : V) :
    balance H K (K x) (K y) = (starRingEnd ℂ) (balance H K x y) := by
  have hεC : (starRingEnd ℂ) ε * ε = 1 := by rwa [starRingEnd_apply]
  have hH : H (ε • x) (ε • y) = H x y := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    linear_combination (H x y) * hεC
  rw [balance_apply, balance_apply, hK x, hK y, hH, map_add, Complex.conj_conj, add_comm]

/-- The balanced form is Hermitian if `H` is. -/
theorem isSymm_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsSymm)
    (K : V →ₛₗ[starRingEnd ℂ] V) : (balance H K).IsSymm where
  eq x y := by
    rw [balance_apply, balance_apply, map_add, Complex.conj_conj, hH.eq x y,
      hH.eq (K y) (K x)]

/-- The balanced form is nonnegative if `H` is: both summands are, the second because conjugation
fixes a nonnegative complex number. -/
theorem isNonneg_balance {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (K : V →ₛₗ[starRingEnd ℂ] V) : (balance H K).IsNonneg where
  nonneg x := by
    rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
    exact add_nonneg (hH.nonneg x) (hH.nonneg (K x))

/-- The balanced form is definite off the origin if `H` is: the first summand is already nonzero
and the second is nonnegative. -/
theorem balance_apply_self_ne_zero {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hH : H.IsNonneg)
    (hdef : ∀ x : V, x ≠ 0 → H x x ≠ 0) (K : V →ₛₗ[starRingEnd ℂ] V) {x : V} (hx : x ≠ 0) :
    balance H K x x ≠ 0 := by
  rw [balance_apply, starRingEnd_apply, (hH.nonneg (K x)).star_eq]
  exact (add_pos_of_pos_of_nonneg
    (lt_of_le_of_ne (hH.nonneg x) (Ne.symm (hdef x hx))) (hH.nonneg (K x))).ne'

end LinearMap
