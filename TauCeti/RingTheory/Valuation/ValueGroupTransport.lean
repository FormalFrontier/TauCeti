/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Transporting the value group along an equivalence of valuations

Mathlib's `Valuation.IsEquiv.orderMonoidIso` is an isomorphism of the value monoids *with
zero*, `ValueGroup₀ (.ofClass v) ≃*o ValueGroup₀ (.ofClass w)`. Consumers that work with the
value **group** — for instance any convex subgroup of it — need the corresponding
isomorphism of groups, which this file supplies.

Since `ValueGroup₀ f = WithZero ↥(valueGroup f)`, it is exactly the inverse of Mathlib's
`OrderMonoidIso.withZero`, the equivalence between order isomorphisms of two groups and
order isomorphisms of those groups with a zero adjoined.

## Main definitions

* `Valuation.IsEquiv.valueGroupOrderIso` : The induced order isomorphism of value groups.

## Main results

* `Valuation.IsEquiv.valueGroupOrderIso_coe` : it agrees with `orderMonoidIso` under the
  coercion into the value monoid with zero.
* `Valuation.IsEquiv.valueGroupOrderIso_symm`,
  `Valuation.IsEquiv.valueGroupOrderIso_eq_refl` and
  `Valuation.IsEquiv.valueGroupOrderIso_trans` : the transport is functorial, mirroring
  Mathlib's `orderMonoidIso_symm`, `orderMonoidIso_eq_refl` and `orderMonoidIso_trans`.

-/

public section

namespace Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-- The order isomorphism of **value groups** induced by an equivalence of valuations.
Mathlib's `IsEquiv.orderMonoidIso` is an isomorphism of the value monoids *with zero*, and
`ValueGroup₀ f = WithZero ↥(valueGroup f)`, so this is exactly the inverse of Mathlib's
`OrderMonoidIso.withZero`, which identifies order isomorphisms of two groups with those of
the groups with zero adjoined. -/
noncomputable def IsEquiv.valueGroupOrderIso {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) :
    valueGroup (.ofClass v) ≃*o valueGroup (.ofClass w) :=
  OrderMonoidIso.withZero.symm h.orderMonoidIso

/-- The induced value-group isomorphism agrees with `orderMonoidIso` under the coercion. -/
@[simp]
theorem IsEquiv.valueGroupOrderIso_coe {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (γ : valueGroup (.ofClass v)) :
    ((h.valueGroupOrderIso γ : valueGroup (.ofClass w)) : ValueGroup₀ (.ofClass w))
      = h.orderMonoidIso (γ : ValueGroup₀ (.ofClass v)) :=
  (rfl)

/-- Transport along the inverse equivalence is the inverse transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso_symm`. -/
theorem IsEquiv.valueGroupOrderIso_symm {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.valueGroupOrderIso.symm = h'.valueGroupOrderIso :=
  (rfl)

/-- Transport along a valuation's equivalence with itself is the identity. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso_eq_refl`. -/
@[simp]
theorem IsEquiv.valueGroupOrderIso_eq_refl {v : Valuation A Γ₀}
    (h : v.IsEquiv v) : h.valueGroupOrderIso = .refl _ := by
  ext γ
  simp [Valuation.IsEquiv.valueGroupOrderIso]

/-- `OrderMonoidIso.withZero` is compatible with composition. This is the general fact behind
`Valuation.IsEquiv.valueGroupOrderIso_trans`; it mentions no valuations. -/
private theorem withZero_symm_trans {G H K : Type*} [CommGroup G] [PartialOrder G]
    [CommGroup H] [PartialOrder H] [CommGroup K] [PartialOrder K]
    (A : WithZero G ≃*o WithZero H) (B : WithZero H ≃*o WithZero K) :
    (OrderMonoidIso.withZero.symm A).trans (OrderMonoidIso.withZero.symm B)
      = OrderMonoidIso.withZero.symm (A.trans B) := by
  ext x
  simp [OrderMonoidIso.withZero]

/-- Transport along a composite equivalence is the composite transport. Mirrors Mathlib's
`Valuation.IsEquiv.orderMonoidIso_trans`. -/
@[simp]
theorem IsEquiv.valueGroupOrderIso_trans {Γ₀'' : Type*}
    [LinearOrderedCommGroupWithZero Γ₀''] {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    {u : Valuation A Γ₀''} (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.valueGroupOrderIso.trans h'.valueGroupOrderIso = (h.trans h').valueGroupOrderIso := by
  simp only [Valuation.IsEquiv.valueGroupOrderIso]
  rw [withZero_symm_trans, Valuation.IsEquiv.orderMonoidIso_trans]

end Valuation
