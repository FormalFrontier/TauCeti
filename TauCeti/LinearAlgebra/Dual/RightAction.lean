/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The dual of a right module as a left module

For a right module `N` over a semiring `A` whose right action commutes with a base commutative
semiring `k`, the duality `D = Hom_k(-, k)` turns `N` into a *left* `A`-module: a scalar `a` acts on
a functional `φ` by precomposition with multiplication by `a`, `(a • φ) x = φ (x * a)`.
Precomposition reverses composition, which is exactly what exchanges the two sides.

This file records that action as the ring homomorphism `TauCeti.dualRightAction`.

## Main definitions

* `TauCeti.dualRightAction`: the left action of `A` on the `k`-dual of a right `A`-module, as a ring
  homomorphism into the `k`-linear endomorphisms of the dual.

## Implementation notes

The action is deliberately *not* installed as a `Module A (Module.Dual k N)` instance: the
underlying type of `Module.Dual k N` is a type of linear maps, which already carries the
codomain-scaling `Module` instances of `Mathlib.Algebra.Module.LinearMap.Defs`, and a second
`Module` structure matching every dual would make instance search on those types depend on an
undetermined right-module structure.  A consumer that wants the left module structure on one
particular dual builds it with `Module.compHom`, which pins the right-module structure being
dualized.
-/

public section

namespace TauCeti

universe u v w

variable (k : Type u) (N : Type w) {A : Type v} [CommSemiring k] [Semiring A] [AddCommMonoid N]
  [Module k N] [Module Aᵐᵒᵖ N] [SMulCommClass Aᵐᵒᵖ k N]

/-- The **duality** `D = Hom_k(-, k)` turns a right `A`-module `N` into a left `A`-module: the
scalar `a` sends a functional `φ` to `x ↦ φ (x * a)`.  This records that action as a ring
homomorphism from `A` to the `k`-linear endomorphisms of `Module.Dual k N`.

Precomposition reverses composition, which is exactly what makes a *right* action on `N` into a
*left* action on its dual; the hypothesis `SMulCommClass Aᵐᵒᵖ k N` is what makes multiplication by
`a` a `k`-linear endomorphism of `N` in the first place. -/
def dualRightAction : A →+* Module.End k (Module.Dual k N) where
  toFun a := (Module.toModuleEnd k N (MulOpposite.op a)).dualMap
  map_one' := by ext φ x; simp
  map_mul' a b := by ext φ x; simp [mul_smul]
  map_zero' := by ext φ x; simp
  map_add' a b := by ext φ x; simp [add_smul]

@[simp]
theorem dualRightAction_apply_apply (a : A) (φ : Module.Dual k N) (x : N) :
    dualRightAction k N a φ x = φ (MulOpposite.op a • x) := by
  -- unfolding `dualRightAction` leaves `LinearMap.dualMap` of multiplication by `a`, evaluated by
  -- `LinearMap.dualMap_apply`
  simp [dualRightAction, LinearMap.dualMap_apply]

end TauCeti
