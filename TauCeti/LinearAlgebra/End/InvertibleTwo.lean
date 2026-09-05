/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Group.Action.Hom
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Real.Basic

/-!
# Doubling is invertible on a real vector space

For a real vector space `N`, multiplication by `2` is a bijection, so the doubling map is a unit
of the endomorphism ring — and it remains one when `N` is regarded only as a `ℤ`-module, where
`2` itself is not invertible. This file records that as an `Invertible (2 : Module.End ℤ N)`
instance, together with the rewrite rule identifying its inverse with the real scalar `(2 : ℝ)⁻¹`.

## Main definitions

* `TauCeti.invertibleTwoModuleEndInt`: for any semiring `S` acting on `N` in which `2` is
  invertible, doubling is invertible on the `ℤ`-endomorphisms of `N`.

## Main results

* `TauCeti.invOf_two_moduleEndInt_apply`: the inverse of doubling is halving by the scalar,
  for whichever `Invertible (2 : Module.End ℤ N)` instance is in scope.
* `TauCeti.instInvertibleTwoModuleEndInt`: the instance for `S = ℝ`, so that doubling is
  invertible on any real vector space viewed as an endomorphism of its underlying `ℤ`-module.
* `TauCeti.half_moduleEndInt_apply_eq_half_smul`: that inverse acts as the scalar `(2 : ℝ)⁻¹`.
  This is the `R = ℤ` counterpart of Mathlib's
  `QuadraticMap.half_moduleEnd_apply_eq_half_smul`, whose `Invertible (2 : R)` hypothesis is
  unavailable for `R = ℤ`; here the halving scalar comes from the module structure instead of
  from the ring.

## The consumer this exists for

Mathlib builds the bilinear map associated with a quadratic map by halving the polar form:
`QuadraticMap.associatedHom` is `⅟(2 : Module.End R N) • QuadraticMap.polarBilin`, with
`QuadraticMap.associated'` the `ℤ`-linear specialisation. Halving needs
`Invertible (2 : Module.End R N)`, and Mathlib's docstring for `associatedHom` names exactly the
case this file supplies:

> Note that this makes the bijection available in more cases than the simpler condition
> `Invertible (2 : R)`, e.g., when `R = ℤ` and `N = ℝ`.

Mathlib provides no instance reaching it: its only route is
`[Invertible (2 : R)] → Invertible (2 : Module.End R M)`, which for `R = ℤ` asks for
`Invertible (2 : ℤ)` and fails. With the instance below, `associated'` and its API —
`associated_apply`, `associated_isSymm`, `associated_flip`, `associated_eq_self_apply` — become
usable on `ℤ`-quadratic maps with values in a real vector space.

## Implementation notes

The construction is stated for a general scalar semiring `S` but is a `def` rather than an
`instance`, because `S` appears nowhere in the conclusion `Invertible (2 : Module.End ℤ N)` and
so could never be inferred by instance search. Instances are registered by applying it to the
scalar rings that are wanted; `ℝ` is the one this repository needs.

-/

public section

namespace TauCeti

variable {N : Type*} [AddCommGroup N]

/-- **Doubling is invertible on the `ℤ`-endomorphisms of a module over a semiring in which `2` is
invertible.** The halving scalar comes from the module structure rather than from `ℤ`. -/
-- A `def`, not an `instance`: `S` occurs nowhere in the conclusion, so instance search could never
-- infer it. Instances are registered for the scalar rings that are wanted, `ℝ` below.
@[instance_reducible]
noncomputable def invertibleTwoModuleEndInt (S : Type*) [Semiring S] [Module S N]
    [Invertible (2 : S)] : Invertible (2 : Module.End ℤ N) :=
  -- Doubling is the image of `2 : S` under `x ↦ x • 1`, which is multiplicative, so
  -- `Invertible.map` transports invertibility along it; only the numerals need reconciling.
  (Invertible.map (MonoidHom.smulOneHom (M := S) (N := Module.End ℤ N)) 2).copy 2 <|
    -- `ofNat_smul_eq_nsmul` is the bridge: the `2 •` that `Module.End`'s numeral produces is an
    -- `nsmul`, and it has to be matched against the `S`-action before the scalars can cancel.
    by ext x; simp [← ofNat_smul_eq_nsmul S]

/-- **The inverse of doubling is halving by the scalar**, for whichever
`Invertible (2 : Module.End ℤ N)` instance is in scope. -/
-- Instance-independent because an inverse in a monoid is unique: `invOf_eq_right_inv` derives
-- `⅟` from the equation, so the proof never unfolds `invertibleTwoModuleEndInt` and the
-- definition needs no `@[expose]`.
theorem invOf_two_moduleEndInt_apply (S : Type*) [Semiring S] [Module S N] [Invertible (2 : S)]
    [Invertible (2 : Module.End ℤ N)] (x : N) :
    ⅟(2 : Module.End ℤ N) x = ⅟(2 : S) • x := by
  rw [invOf_eq_right_inv (b := ⅟(2 : S) • (1 : Module.End ℤ N))
    (by ext y; simp [← ofNat_smul_eq_nsmul S, smul_smul])]
  simp

variable [Module ℝ N]

/-- **Doubling is invertible on a real vector space**, as an endomorphism of its `ℤ`-module
structure. -/
-- Named rather than anonymous: Lean's generated name for the anonymous form carries an underscore
-- (`instInvertibleEndIntOfNat_tauCeti`), which the `defsWithUnderscore` linter rejects.
noncomputable instance instInvertibleTwoModuleEndInt : Invertible (2 : Module.End ℤ N) :=
  invertibleTwoModuleEndInt ℝ

/-- The inverse of doubling acts as the real scalar `(2 : ℝ)⁻¹`. -/
-- Stated with function application rather than `•`, because `simp` normalises a `Module.End`
-- action to application (`Module.End.smul_def`).
@[simp]
theorem half_moduleEndInt_apply_eq_half_smul (x : N) :
    ⅟(2 : Module.End ℤ N) x = (2 : ℝ)⁻¹ • x := by
  rw [invOf_two_moduleEndInt_apply ℝ, invOf_eq_inv]

end TauCeti
