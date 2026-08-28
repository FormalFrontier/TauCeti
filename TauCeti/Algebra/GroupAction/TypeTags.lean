/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# A distributive action on the additive type tag

`Mathlib/Algebra/Group/Action/TypeTags.lean` transports an action along the type tags on the
*acting* monoid: `Additive.addAction` turns a `MulAction α β` into an `AddAction (Additive α) β`.
This file is the missing counterpart on the side that is acted **on**: a monoid `M` acting on a
monoid `A` by monoid endomorphisms acts distributively on `Additive A`, because `g • 1 = 1` and
`g • (a * b) = g • a * g • b` are literally `g • 0 = 0` and `g • (x + y) = g • x + g • y` read in
additive notation.

Mathlib records the same transport only as a representation,
`Representation.ofMulDistribMulAction : Representation ℤ M (Additive G)` for a commutative `G`,
which is not usable where a bare `DistribMulAction M (Additive A)` instance is what typeclass
search must find. Multiplicative coefficient modules — the units of a field, the roots of unity —
reach the additive world of cohomology through exactly this instance.
-/

public section

namespace TauCeti

variable {M A : Type*} [Monoid M] [Monoid A] [MulDistribMulAction M A]

/-- A monoid acting on a monoid by monoid endomorphisms acts distributively on the additive type
tag: `smul_one` becomes `smul_zero` and `smul_mul'` becomes `smul_add`. -/
instance Additive.distribMulAction : DistribMulAction M (Additive A) where
  smul g x := Additive.ofMul (g • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul M x.toMul)
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h x.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g x.toMul y.toMul)

@[simp]
theorem Additive.ofMul_smul (g : M) (a : A) :
    g • Additive.ofMul a = Additive.ofMul (g • a) :=
  rfl

@[simp]
theorem Additive.toMul_smul (g : M) (x : Additive A) : (g • x).toMul = g • x.toMul :=
  rfl

end TauCeti
