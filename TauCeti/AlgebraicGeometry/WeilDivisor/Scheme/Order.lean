/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Orders of rational functions at codimension-one points

For a locally Noetherian integral scheme `X`, Mathlib defines the order of vanishing
`Scheme.ord f x : ℤ` of a rational function at a point. This file packages its restriction to
nonzero rational functions at a codimension-one point as an additive homomorphism

`SchemeWeilDivisor.orderAt x : Additive X.functionFieldˣ →+ ℤ`.

This is the local algebraic input for the scheme-theoretic principal-divisor map. Constructing
that map also requires the separate global theorem that a nonzero rational function has nonzero
order at only finitely many codimension-one points; no finiteness assumption is hidden here.

The construction advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, the
"principal divisors" part of "Divisors on a curve". It reuses Mathlib's
`AlgebraicGeometry.Scheme.ord` and `ord_mul`; no external formalization is vendored.
-/

public section

open AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

noncomputable section

/-- The order of a nonzero rational function at a codimension-one point, as an additive
homomorphism from the additive form of the unit group of the function field. -/
noncomputable def orderAt (x : CodimensionOnePoint X) :
    Additive (X.functionFieldˣ) →+ ℤ where
  toFun f := X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x
  map_zero' := by
    have h := X.ord_mul (x := x.1)
      (Units.ne_zero (1 : X.functionFieldˣ)) (Units.ne_zero (1 : X.functionFieldˣ))
    have h' : X.ord (1 : X.functionField) x =
        X.ord (1 : X.functionField) x + X.ord (1 : X.functionField) x := by
      simpa only [Units.val_one, one_mul] using h
    have hz : X.ord (1 : X.functionField) x = 0 := by
      apply add_left_cancel (a := X.ord (1 : X.functionField) x)
      simpa only [add_zero] using h'.symm
    simpa only [toMul_zero, Units.val_one] using hz
  map_add' f g := by
    simp only [toMul_add]
    exact X.ord_mul (x := x.1)
      (Units.ne_zero (Additive.toMul f)) (Units.ne_zero (Additive.toMul g))

/-- Evaluating `orderAt` gives Mathlib's integer-valued order of vanishing. -/
@[simp]
lemma orderAt_apply (x : CodimensionOnePoint X) (f : Additive X.functionFieldˣ) :
    orderAt x f = X.ord ((Additive.toMul f : X.functionFieldˣ) : X.functionField) x :=
  (rfl)

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
