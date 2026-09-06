/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
public import Mathlib.FieldTheory.Separable
-- Proof-only: `polynomialY_ne_zero`, and the intermediate-field separability lemmas.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Derivative
import Mathlib.FieldTheory.SeparableDegree

/-!
# The function field of a Weierstrass curve is a separable extension

The Weierstrass polynomial, read over a fraction field `L` of `F[X]`, is the minimal polynomial
of the generic `y`-coordinate, and on an elliptic curve it is separable. Since `y` generates,
`F(W)` is a separable extension of `L`.

## Main results

* `WeierstrassCurve.Affine.isSeparable_genericY_iff`: `y` is separable over `L` exactly when the
  `Y`-partial `W_Y` is a nonzero polynomial.
* `WeierstrassCurve.Affine.isSeparable_functionField_iff`: the same for the whole extension, `y`
  being a generator.
* `WeierstrassCurve.Affine.isSeparable_functionField`: the instance for an elliptic curve.

`L` is an arbitrary fraction field of `F[X]`, so `RatFunc F` and `FractionRing F[X]` are both
covered rather than one being privileged; that is the generality of `finrank_functionField`, which
the degree computation uses.

Separability is *equivalent* to the condition the argument needs — that the `Y`-partial
`W_Y = 2y + a₁x + a₃` is a nonzero polynomial — because that partial is the derivative of the
minimal polynomial. In characteristic two its leading term vanishes, so this is not automatic;
`Δ ≠ 0` implies it (`polynomialY_ne_zero`), and an elliptic curve is the special case of that.

## Provenance

`isSeparable_functionField` is `functionField_isSeparable` of
`projects/HasseWeil/HasseWeil/Ramification.lean` in
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) at revision `513e83879e2f`, Apache-2.0, there
stated for `L = FractionRing F[X]`.
-/

open Polynomial

public section

namespace WeierstrassCurve.Affine

section Field

variable {F : Type*} [CommRing F] [IsDomain F] (W : _root_.WeierstrassCurve.Affine F)
  (L : Type*) [Field L] [Algebra F[X] L] [IsFractionRing F[X] L]
  [Algebra L W.FunctionField] [IsScalarTower F[X] L W.FunctionField]

/-- **The generic `y`-coordinate is separable over `L` exactly when `W_Y` is nonzero.** The
minimal polynomial is the Weierstrass polynomial, so its derivative is `W_Y`. -/
theorem isSeparable_genericY_iff : IsSeparable L (genericY W) ↔ W.polynomialY ≠ 0 := by
  have hirr : Irreducible (minpoly L (genericY W)) := minpoly.irreducible (isIntegral_genericY W L)
  rw [IsSeparable, Polynomial.separable_iff_derivative_ne_zero hirr, minpoly_genericY W L,
    derivative_map, derivative_polynomial, Ne, Ne,
    Polynomial.map_eq_zero_iff (IsFractionRing.injective F[X] L)]

/-- **The function field is a separable extension of `L` exactly when `W_Y` is nonzero.** The
generic `y`-coordinate generates, so the extension is separable exactly when it is. -/
theorem isSeparable_functionField_iff :
    Algebra.IsSeparable L W.FunctionField ↔ W.polynomialY ≠ 0 := by
  refine ⟨fun _ => (isSeparable_genericY_iff W L).1 (Algebra.IsSeparable.isSeparable L _),
    fun hY => ?_⟩
  exact (IntermediateField.isSeparable_top L W.FunctionField).1 <| adjoin_genericY_eq_top W L ▸
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable L W.FunctionField).2
      ((isSeparable_genericY_iff W L).2 hY)

/-- **The function field of an elliptic curve is a separable extension of `L`.** -/
instance isSeparable_functionField [W.IsElliptic] : Algebra.IsSeparable L W.FunctionField :=
  (isSeparable_functionField_iff W L).2 (polynomialY_ne_zero W.isUnit_Δ.ne_zero)

end Field

end WeierstrassCurve.Affine
