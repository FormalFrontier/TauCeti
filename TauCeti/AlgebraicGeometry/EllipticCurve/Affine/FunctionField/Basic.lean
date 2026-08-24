/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# The function field of a Weierstrass curve is an algebraic function field of one variable

`TauCeti.IsFunctionField k F` says that `F` is finite over `k⟮x⟯` for some `x` transcendental over
`k`. It is the hypothesis carried by this repository's general theory of places, degrees,
divisors and weak approximation, in `TauCeti/FieldTheory/FunctionField/`. This file discharges it
for `W.FunctionField`, the fraction field of the coordinate ring of an affine Weierstrass curve
`W` over a field `F`, so that the general theory applies to `W` with no further hypothesis.

The rational parameter is the affine coordinate `x`: the function field is a quadratic extension
of the rational function field `F(x)`, which is `finrank_functionField`, and the intrinsic
predicate agrees with Mathlib's `FunctionField` once such an embedding of `F(x)` is chosen. So
this is the elliptic instance of a general bridge, not a new computation.

Nothing here assumes ellipticity or nonsingularity: a Weierstrass equation is irreducible over
any field, which is all that makes the fraction field a field of transcendence degree one.

## Main results

* `WeierstrassCurve.Affine.isFunctionField`: `W.FunctionField` is an algebraic function field of
  one variable over `F`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0**, whose places-and-divisors interface is
"the places of `W.FunctionField` over `K` — the valuation-theoretic points of the regular proper
curve (Stichtenoth I.1)". Stichtenoth's theory is developed in this repository against an
abstract `TauCeti.IsFunctionField`, and this is the instance of that hypothesis which the
elliptic layers supply.

## Provenance

Not ported. The statement is the abstract predicate of
`TauCeti/FieldTheory/FunctionField/Basic.lean` applied to Mathlib's Weierstrass function field,
through the degree computation already in `Affine/FunctionField/Finrank.lean`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 1.1.1.
-/

public section

namespace WeierstrassCurve.Affine

open scoped RatFunc

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

/-- **The function field of a Weierstrass curve is an algebraic function field of one variable**
over the base field, the affine coordinate `x` being a rational parameter: `F(W) / F(x)` is
finite, of degree two.

This is what makes the general theory of places, divisors and degrees applicable to a Weierstrass
curve. -/
theorem isFunctionField : TauCeti.IsFunctionField F W.FunctionField :=
  TauCeti.isFunctionField_iff_functionField.2
    (inferInstanceAs (FiniteDimensional (RatFunc F) W.FunctionField))

end WeierstrassCurve.Affine

end
