/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Evaluating the coordinate ring of a Weierstrass curve at a point

The coordinate ring `R[W]` of an affine Weierstrass curve `W` is `AdjoinRoot W.polynomial`, so at a
point `(x, y)` satisfying the Weierstrass equation the evaluation map `Polynomial.evalEval x y`
factors through it, by Mathlib's `AdjoinRoot.evalEval`. The statement below is about the affine
model `WeierstrassCurve.Affine R` itself, not about a global `WeierstrassCurve R`. This file
records the one consequence that factorisation is wanted for: an identity between bivariate
polynomials that holds only in `R[W]` may be evaluated at any point of `W`.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_eq_of_mk_eq`: bivariate polynomials that are equal in the
  coordinate ring evaluate equally at a point of the curve.

Stated over an arbitrary commutative ring; the curve need not be elliptic, and `R` need not be a
domain, since the statement is exactly the factorisation and nothing more.

This supports the Nagell–Lutz route of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item
"The torsion subgroup and Nagell–Lutz", whose division-polynomial identities Mathlib states in the
coordinate ring but which are consumed at points of the curve.
-/

public section

open Polynomial WeierstrassCurve

open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : _root_.WeierstrassCurve.Affine R) {x y : R}

/-- Bivariate polynomials that are equal in the coordinate ring `R[W]` evaluate equally at a
point `(x, y)` of `W`. -/
theorem evalEval_eq_of_mk_eq (h : W.Equation x y) {p q : R[X][Y]}
    (hpq : Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W q) :
    p.evalEval x y = q.evalEval x y := by
  have hev := AdjoinRoot.evalEval_mk (p := W.polynomial) h
  exact hev p ▸ hev q ▸ congrArg _ hpq

end WeierstrassCurve

end TauCeti
