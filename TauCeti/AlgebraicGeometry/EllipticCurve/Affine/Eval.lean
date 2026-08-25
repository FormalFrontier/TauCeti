/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Evaluating the coordinate ring of a Weierstrass curve at a point

The coordinate ring `R[W]` of an affine Weierstrass curve `W` is `AdjoinRoot W.polynomial`, so at a
point `(x, y)` satisfying the Weierstrass equation the evaluation map `Polynomial.evalEval x y`
factors through it, by Mathlib's `AdjoinRoot.evalEval`. Conversely, every `R`-algebra homomorphism
from `R[W]` to `R` is evaluation at the images of the coordinate functions, and those images
satisfy the equation. These statements concern the affine model `WeierstrassCurve.Affine R`
itself, not a global `WeierstrassCurve R`.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_eq_of_mk_eq`: bivariate polynomials that are equal in the
  coordinate ring evaluate equally at a point of the curve.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.algHom_mk_eq_evalEval`: an algebra homomorphism
  from the coordinate ring is evaluation at the images of the coordinate functions, and
  `TauCeti.WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom` says that those images
  satisfy the Weierstrass equation.

Stated over an arbitrary commutative ring; the curve need not be elliptic, and `R` need not be a
domain, since the statement is exactly the factorisation and nothing more.

This supports the Nagell–Lutz route of `TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, item
"The torsion subgroup and Nagell–Lutz", whose division-polynomial identities Mathlib states in the
coordinate ring but which are consumed at points of the curve. The converse evaluation statements
also support Layer 0's point–place dictionary by recovering an equation solution from a residue
degree-one ideal.
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

namespace Affine.CoordinateRing

variable {W : _root_.WeierstrassCurve.Affine R}

/-- An algebra homomorphism from the coordinate ring to the base ring is evaluation at the images
of the two coordinate functions. -/
theorem algHom_mk_eq_evalEval (f : W.CoordinateRing →ₐ[R] R) (p : R[X][Y]) :
    f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W p) =
      p.evalEval
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
  -- `f` precomposed with the quotient map, as an `R`-algebra map on bivariate polynomials
  let g : R[X][Y] →ₐ[R] R :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars R)
  have hg (q : R[X][Y]) : g q = f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W q) := by
    simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]
  have key : g.toRingHom = evalEvalRingHom (g (C X)) (g Y) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp only [RingHom.comp_apply, coe_evalRingHom, eval_C]
        have hCC : (C (C r) : R[X][Y]) = algebraMap R R[X][Y] r :=
          (congrFun coe_algebraMap_eq_CC r).symm
        rw [hCC]
        exact g.commutes r
      · simp
    · simp
  rw [← hg]
  exact RingHom.congr_fun key p

/-- The images of the coordinate functions under an algebra homomorphism from the coordinate ring
to the base ring satisfy the Weierstrass equation. -/
theorem equation_of_algHom (f : W.CoordinateRing →ₐ[R] R) :
    W.Equation
      (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
      (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
  rw [_root_.WeierstrassCurve.Affine.Equation, ← algHom_mk_eq_evalEval f W.polynomial,
    AdjoinRoot.mk_self, map_zero]

end Affine.CoordinateRing

end WeierstrassCurve

end TauCeti
