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
factors through it, by Mathlib's `AdjoinRoot.evalEval`. Conversely, every `R`-algebra homomorphism
from `R[W]` to `R` is evaluation at the images of the coordinate functions, and those images
satisfy the equation. These statements concern the affine model `WeierstrassCurve.Affine R`
itself, not a global `WeierstrassCurve R`.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_eq_of_mk_eq`: bivariate polynomials that are equal in the
  coordinate ring evaluate equally at a point of the curve.
* `TauCeti.WeierstrassCurve.ringHom_eq_evalEvalRingHom`: a ring homomorphism on bivariate
  polynomials that fixes constants is evaluation at the images of the variables.
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

/-- A ring homomorphism from bivariate polynomials that fixes the constant coefficients is
evaluation at the images of the two variables. -/
theorem ringHom_eq_evalEvalRingHom (g : R[X][Y] →+* R)
    (hg : ∀ c : R, g (C (C c)) = c) :
    g = evalEvalRingHom (g (C X)) (g Y) := by
  refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
  · ext c
    simp only [RingHom.comp_apply, hg, coe_evalRingHom, eval_C]
  · simp
  · simp

namespace Affine.CoordinateRing

variable {W : _root_.WeierstrassCurve.Affine R}

/-- An algebra homomorphism from the coordinate ring to the base ring is evaluation at the images
of the two coordinate functions. -/
theorem algHom_mk_eq_evalEval (f : W.CoordinateRing →ₐ[R] R) (p : R[X][Y]) :
    f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W p) =
      p.evalEval
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
  have hconstants : ∀ c : R,
      (f.toRingHom.comp (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W)) (C (C c)) = c :=
    fun c ↦ by
    rw [RingHom.comp_apply]
    have hCC : _root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C (C c)) =
        algebraMap R W.CoordinateRing c := by
      rw [IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq]
      simp
    rw [hCC]
    exact f.commutes c
  exact DFunLike.congr_fun
    (ringHom_eq_evalEvalRingHom
      (f.toRingHom.comp (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W)) hconstants) p

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
