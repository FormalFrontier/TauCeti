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
from `R[W]` to a commutative `R`-algebra is evaluation at the images of the coordinate functions,
and those images satisfy the equation. Conversely, every solution of the base-changed equation
defines such a homomorphism. These statements concern the affine model `WeierstrassCurve.Affine R`
itself, not a global `WeierstrassCurve R`.

## Main results

* `TauCeti.WeierstrassCurve.evalEval_eq_of_mk_eq`: bivariate polynomials that are equal in the
  coordinate ring evaluate equally at a point of the curve.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.algHom_mk_eq_evalEval`: an algebra homomorphism
  from the coordinate ring is evaluation at the images of the coordinate functions, and
  `TauCeti.WeierstrassCurve.Affine.CoordinateRing.equation_of_algHom` says that those images
  satisfy the Weierstrass equation.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.ofEquation`: the converse construction from a
  solution of the base-changed equation, with computation and extensionality lemmas.

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

variable {A : Type*} [CommRing A] [Algebra R A]
variable {W : _root_.WeierstrassCurve.Affine R}

/-- An algebra homomorphism from the coordinate ring to a commutative `R`-algebra is evaluation at
the images of the two coordinate functions. -/
theorem algHom_mk_eq_evalEval (f : W.CoordinateRing →ₐ[R] A) (p : R[X][Y]) :
    f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
        (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
  -- `f` precomposed with the quotient map, as an `R`-algebra map on bivariate polynomials
  let g : R[X][Y] →ₐ[R] A :=
    f.comp ((AdjoinRoot.mkₐ W.polynomial).restrictScalars R)
  have hg (q : R[X][Y]) : g q = f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W q) := by
    simp only [g, AlgHom.comp_apply, AlgHom.restrictScalars_apply, AdjoinRoot.coe_mkₐ]
  have key : g.toRingHom =
      eval₂RingHom (eval₂RingHom (algebraMap R A) (g (C X))) (g Y) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r
        simp only [RingHom.comp_apply]
        have hCC : (C (C r) : R[X][Y]) = algebraMap R R[X][Y] r :=
          (congrFun coe_algebraMap_eq_CC r).symm
        rw [hCC]
        simpa using g.commutes r
      · simp
    · simp
  rw [← hg, ← eval₂_eval₂RingHom_apply]
  exact RingHom.congr_fun key p

/-- Two algebra homomorphisms out of the coordinate ring are equal when they agree on the two
coordinate functions. -/
theorem algHom_ext_coords {f g : W.CoordinateRing →ₐ[R] A}
    (hX : f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)) =
      g (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
    (hY : f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y) =
      g (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) : f = g :=
  AlgHom.ext fun z ↦ by
    induction z using AdjoinRoot.induction_on with
    | ih p =>
      rw [algHom_mk_eq_evalEval f p, algHom_mk_eq_evalEval g p, hX, hY]

/-- The images of the coordinate functions under an algebra homomorphism from the coordinate ring
to a commutative `R`-algebra satisfy the base-changed Weierstrass equation. -/
theorem equation_of_algHom (f : W.CoordinateRing →ₐ[R] A) :
    (W.map (algebraMap R A)).Equation
      (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W (C X)))
      (f (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
  rw [_root_.WeierstrassCurve.Affine.Equation,
    _root_.WeierstrassCurve.Affine.map_polynomial,
    ← algHom_mk_eq_evalEval f W.polynomial, AdjoinRoot.mk_self, map_zero]

/-- A solution of the base-changed Weierstrass equation defines an algebra homomorphism from the
coordinate ring. -/
noncomputable def ofEquation {x y : A}
    (h : (W.map (algebraMap R A)).Equation x y) : W.CoordinateRing →ₐ[R] A :=
  AdjoinRoot.liftAlgHom W.polynomial (aeval x) y <| by
    have hcoe : ((aeval x : R[X] →ₐ[R] A) : R[X] →+* A) =
        eval₂RingHom (algebraMap R A) x := by
      apply RingHom.ext
      intro p
      simp [Polynomial.aeval_def]
    dsimp only [_root_.WeierstrassCurve.Affine.Equation] at h
    rw [hcoe, eval₂_eval₂RingHom_apply,
      ← _root_.WeierstrassCurve.Affine.map_polynomial]
    exact h

/-- `ofEquation` sends the class of `X` to the chosen `x`-coordinate. -/
@[simp]
theorem ofEquation_of_X {x y : A} (h : (W.map (algebraMap R A)).Equation x y) :
    ofEquation h (AdjoinRoot.of W.polynomial X) = x := by
  rw [ofEquation, AdjoinRoot.liftAlgHom_of, aeval_X]

/-- `ofEquation` sends the class of `Y` to the chosen `y`-coordinate. -/
@[simp]
theorem ofEquation_root {x y : A} (h : (W.map (algebraMap R A)).Equation x y) :
    ofEquation h (AdjoinRoot.root W.polynomial) = y :=
  AdjoinRoot.liftAlgHom_root ..

/-- The value of `ofEquation` on the class of a bivariate polynomial is evaluation at the chosen
point. -/
@[simp]
theorem ofEquation_mk {x y : A} (h : (W.map (algebraMap R A)).Equation x y) (p : R[X][Y]) :
    ofEquation h (_root_.WeierstrassCurve.Affine.CoordinateRing.mk W p) =
      (p.map (mapRingHom (algebraMap R A))).evalEval x y := by
  rw [algHom_mk_eq_evalEval]
  change (p.map (mapRingHom (algebraMap R A))).evalEval
    (ofEquation h (AdjoinRoot.of W.polynomial X))
    (ofEquation h (AdjoinRoot.root W.polynomial)) = _
  rw [ofEquation_of_X, ofEquation_root]

/-- Constructing a homomorphism from the equation satisfied by its coordinates recovers the
original homomorphism. -/
@[simp]
theorem ofEquation_equation_ofAlgHom (f : W.CoordinateRing →ₐ[R] A) :
    ofEquation (equation_of_algHom f) = f :=
  algHom_ext_coords
    (by change ofEquation (equation_of_algHom f) (AdjoinRoot.of W.polynomial X) = _
        rw [ofEquation_of_X])
    (by change ofEquation (equation_of_algHom f) (AdjoinRoot.root W.polynomial) = _
        rw [ofEquation_root])

end Affine.CoordinateRing

end WeierstrassCurve

end TauCeti
