/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Coordinates and constructor elimination for affine points

`WeierstrassCurve.Affine.Point` is a two-constructor inductive type: the point at infinity, and an
affine point together with a nonsingularity certificate. Ruling out the first constructor and
naming the data of the second is a step that recurs wherever a point is known to be nonzero.
This file also supplies total coordinate accessors, junk-valued at the point at infinity, so
downstream definitions can read both coordinates without embedding a case split.

The existential form reads best when the point is a compound term such as `n • P`: `obtain` names
the coordinates, the nonsingularity certificate and the identifying equation in one line, with no
separate generalisation to arrange. The accessor form is useful when the coordinates must occur in
a definition, such as evaluation at a translated generic point.

The junk value `0` is harmless: every result that uses coordinates geometrically assumes the point
is nonzero. Nothing here needs a field, ellipticity, or the group law; the two map lemmas need field
hypotheses only because Mathlib's `Point.map` does.

## Main definitions

* `WeierstrassCurve.Affine.Point.xCoord` and
  `WeierstrassCurve.Affine.Point.yCoord`: the two affine coordinates, both `0` at infinity.

## Main results

* `WeierstrassCurve.Affine.Point.exists_eq_some_of_ne_zero`: a nonzero affine point is `.some`,
  in a form that applies to a compound point.
* `WeierstrassCurve.Affine.Point.nonsingular_coords` and
  `WeierstrassCurve.Affine.Point.some_coords`: a nonzero point is `.some` of its accessors.
* `WeierstrassCurve.Affine.Point.eq_of_coords`: nonzero points with equal coordinates are equal.
* `WeierstrassCurve.Affine.Point.xCoord_map` and
  `WeierstrassCurve.Affine.Point.yCoord_map`: the accessors commute with `Point.map`.

The coordinate accessors support `TauCetiRoadmap/EllipticCurves/README.md`, Layer 0.5, whose
translation-action milestone evaluates functions at translates of the generic point.

## Provenance

Not a port: Mathlib carries `Point.xRep`, the projective representative of the `x`-coordinate
map to `ℙ¹`, but that object intentionally identifies `±P` and records no `y`-coordinate.
-/

public section

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [CommRing F] {E : WeierstrassCurve F}

/-- **A nonzero affine point is `.some`.** The case split on `Affine.Point`'s two constructors,
packaged as an existential: one `obtain` yields the coordinates, the nonsingularity certificate,
and the equation identifying the point with `.some` of them — the last being what consumers go on
to rewrite with. -/
theorem exists_eq_some_of_ne_zero {P : Affine.Point E.toAffine} (hP : P ≠ 0) :
    ∃ x y, ∃ hns : E.toAffine.Nonsingular x y, P = .some _ _ hns := by
  rcases P with _ | ⟨_, _, hns⟩
  · exact absurd rfl hP
  · exact ⟨_, _, hns, rfl⟩

open WeierstrassCurve

variable {R : Type*} [CommRing R] {W : _root_.WeierstrassCurve.Affine R}

/-- The `x`-coordinate of a point, taken to be `0` at the point at infinity. -/
def xCoord : W.Point → R
  | 0 => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point, taken to be `0` at the point at infinity. -/
def yCoord : W.Point → R
  | 0 => 0
  | .some _ y _ => y

@[simp]
theorem xCoord_zero : xCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem yCoord_zero : yCoord (0 : W.Point) = 0 := (rfl)

@[simp]
theorem xCoord_some {x y : R} (h : W.Nonsingular x y) : xCoord (.some x y h) = x := (rfl)

@[simp]
theorem yCoord_some {x y : R} (h : W.Nonsingular x y) : yCoord (.some x y h) = y := (rfl)

/-- **The coordinates of a nonzero point are a nonsingular solution of the equation.** -/
theorem nonsingular_coords {P : W.Point} (hP : P ≠ 0) : W.Nonsingular (xCoord P) (yCoord P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

/-- **A nonzero point is `Point.some` of its two coordinates.** -/
theorem some_coords {P : W.Point} (hP : P ≠ 0) :
    _root_.WeierstrassCurve.Affine.Point.some (xCoord P) (yCoord P)
      (nonsingular_coords hP) = P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => (rfl)

/-- **Two nonzero points with the same two affine coordinates are equal.** -/
theorem eq_of_coords {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xCoord P = xCoord Q) (hy : yCoord P = yCoord Q) : P = Q := by
  rw [← some_coords hP, ← some_coords hQ]
  simp only [hx, hy]

@[simp]
theorem xCoord_neg (P : W.Point) : xCoord (-P) = xCoord P := by
  cases P <;> (rfl)

/-- **The `y`-coordinate of the negation of a nonzero point.** -/
@[simp]
theorem yCoord_neg {P : W.Point} (hP : P ≠ 0) :
    yCoord (-P) = W.negY (xCoord P) (yCoord P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [Algebra R S] [Algebra R F]
  [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [DecidableEq F] [DecidableEq K]

/-- **The `x`-coordinate commutes with `Point.map`.** The point at infinity needs no exception:
both sides are `0` there. -/
@[simp]
theorem xCoord_map (f : F →ₐ[S] K) (P : (W⁄F).toAffine.Point) :
    xCoord (Point.map f P) = f (xCoord P) := by
  cases P with
  | zero => exact f.toRingHom.map_zero.symm
  | some x y h => (rfl)

/-- **The `y`-coordinate commutes with `Point.map`.** -/
@[simp]
theorem yCoord_map (f : F →ₐ[S] K) (P : (W⁄F).toAffine.Point) :
    yCoord (Point.map f P) = f (yCoord P) := by
  cases P with
  | zero => exact f.toRingHom.map_zero.symm
  | some x y h => (rfl)

end WeierstrassCurve.Affine.Point
