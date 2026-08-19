/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Relative Frobenius on affine coordinate rings

For a Weierstrass curve `W` over a commutative ring of exponential characteristic `p`, this file
constructs the relative Frobenius map from the coordinate ring of the Frobenius twist
`W.map (frobenius R p)` to `W.CoordinateRing`. It sends the two coordinates to their `p`-th
powers and factors the absolute Frobenius through Mathlib's base-change map.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.relativeFrobeniusCoordinateRingHom`: the
  relative Frobenius on coordinate rings.

## Main results

* `relativeFrobeniusCoordinateRingHom_comp_coordinateRingMap`: composing relative Frobenius with
  the base-change map recovers absolute Frobenius.
* `relativeFrobeniusCoordinateRingHom_coordinateRingMap`: the pointwise form of that identity.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the relative Frobenius milestone. This is
the coordinate-ring construction underlying the function-field pullback and isogeny.

## Provenance

Not a port. The pinned sources build only the absolute finite-field Frobenius; the relative
Frobenius over an arbitrary commutative base appears in none of them.
-/

public section

open Polynomial

namespace TauCeti.WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
  (W : _root_.WeierstrassCurve.Affine R)

/-- Substituting `(xᵖ, yᵖ)` into the Weierstrass polynomial of the twist gives zero: it is the
`p`-th power of the Weierstrass polynomial of `W`, evaluated at `(x, y)`. -/
private theorem eval₂_relativeFrobenius_eq_zero :
    Polynomial.eval₂ ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (W.map (frobenius R p)).polynomial = 0 := by
  have hcomp : ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom).comp
      (mapRingHom (frobenius R p)) =
      (frobenius W.CoordinateRing p).comp (AdjoinRoot.of W.polynomial) := by
    apply RingHom.ext
    intro g
    simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, Polynomial.coe_mapRingHom]
    -- Expose the underlying functions of the `toRingHom` and `frobenius` wrappers.
    change AdjoinRoot.of W.polynomial (expand R p (map (frobenius R p) g)) =
      (AdjoinRoot.of W.polynomial g) ^ p
    rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand, map_pow]
  rw [_root_.WeierstrassCurve.Affine.map_polynomial, Polynomial.eval₂_map, hcomp,
    ← frobenius_def, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/-- **The relative Frobenius on coordinate rings**: the `R`-algebra map out of the coordinate ring
of the Frobenius twist `W⁽ᵖ⁾` that sends its two coordinates to the `p`-th powers of the
coordinates of `W`. -/
noncomputable def relativeFrobeniusCoordinateRingHom :
    (W.map (frobenius R p)).CoordinateRing →ₐ[R] W.CoordinateRing :=
  { AdjoinRoot.lift ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (eval₂_relativeFrobenius_eq_zero p W) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply R R[X] (W.map (frobenius R p)).CoordinateRing,
        IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing]
      simp [AdjoinRoot.algebraMap_eq] }

/-- The relative Frobenius substitutes `X ^ p` into a polynomial in the affine coordinate. -/
@[simp]
theorem relativeFrobeniusCoordinateRingHom_of (g : R[X]) :
    relativeFrobeniusCoordinateRingHom p W
        (AdjoinRoot.of (W.map (frobenius R p)).polynomial g) =
      AdjoinRoot.of W.polynomial (expand R p g) :=
  AdjoinRoot.lift_of (eval₂_relativeFrobenius_eq_zero p W)

/-- The relative Frobenius sends the second coordinate of the twist to `y ^ p`. -/
@[simp]
theorem relativeFrobeniusCoordinateRingHom_root :
    relativeFrobeniusCoordinateRingHom p W
        (AdjoinRoot.root (W.map (frobenius R p)).polynomial) =
      AdjoinRoot.root W.polynomial ^ p :=
  AdjoinRoot.lift_root (eval₂_relativeFrobenius_eq_zero p W)

/-- The base-change map on a coordinate ring sends a polynomial in the affine coordinate to the
coefficientwise image of that polynomial. -/
private theorem map_of (g : R[X]) :
    _root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p)
        (AdjoinRoot.of W.polynomial g) =
      AdjoinRoot.of (W.map (frobenius R p)).polynomial (g.map (frobenius R p)) := by
  rw [← AdjoinRoot.mk_C, _root_.WeierstrassCurve.Affine.CoordinateRing.map_mk,
    Polynomial.map_C, Polynomial.coe_mapRingHom, AdjoinRoot.mk_C]

/-- The base-change map on a coordinate ring sends the second coordinate to the second
coordinate. -/
private theorem map_root :
    _root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p)
        (AdjoinRoot.root W.polynomial) =
      AdjoinRoot.root (W.map (frobenius R p)).polynomial := by
  rw [← AdjoinRoot.mk_X, _root_.WeierstrassCurve.Affine.CoordinateRing.map_mk,
    Polynomial.map_X, AdjoinRoot.mk_X]

/-- **The absolute Frobenius factors through the twist.** Mathlib's base-change map
`W.CoordinateRing →+* (W.map (frobenius R p)).CoordinateRing` is semilinear over the coefficient
Frobenius; composing the relative Frobenius with it recovers the `p`-power map of
`W.CoordinateRing`. -/
theorem relativeFrobeniusCoordinateRingHom_comp_coordinateRingMap :
    (relativeFrobeniusCoordinateRingHom p W).toRingHom.comp
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p)) =
      frobenius W.CoordinateRing p := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · apply RingHom.ext
    intro g
    simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, map_of]
    -- Expose the underlying functions of the `toRingHom` and `frobenius` wrappers.
    change relativeFrobeniusCoordinateRingHom p W
        (AdjoinRoot.of (W.map (frobenius R p)).polynomial (map (frobenius R p) g)) =
      (AdjoinRoot.of W.polynomial g) ^ p
    rw [relativeFrobeniusCoordinateRingHom_of, ← Polynomial.map_expand,
      Polynomial.map_frobenius_expand, map_pow]
  · simp [map_root, frobenius_def]

/-- The pointwise form of `relativeFrobeniusCoordinateRingHom_comp_coordinateRingMap`. -/
@[simp]
theorem relativeFrobeniusCoordinateRingHom_coordinateRingMap (z : W.CoordinateRing) :
    relativeFrobeniusCoordinateRingHom p W
      (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p) z) = z ^ p := by
  simpa [frobenius_def] using
    congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing ↦ f z)
      (relativeFrobeniusCoordinateRingHom_comp_coordinateRingMap p W)

end TauCeti.WeierstrassCurve.Affine.CoordinateRing

end
