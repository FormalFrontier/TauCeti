/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Relative Frobenius on affine coordinate rings

For a Weierstrass curve `W` over a commutative ring of exponential characteristic `p`, this file
constructs the relative Frobenius map from the coordinate ring of the Frobenius twist
`W.map (frobenius R p)` to `W.CoordinateRing`. It sends the two coordinates to their `p`-th
powers and factors the absolute Frobenius through Mathlib's base-change map.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.relativeFrobenius`: the relative Frobenius on coordinate
  rings.

## Main results

* `WeierstrassCurve.Affine.expChar_coordinateRing`: a coordinate ring has the same exponential
  characteristic as its base ring, so the absolute Frobenius of the coordinate ring is available.
* `relativeFrobenius_comp_map`: composing relative Frobenius with the base-change map recovers
  absolute Frobenius.
* `relativeFrobenius_map`: the pointwise form of that identity.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, the relative Frobenius milestone. This is
the coordinate-ring construction underlying the function-field pullback and isogeny.

## Provenance

Not a port. The pinned sources build only the absolute finite-field Frobenius; the relative
Frobenius over an arbitrary commutative base appears in none of them. The exponential-characteristic
instance is the direct transport along Mathlib's injective coordinate-ring algebra map.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p]
  (W : _root_.WeierstrassCurve.Affine R)

/-- The coordinate ring of a Weierstrass curve has the same exponential characteristic as its
base ring. -/
instance expChar_coordinateRing : ExpChar W.CoordinateRing p :=
  ExpChar.of_injective_algebraMap' R p

namespace CoordinateRing

/-- Substituting `X ^ p` into the coefficientwise `p`-th power of a polynomial is its `p`-th
power: the freshman's dream, in the form `Polynomial.expand` consumes. -/
private theorem expand_map_frobenius (g : R[X]) : expand R p (g.map (frobenius R p)) = g ^ p := by
  rw [← Polynomial.map_expand, Polynomial.map_frobenius_expand]

/-- Substituting `(xᵖ, yᵖ)` into the Weierstrass polynomial of the twist gives zero: it is the
`p`-th power of the Weierstrass polynomial of `W`, evaluated at `(x, y)`. -/
private theorem eval₂_relativeFrobenius_eq_zero :
    Polynomial.eval₂
        ((AdjoinRoot.ofAlgHom R W.polynomial).comp (expand R p) : R[X] →+* W.CoordinateRing)
      (AdjoinRoot.root W.polynomial ^ p) (W.map (frobenius R p)).polynomial = 0 := by
  have hcomp : ((AdjoinRoot.ofAlgHom R W.polynomial).comp (expand R p) :
        R[X] →+* W.CoordinateRing).comp (mapRingHom (frobenius R p)) =
      (frobenius W.CoordinateRing p).comp (AdjoinRoot.of W.polynomial) := by
    apply RingHom.ext
    intro g
    simp only [AlgHom.comp_toRingHom, AdjoinRoot.toRingHom_ofAlgHom, RingHom.comp_apply,
      Polynomial.coe_mapRingHom, AlgHom.coe_toRingHom, frobenius_def, expand_map_frobenius,
      map_pow]
  rw [_root_.WeierstrassCurve.Affine.map_polynomial, Polynomial.eval₂_map, hcomp,
    ← frobenius_def, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/-- **The relative Frobenius on coordinate rings**: the `R`-algebra map out of the coordinate ring
of the Frobenius twist `W⁽ᵖ⁾` that sends its two coordinates to the `p`-th powers of the
coordinates of `W`. -/
noncomputable def relativeFrobenius :
    (W.map (frobenius R p)).CoordinateRing →ₐ[R] W.CoordinateRing :=
  AdjoinRoot.liftAlgHom _ ((AdjoinRoot.ofAlgHom R W.polynomial).comp (expand R p))
    (AdjoinRoot.root W.polynomial ^ p) (eval₂_relativeFrobenius_eq_zero p W)

/-- The relative Frobenius substitutes `X ^ p` into a polynomial in the affine coordinate. -/
@[simp]
theorem relativeFrobenius_of (g : R[X]) :
    relativeFrobenius p W (AdjoinRoot.of (W.map (frobenius R p)).polynomial g) =
      AdjoinRoot.of W.polynomial (expand R p g) :=
  AdjoinRoot.liftAlgHom_of _ _ _ (eval₂_relativeFrobenius_eq_zero p W) g

/-- The relative Frobenius sends the second coordinate of the twist to `y ^ p`. -/
@[simp]
theorem relativeFrobenius_root :
    relativeFrobenius p W (AdjoinRoot.root (W.map (frobenius R p)).polynomial) =
      AdjoinRoot.root W.polynomial ^ p :=
  AdjoinRoot.liftAlgHom_root _ _ _ (eval₂_relativeFrobenius_eq_zero p W)

/-- Mathlib's base-change map on a coordinate ring is `AdjoinRoot.map` along the coefficientwise
map of bivariate polynomials, so `AdjoinRoot.map_of` and `AdjoinRoot.map_root` describe it on the
two coordinates. -/
private theorem map_eq_adjoinRootMap {S : Type*} [CommRing S] (f : R →+* S) :
    _root_.WeierstrassCurve.Affine.CoordinateRing.map W f =
      AdjoinRoot.map (mapRingHom f) W.polynomial (W.map f).polynomial
        (dvd_of_eq (_root_.WeierstrassCurve.Affine.map_polynomial W f)) := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun g ↦ ?_) ?_
  · rw [RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.map_of]
    simp only [← AdjoinRoot.mk_C, _root_.WeierstrassCurve.Affine.CoordinateRing.map_mk,
      Polynomial.map_C]
  · rw [AdjoinRoot.map_root]
    simp only [← AdjoinRoot.mk_X, _root_.WeierstrassCurve.Affine.CoordinateRing.map_mk,
      Polynomial.map_X]

/-- **The absolute Frobenius factors through the twist.** Mathlib's base-change map
`W.CoordinateRing →+* (W.map (frobenius R p)).CoordinateRing` is semilinear over the coefficient
Frobenius; composing the relative Frobenius with it recovers the `p`-power map of
`W.CoordinateRing`. -/
theorem relativeFrobenius_comp_map :
    (relativeFrobenius p W).toRingHom.comp
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p)) =
      frobenius W.CoordinateRing p := by
  rw [map_eq_adjoinRootMap]
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · apply RingHom.ext
    intro g
    simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, AdjoinRoot.map_of,
      Polynomial.coe_mapRingHom, AlgHom.coe_toRingHom, frobenius_def, relativeFrobenius_of,
      expand_map_frobenius, map_pow]
  · simp [frobenius_def]

/-- The pointwise form of `relativeFrobenius_comp_map`. -/
@[simp]
theorem relativeFrobenius_map (z : W.CoordinateRing) :
    relativeFrobenius p W
      (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p) z) = z ^ p := by
  simpa [frobenius_def] using
    congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing ↦ f z)
      (relativeFrobenius_comp_map p W)

end CoordinateRing

end WeierstrassCurve.Affine

end
