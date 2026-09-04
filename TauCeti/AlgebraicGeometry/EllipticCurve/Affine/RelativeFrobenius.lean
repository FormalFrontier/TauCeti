/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
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
* `WeierstrassCurve.Affine.CoordinateRing.iterateRelativeFrobenius`: its `n`-fold iterate, from
  the coordinate ring of `W.map (iterateFrobenius R p n)` to that of `W`.

## Main results

* `WeierstrassCurve.Affine.expChar_coordinateRing`: a coordinate ring has the same exponential
  characteristic as its base ring, so the absolute Frobenius of the coordinate ring is available.
* `relativeFrobenius_comp_map`: composing relative Frobenius with the base-change map recovers
  absolute Frobenius.
* `relativeFrobenius_map`: the pointwise form of that identity.
* `iterateRelativeFrobenius_comp_map`: the iterated coefficient Frobenius followed by the
  iterated relative Frobenius is the `p ^ n`-power map.

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
    Polynomial.eval₂ ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (W.map (frobenius R p)).polynomial = 0 := by
  have hcomp : ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom).comp
      (mapRingHom (frobenius R p)) =
      (frobenius W.CoordinateRing p).comp (AdjoinRoot.of W.polynomial) := by
    apply RingHom.ext
    intro g
    simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      AlgHom.coe_toRingHom, frobenius_def, expand_map_frobenius, map_pow]
  rw [_root_.WeierstrassCurve.Affine.map_polynomial, Polynomial.eval₂_map, hcomp,
    ← frobenius_def, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/-- **The relative Frobenius on coordinate rings**: the `R`-algebra map out of the coordinate ring
of the Frobenius twist `W⁽ᵖ⁾` that sends its two coordinates to the `p`-th powers of the
coordinates of `W`. -/
noncomputable def relativeFrobenius :
    (W.map (frobenius R p)).CoordinateRing →ₐ[R] W.CoordinateRing :=
  { AdjoinRoot.lift ((AdjoinRoot.of W.polynomial).comp (expand R p).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p) (eval₂_relativeFrobenius_eq_zero p W) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply R R[X] (W.map (frobenius R p)).CoordinateRing,
        IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing]
      simp [AdjoinRoot.algebraMap_eq] }

/-- The relative Frobenius substitutes `X ^ p` into a polynomial in the affine coordinate. -/
@[simp]
theorem relativeFrobenius_of (g : R[X]) :
    relativeFrobenius p W (AdjoinRoot.of (W.map (frobenius R p)).polynomial g) =
      AdjoinRoot.of W.polynomial (expand R p g) :=
  AdjoinRoot.lift_of (eval₂_relativeFrobenius_eq_zero p W)

/-- The relative Frobenius sends the second coordinate of the twist to `y ^ p`. -/
@[simp]
theorem relativeFrobenius_root :
    relativeFrobenius p W (AdjoinRoot.root (W.map (frobenius R p)).polynomial) =
      AdjoinRoot.root W.polynomial ^ p :=
  AdjoinRoot.lift_root (eval₂_relativeFrobenius_eq_zero p W)

/-- **The absolute Frobenius factors through the twist.** Mathlib's base-change map
`W.CoordinateRing →+* (W.map (frobenius R p)).CoordinateRing` is semilinear over the coefficient
Frobenius; composing the relative Frobenius with it recovers the `p`-power map of
`W.CoordinateRing`. -/
theorem relativeFrobenius_comp_map :
    (relativeFrobenius p W).toRingHom.comp
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p)) =
      frobenius W.CoordinateRing p := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · apply Polynomial.ringHom_ext
    · intro r
      -- Unfold composition at `C r`, identify its class with `algebraMap r`, and unfold Frobenius.
      change relativeFrobenius p W
          (map W (frobenius R p) (algebraMap R W.CoordinateRing r)) =
        algebraMap R W.CoordinateRing r ^ p
      rw [map_algebraMap]
      simp [frobenius_def]
    · simp [frobenius_def]
  · simp [frobenius_def]

/-- The pointwise form of `relativeFrobenius_comp_map`. -/
@[simp]
theorem relativeFrobenius_map (z : W.CoordinateRing) :
    relativeFrobenius p W
      (_root_.WeierstrassCurve.Affine.CoordinateRing.map W (frobenius R p) z) = z ^ p := by
  simpa [frobenius_def] using
    congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing ↦ f z)
      (relativeFrobenius_comp_map p W)

/-! ### Iterated relative Frobenius -/

/-- Substituting `X ^ (p ^ n)` into the coefficientwise iterated Frobenius of a polynomial is
its `p ^ n`-th power. -/
private theorem expand_map_iterateFrobenius (n : ℕ) (g : R[X]) :
    expand R (p ^ n) (g.map (iterateFrobenius R p n)) = g ^ p ^ n := by
  rw [← Polynomial.map_expand, Polynomial.map_iterateFrobenius_expand]

/-- Substituting `(x ^ (p ^ n), y ^ (p ^ n))` into the equation of the `n`-th Frobenius twist
gives zero. -/
private theorem eval₂_iterateRelativeFrobenius_eq_zero (n : ℕ) :
    Polynomial.eval₂
        ((AdjoinRoot.of W.polynomial).comp (expand R (p ^ n)).toRingHom)
        (AdjoinRoot.root W.polynomial ^ p ^ n)
        (W.map (iterateFrobenius R p n)).polynomial = 0 := by
  have hcomp : ((AdjoinRoot.of W.polynomial).comp
      (expand R (p ^ n)).toRingHom).comp
        (mapRingHom (iterateFrobenius R p n)) =
      (iterateFrobenius W.CoordinateRing p n).comp (AdjoinRoot.of W.polynomial) := by
    apply RingHom.ext
    intro g
    simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      AlgHom.coe_toRingHom, iterateFrobenius_def, expand_map_iterateFrobenius, map_pow]
  rw [_root_.WeierstrassCurve.Affine.map_polynomial, Polynomial.eval₂_map, hcomp,
    ← iterateFrobenius_def, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

/-- **The iterated relative Frobenius on coordinate rings.** It maps the coordinate ring of the
`n`-th Frobenius twist `W.map (iterateFrobenius R p n)` to `W.CoordinateRing`, sending the two
coordinates to their `p ^ n`-th powers. -/
noncomputable def iterateRelativeFrobenius (n : ℕ) :
    (W.map (iterateFrobenius R p n)).CoordinateRing →ₐ[R] W.CoordinateRing :=
  { AdjoinRoot.lift
      ((AdjoinRoot.of W.polynomial).comp (expand R (p ^ n)).toRingHom)
      (AdjoinRoot.root W.polynomial ^ p ^ n)
      (eval₂_iterateRelativeFrobenius_eq_zero p W n) with
    commutes' := fun c ↦ by
      rw [IsScalarTower.algebraMap_apply R R[X]
          (W.map (iterateFrobenius R p n)).CoordinateRing,
        IsScalarTower.algebraMap_apply R R[X] W.CoordinateRing]
      simp [AdjoinRoot.algebraMap_eq] }

/-- The iterated relative Frobenius substitutes `X ^ (p ^ n)` into a polynomial in the affine
coordinate. -/
@[simp]
theorem iterateRelativeFrobenius_of (n : ℕ) (g : R[X]) :
    iterateRelativeFrobenius p W n
        (AdjoinRoot.of (W.map (iterateFrobenius R p n)).polynomial g) =
      AdjoinRoot.of W.polynomial (expand R (p ^ n) g) :=
  AdjoinRoot.lift_of (eval₂_iterateRelativeFrobenius_eq_zero p W n)

/-- The iterated relative Frobenius sends the second coordinate of the twist to its
`p ^ n`-th power. -/
@[simp]
theorem iterateRelativeFrobenius_root (n : ℕ) :
    iterateRelativeFrobenius p W n
        (AdjoinRoot.root (W.map (iterateFrobenius R p n)).polynomial) =
      AdjoinRoot.root W.polynomial ^ p ^ n :=
  AdjoinRoot.lift_root (eval₂_iterateRelativeFrobenius_eq_zero p W n)

/-- **The iterated absolute Frobenius factors through the `n`-th twist.** Composing the
coefficient map with the iterated relative Frobenius is the `p ^ n`-power map on
`W.CoordinateRing`. -/
theorem iterateRelativeFrobenius_comp_map (n : ℕ) :
    (iterateRelativeFrobenius p W n).toRingHom.comp
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W
          (iterateFrobenius R p n)) =
      iterateFrobenius W.CoordinateRing p n := by
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · apply Polynomial.ringHom_ext
    · intro r
      -- Unfold composition at `C r`, identify its class with `algebraMap r`, and unfold Frobenius.
      change iterateRelativeFrobenius p W n
          (map W (iterateFrobenius R p n) (algebraMap R W.CoordinateRing r)) =
        algebraMap R W.CoordinateRing r ^ p ^ n
      rw [map_algebraMap]
      simp [iterateFrobenius_def]
    · simp [iterateFrobenius_def]
  · simp [iterateFrobenius_def]

/-- Pointwise form of `iterateRelativeFrobenius_comp_map`. -/
@[simp]
theorem iterateRelativeFrobenius_map (n : ℕ) (z : W.CoordinateRing) :
    iterateRelativeFrobenius p W n
        (_root_.WeierstrassCurve.Affine.CoordinateRing.map W
          (iterateFrobenius R p n) z) =
      z ^ p ^ n := by
  simpa [iterateFrobenius_def] using
    congrArg (fun f : W.CoordinateRing →+* W.CoordinateRing ↦ f z)
      (iterateRelativeFrobenius_comp_map p W n)

end CoordinateRing

end WeierstrassCurve.Affine

end
