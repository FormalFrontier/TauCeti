/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The place of an affine point of an elliptic curve

For an elliptic curve `W` over a field, the coordinate ring is a Dedekind domain and the ideal
`⟨X - x, Y - y⟩ = XYIdeal W x (C y)` of a point `(x, y)` of the curve is maximal and nonzero. It is
therefore a point of `IsDedekindDomain.HeightOneSpectrum W.CoordinateRing`, which is Mathlib's
type of nonzero primes and carries the adic valuation on the function field.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace`: the place — the height-one prime of
  the coordinate ring — attached to a point of the curve, built with Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.ofPrime`.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_asIdeal`: a `@[simp]` lemma
  identifying its underlying ideal as `XYIdeal W x (C y)`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_eq_iff`: `pointPlace` is injective —
  two points have the same place exactly when they have the same coordinates.

`(pointPlace h).valuation W.FunctionField` is then the associated multiplicative adic valuation on
the function field, taking values in `ℤᵐ⁰` and normalised so that a uniformiser has value
`WithZero.exp (-1)`; the order of vanishing is its negative logarithm. Mathlib's `Valuation` API —
multiplicativity, the ultrametric inequality, vanishing exactly at `0`, and the existence of a
uniformiser — comes with it.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors),
whose §Places asks for the affine places as the maximal ideals of the coordinate ring together with
an API of `ord_v` and uniformisers, and for the point–place dictionary. This is the direction that
sends a point to a place. The layer seeds no declaration this competes with, and records that the
design is coordinated with D. Angdinata's in-flight upstream `CoordinateRing` work.

## Provenance

Not a port. AINTLIB's `HasseWeil/Curves/Valuation.lean` builds an `ord_P` for its own
`SmoothPlaneCurve` wrapper with about twenty lemmas — multiplicativity, the ultrametric bound,
inverses, powers, uniformisers. None of that is reproduced: once the point is presented as a
`HeightOneSpectrum`, those are Mathlib's `Valuation.map_mul`, `Valuation.map_add`,
`Valuation.zero_iff`, `Valuation.map_inv`, `Valuation.map_add_of_distinct_val` and
`IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F}
  [IsDedekindDomain W.CoordinateRing] {x : F}

/-- **The place of an affine point of an elliptic curve**: the ideal `⟨X - x, Y - y⟩` as a nonzero
prime of the coordinate ring, for a point `(x, y)` of the curve. The Dedekind hypothesis is an
instance argument; for an elliptic curve it is
`TauCeti.WeierstrassCurve.Affine.isDedekindDomain_coordinateRing`. -/
noncomputable def pointPlace {y : F} (h : W.Equation x y) :
    HeightOneSpectrum W.CoordinateRing :=
  HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime (XYIdeal_ne_bot x (C y)) (XYIdeal_isMaximal_of_equation h).isPrime)

/-- The ideal underlying the place of a point is `⟨X - x, Y - y⟩`. -/
@[simp]
theorem pointPlace_asIdeal {y : F} (h : W.Equation x y) :
    (pointPlace h).asIdeal = CoordinateRing.XYIdeal W x (C y) := by
  simp [pointPlace]

/-- **`pointPlace` is injective**: two points of the curve have the same place exactly when they
have the same coordinates. Whether every place arises from a point is a separate statement, not
proved here. -/
@[simp]
theorem pointPlace_eq_iff {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    pointPlace h₁ = pointPlace h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  -- both directions go through the underlying ideals, `HeightOneSpectrum` being determined by them
  rw [HeightOneSpectrum.ext_iff, pointPlace_asIdeal, pointPlace_asIdeal]
  exact XYIdeal_eq_iff h₁

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
