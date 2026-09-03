/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Solutions of a Weierstrass equation are its degree-one affine places

For an affine Weierstrass curve `W` over a field whose coordinate ring is a Dedekind domain, the
ideal `⟨X - x, Y - y⟩ = XYIdeal W x (C y)` of a solution `(x, y)` of `W.Equation` is maximal and
nonzero. It is therefore a point of `IsDedekindDomain.HeightOneSpectrum W.CoordinateRing`, which
is Mathlib's type of nonzero primes and carries the adic valuation on the function field.

This file builds that place and identifies which places arise: exactly those of **degree one**, the
degree of a place being the rank of its residue field over the base field. A point has degree one
because the quotient by its ideal is the base field, by Mathlib's `quotientXYIdealEquiv`; the
converse ideal-level classification is in `XYIdealMaximal.lean`. The Dedekind hypothesis enters
only in the packaging, where the places are named.

The degree hypothesis is part of the statement, not a convenience: a place of degree `d > 1` has
a residue field of degree `d` over `F` and is the place of no rational point at all. It is only
over an algebraically closed base that every place has degree one, so that points correspond to
*all* nonzero primes.

When `W` is elliptic, Mathlib's `Affine.equation_iff_nonsingular` identifies the solutions of
`W.Equation` with the affine points in `W.toAffine.Point`, namely the points other than `0`.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace`: the place — the height-one prime of
  the coordinate ring — attached to a point of the curve, built with Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.ofPrime`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.equationEquivDegreeOnePlace`: **the affine
  point–place dictionary** — `pointPlace` as an equivalence between solutions of `W.Equation`
  and the degree-one places.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_asIdeal`: a `@[simp]` lemma
  identifying the ideal underlying `pointPlace` as `XYIdeal W x (C y)`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_eq_iff`: `pointPlace` is injective —
  two points have the same place exactly when they have the same coordinates.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace.finrank_residueField_eq_one`: the
  place of a point has degree one.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.exists_pointPlace_eq`: conversely, every
  degree-one place is the place of a point.

`(pointPlace h).valuation W.FunctionField` is then the associated multiplicative adic valuation on
the function field, taking values in `ℤᵐ⁰` and normalised so that a uniformiser has value
`WithZero.exp (-1)`; the order of vanishing is its negative logarithm. Mathlib's `Valuation` API —
multiplicativity, the ultrametric inequality, vanishing exactly at `0`, and the existence of a
uniformiser — comes with it.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0** (the function field, places, and divisors),
whose §Places asks for the affine places as the maximal ideals of the coordinate ring together with
an API of `ord_v` and uniformisers, and for the point–place dictionary: "for elliptic `W`,
`W.toAffine.Point` is in bijection with the degree-`1` places: `O ↦ infinityPlace`, and an affine
nonsingular `(x₀, y₀) ↦` the maximal ideal `(X − x₀, Y − y₀)`". This is the affine half of that
dictionary at the level of equation solutions; for elliptic `W`, `equation_iff_nonsingular`
identifies its domain with the nonzero affine points. The downstream file
`Affine/FunctionField/PointPlace.lean` packages the valuation at infinity and these affine primes
as one type of normalized places, and `pointEquivDegreeOnePlace` extends this affine equivalence to
the whole point group. The layer seeds no declaration this competes with, and records that the
design is coordinated with D. Angdinata's in-flight upstream `CoordinateRing` work.

## Provenance

The degree-one result corresponds to AINTLIB's `HasseWeil/Curves/ResidueFieldAtSmoothPoint.lean`
(`SmoothPlaneCurve.quotientAlgEquivBase`, `SmoothPlaneCurve.residueFieldsAlgEquiv`,
`CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed`). There it is reached through the
`SmoothPlaneCurve`/`SmoothPoint` wrappers with the residue field built by hand, and the residue
degree additionally assumes an algebraically closed base; here the wrappers are dropped, the
hypothesis is the curve equation, no closure is needed, and the content is Mathlib's
`quotientXYIdealEquiv` rather than a fresh construction.

The place itself is not a port. AINTLIB's `HasseWeil/Curves/Valuation.lean` builds an `ord_P` for
its own
`SmoothPlaneCurve` wrapper with about twenty lemmas — multiplicativity, the ultrametric bound,
inverses, powers, uniformisers. None of that is reproduced: once the point is presented as a
`HeightOneSpectrum`, those are Mathlib's `Valuation.map_mul`, `Valuation.map_add`,
`Valuation.zero_iff`, `Valuation.map_inv`, `Valuation.map_add_of_distinct_val` and
`IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`.

The packaged equivalence corresponds to AINTLIB's `smoothPointEquivHeightOneSpectrum` in
`projects/HasseWeil/HasseWeil/Foundation/Curves/Valuation/SmoothPointPrime.lean`
(`github.com/CBirkbeck/AINTLIB @ 1c1c74664e40`, Apache-2.0; Authors: Chris Birkbeck). That version
uses `SmoothPlaneCurve` and `SmoothPoint` wrappers, assumes a maximal-ideal hypothesis and
`[IsAlgClosed F]`, and reaches all height-one primes. Here the domain is the equation-solution
subtype and the codomain is the degree-one places over an arbitrary field. The preceding
"not a port" statement concerns only the `ord_P` valuation API.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

variable [IsDedekindDomain W.CoordinateRing]

/-- **The place of a solution of a Weierstrass equation**: the ideal `⟨X - x, Y - y⟩` as a nonzero
prime of the coordinate ring, for a solution `(x, y)` of `W.Equation`. The Dedekind hypothesis is an
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
have the same coordinates. -/
@[simp]
theorem pointPlace_eq_iff {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) :
    pointPlace h₁ = pointPlace h₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  -- both directions go through the underlying ideals, `HeightOneSpectrum` being determined by them
  rw [HeightOneSpectrum.ext_iff, pointPlace_asIdeal, pointPlace_asIdeal]
  exact XYIdeal_eq_iff h₁

/-- **The place of a point has degree one.** The degree of a place is the rank of its residue field
over the base, and here that rank is one — which is the sense in which the point–place dictionary
lands in the *degree-one* places. -/
@[simp]
theorem pointPlace.finrank_residueField_eq_one {y : F} (h : W.Equation x y) :
    Module.finrank F (W.CoordinateRing ⧸ (pointPlace h).asIdeal) = 1 := by
  rw [pointPlace_asIdeal]
  rw [(CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **Every degree-one place is the place of a point**, the converse of
`pointPlace.finrank_residueField_eq_one`. -/
theorem exists_pointPlace_eq {v : HeightOneSpectrum W.CoordinateRing}
    (hv : Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1) :
    ∃ (x y : F) (h : W.Equation x y), pointPlace h = v := by
  obtain ⟨x, y, h, hI⟩ := finrank_quotient_eq_one_iff.mp hv
  exact ⟨x, y, h, by rw [HeightOneSpectrum.ext_iff, pointPlace_asIdeal, hI]⟩

variable (W) in
/-- Send a solution of `W.Equation` to its degree-one place. -/
private noncomputable def equationToDegreeOnePlace
    (p : {xy : F × F // W.Equation xy.1 xy.2}) :
    {v : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1} :=
  ⟨pointPlace p.2, pointPlace.finrank_residueField_eq_one p.2⟩

variable (W) in
/-- Sending an equation solution to its degree-one place is bijective. -/
private theorem equationToDegreeOnePlace_bijective :
    Function.Bijective (equationToDegreeOnePlace W) :=
  ⟨fun p q h ↦ Subtype.ext <| Prod.ext_iff.mpr <|
      (pointPlace_eq_iff p.2 q.2).mp (Subtype.ext_iff.mp h),
    fun v ↦ by
      obtain ⟨x, y, h, hv⟩ := exists_pointPlace_eq v.2
      exact ⟨⟨(x, y), h⟩, Subtype.ext hv⟩⟩

variable (W) in
/-- **The affine point–place dictionary**: the solutions of `W.Equation` correspond to the
degree-one places of its coordinate ring, a solution going to the prime `⟨X - x, Y - y⟩`.
For elliptic `W`, these solutions are the nonzero affine points by `equation_iff_nonsingular`.
Injectivity is `pointPlace_eq_iff` and surjectivity is `exists_pointPlace_eq`. -/
noncomputable def equationEquivDegreeOnePlace :
    {xy : F × F // W.Equation xy.1 xy.2} ≃
      {v : HeightOneSpectrum W.CoordinateRing //
        Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1} :=
  Equiv.ofBijective (equationToDegreeOnePlace W) (equationToDegreeOnePlace_bijective W)

/-- The dictionary sends a point to its place. -/
@[simp]
theorem equationEquivDegreeOnePlace_apply_coe (p : {xy : F × F // W.Equation xy.1 xy.2}) :
    (equationEquivDegreeOnePlace W p : HeightOneSpectrum W.CoordinateRing) = pointPlace p.2 := by
  rw [equationEquivDegreeOnePlace, Equiv.ofBijective_apply]
  rfl

/-- Reading the dictionary backwards and then taking the place recovers the original place. -/
@[simp]
theorem pointPlace_equationEquivDegreeOnePlace_symm_apply
    (v : {v : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1}) :
    pointPlace ((equationEquivDegreeOnePlace W).symm v).2 = v.1 := by
  rw [← equationEquivDegreeOnePlace_apply_coe]
  exact congrArg Subtype.val ((equationEquivDegreeOnePlace W).apply_symm_apply v)

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
