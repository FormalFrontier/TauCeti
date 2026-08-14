/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.XYIdealMaximal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# The affine points of an elliptic curve are its degree-one affine places

For an elliptic curve `W` over a field, the coordinate ring is a Dedekind domain and the ideal
`⟨X - x, Y - y⟩ = XYIdeal W x (C y)` of a point `(x, y)` of the curve is maximal and nonzero. It is
therefore a point of `IsDedekindDomain.HeightOneSpectrum W.CoordinateRing`, which is Mathlib's
type of nonzero primes and carries the adic valuation on the function field.

This file builds that place and identifies which places arise: exactly those of **degree one**, the
degree of a place being the rank of its residue field over the base field. A point has degree one
because the quotient by its ideal is the base field, by Mathlib's `quotientXYIdealEquiv`.
Conversely a proper ideal `I` of `F[W]` whose quotient has rank one is the ideal of a point. The
rank hypothesis makes `algebraMap F (F[W] ⧸ I)` bijective, so composing the quotient map with its
inverse gives a ring homomorphism `ρ : F[W] → F` fixing the constants; being a ring homomorphism
out of `F[X][Y]/⟨W(X, Y)⟩`, it is evaluation at the pair `(ρ x, ρ y)`, which therefore satisfies
the Weierstrass equation. The maximal ideal `⟨X - ρ x, Y - ρ y⟩` is contained in the proper ideal
`I`, hence equal to it.

Neither direction needs ellipticity or a Dedekind hypothesis: both are statements about an ideal
of the coordinate ring. Those hypotheses enter only in the packaging, where the places and the
point group are named.

The degree hypothesis is part of the statement, not a convenience: a place of degree `d > 1` has
a residue field of degree `d` over `F` and is the place of no rational point at all. It is only
over an algebraically closed base that every place has degree one, so that points correspond to
*all* nonzero primes.

## Main definitions

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace`: the place — the height-one prime of
  the coordinate ring — attached to a point of the curve, built with Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.ofPrime`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.equationEquivPointPlace`: **the affine
  point–place dictionary** — `pointPlace` as an equivalence between the points of the curve and
  the degree-one places.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointEquivPointPlace`: the same dictionary read
  on the point group of an elliptic curve, whose extra element — the point at infinity — is the
  `WithZero` adjoined to the degree-one places.

## Main results

* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_asIdeal`: a `@[simp]` lemma
  identifying its underlying ideal as `XYIdeal W x (C y)`.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace_eq_iff`: `pointPlace` is injective —
  two points have the same place exactly when they have the same coordinates.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.finrank_quotient_XYIdeal` and
  `TauCeti.WeierstrassCurve.Affine.CoordinateRing.pointPlace.finrank_residueField_eq_one`:
  the place of a point has degree one.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.exists_equation_and_eq_XYIdeal`: **the
  classification** — a proper ideal whose quotient has rank one over the base field is the ideal
  of a point of the curve.
* `TauCeti.WeierstrassCurve.Affine.CoordinateRing.exists_pointPlace_eq`: consequently every
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
dictionary, in both directions. The place at infinity
(`TauCeti.WeierstrassCurve.Affine.infinityPlace`) is a valuation on the function field rather than
a prime of the coordinate ring, so the two are not yet terms of one type of places, although they
are already known to be distinct places
(`TauCeti.WeierstrassCurve.Affine.infinityPlace_ne_heightOneSpectrum_valuation`). Until Layer 0
fixes that type, the point at infinity is the adjoined element of `pointEquivPointPlace`, and
identifying that element with the place at infinity is what remains. The layer seeds no declaration
this competes with, and records that the design is coordinated with D. Angdinata's in-flight
upstream `CoordinateRing` work.

## Provenance

The degree-one result corresponds to AINTLIB's `HasseWeil/Curves/ResidueFieldAtSmoothPoint.lean`
(`SmoothPlaneCurve.quotientAlgEquivBase`, `SmoothPlaneCurve.residueFieldsAlgEquiv`,
`CurveMap.CoordHom.inertiaDeg_eq_one_of_isAlgClosed`). There it is reached through the
`SmoothPlaneCurve`/`SmoothPoint` wrappers with the residue field built by hand, and the residue
degree additionally assumes an algebraically closed base; here the wrappers are dropped, the
hypothesis is the curve equation, no closure is needed, and the content is Mathlib's
`quotientXYIdealEquiv` rather than a fresh construction.

The classification has a counterpart in the same project, in
`projects/HasseWeil/HasseWeil/Foundation/Curves/Valuation/NormValuation.lean` at
`github.com/CBirkbeck/AINTLIB @ 1c1c74664e40` (Apache-2.0 per that file's header;
Authors: Chris Birkbeck): `exists_coordinates_of_isMaximal_of_surjective`,
`equation_of_coordinates_of_field` and `exists_smoothPoint_of_isMaximal_of_surjective`, packaged
in `Valuation/SmoothPointPrime.lean` as `smoothPointEquivHeightOneSpectrum`. That statement is
about a *maximal* ideal of the coordinate ring of a `SmoothPlaneCurve`, hypothesises surjectivity
of `algebraMap F (F[C] ⧸ M)`, assumes ellipticity throughout, and its packaged bijection is onto
all height-one primes under `[IsAlgClosed F]`. The development below is written directly against
Mathlib's `XYIdeal`: the ideal is only assumed proper, the hypothesis is the residue degree, no
ellipticity is used until the point group is named, and the bijection is with the degree-one
places over an arbitrary field, which is the roadmap's statement and the one that survives without
a closure hypothesis.

The place itself is not a port. AINTLIB's `HasseWeil/Curves/Valuation.lean` builds an `ord_P` for
its own
`SmoothPlaneCurve` wrapper with about twenty lemmas — multiplicativity, the ultrametric bound,
inverses, powers, uniformisers. None of that is reproduced: once the point is presented as a
`HeightOneSpectrum`, those are Mathlib's `Valuation.map_mul`, `Valuation.map_add`,
`Valuation.zero_iff`, `Valuation.map_inv`, `Valuation.map_add_of_distinct_val` and
`IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer`.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain
open scoped Polynomial.Bivariate

namespace TauCeti

namespace WeierstrassCurve.Affine.CoordinateRing

variable {F : Type*} [Field F] {W : _root_.WeierstrassCurve.Affine F} {x : F}

/-- **The ideal of a point has residue degree one**: the quotient of the coordinate ring by
`⟨X - x, Y - y⟩` is one-dimensional over the base field, being the base field itself by Mathlib's
`quotientXYIdealEquiv`. -/
theorem finrank_quotient_XYIdeal {y : F} (h : W.Equation x y) :
    Module.finrank F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) = 1 := by
  rw [(CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- **A proper ideal of residue degree one is the ideal of a point.** The quotient map, followed by
the inverse of the bijection `algebraMap F (F[W] ⧸ I)`, is a ring homomorphism `F[W] → F`; it is
evaluation at the images `(x, y)` of the two coordinates, so that pair satisfies the Weierstrass
equation, and the maximal ideal it cuts out is contained in `I`, hence equal to it.

No ellipticity or Dedekind hypothesis is involved; this is the converse of
`finrank_quotient_XYIdeal`. -/
theorem exists_equation_and_eq_XYIdeal {I : Ideal W.CoordinateRing} (hI : I ≠ ⊤)
    (hdeg : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (_ : W.Equation x y), I = CoordinateRing.XYIdeal W x (C y) := by
  have hnt : Nontrivial (W.CoordinateRing ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ I)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg
  set e : (W.CoordinateRing ⧸ I) ≃+* F := (RingEquiv.ofBijective _ hbij).symm with he
  set ρ : W.CoordinateRing →+* F := (e : (W.CoordinateRing ⧸ I) →+* F).comp (Ideal.Quotient.mk I)
    with hρ
  have hρmem : ∀ a, ρ a = 0 ↔ a ∈ I := fun a ↦ by
    rw [hρ, RingHom.comp_apply, RingEquiv.coe_toRingHom, map_eq_zero_iff e e.injective,
      Ideal.Quotient.eq_zero_iff_mem]
  have hρalg : ∀ c : F, ρ (algebraMap F W.CoordinateRing c) = c := fun c ↦ by
    rw [hρ, RingHom.comp_apply, RingEquiv.coe_toRingHom, he, ← Ideal.Quotient.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply F W.CoordinateRing (W.CoordinateRing ⧸ I) c]
    exact (RingEquiv.ofBijective _ hbij).symm_apply_apply c
  set x₀ := ρ (CoordinateRing.mk W (C X)) with hx₀
  set y₀ := ρ (CoordinateRing.mk W Y) with hy₀
  -- a ring homomorphism out of the coordinate ring is evaluation at the images of the coordinates
  have hcomp : ∀ p : F[X][Y], ρ (CoordinateRing.mk W p) = p.evalEval x₀ y₀ := by
    have h : ρ.comp (CoordinateRing.mk W) = evalEvalRingHom x₀ y₀ := by
      refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
      · ext c
        have hCC : CoordinateRing.mk W (C (C c)) = algebraMap F W.CoordinateRing c := by
          rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq]
          simp
        simp only [RingHom.comp_apply, hCC, hρalg, coe_evalRingHom, eval_C]
      · simpa using hx₀.symm
      · simpa using hy₀.symm
    exact fun p ↦ congrArg (fun f ↦ f p) h
  have heq : W.Equation x₀ y₀ := by
    have h0 : ρ (CoordinateRing.mk W W.polynomial) = 0 := by rw [AdjoinRoot.mk_self, map_zero]
    rwa [hcomp] at h0
  refine ⟨x₀, y₀, heq, ((XYIdeal_isMaximal_of_equation heq).eq_of_le hI ?_).symm⟩
  rw [CoordinateRing.XYIdeal, Ideal.span_le, Set.pair_subset_iff]
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, ← hρmem, CoordinateRing.XClass, hcomp]
    simp [evalEval_C]
  · rw [SetLike.mem_coe, ← hρmem, CoordinateRing.YClass, hcomp]
    simp

variable [IsDedekindDomain W.CoordinateRing]

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
  rw [(Ideal.quotientEquivAlgOfEq F (pointPlace_asIdeal h)).toLinearEquiv.finrank_eq]
  exact finrank_quotient_XYIdeal h

/-- **Every degree-one place is the place of a point**, the converse of
`pointPlace.finrank_residueField_eq_one`. -/
theorem exists_pointPlace_eq {v : HeightOneSpectrum W.CoordinateRing}
    (hv : Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1) :
    ∃ (x y : F) (h : W.Equation x y), pointPlace h = v := by
  obtain ⟨x, y, h, hI⟩ := exists_equation_and_eq_XYIdeal v.isPrime.ne_top hv
  exact ⟨x, y, h, by rw [HeightOneSpectrum.ext_iff, pointPlace_asIdeal, hI]⟩

variable (W) in
/-- **The affine point–place dictionary**: the points of the curve correspond to the degree-one
places of its coordinate ring, a point going to the prime `⟨X - x, Y - y⟩`. Injectivity is
`pointPlace_eq_iff` and surjectivity is `exists_pointPlace_eq`. -/
noncomputable def equationEquivPointPlace :
    {xy : F × F // W.Equation xy.1 xy.2} ≃
      {v : HeightOneSpectrum W.CoordinateRing //
        Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1} :=
  Equiv.ofBijective (fun p ↦ ⟨pointPlace p.2, pointPlace.finrank_residueField_eq_one p.2⟩)
    ⟨fun p q h ↦ Subtype.ext <| Prod.ext_iff.mpr <|
        (pointPlace_eq_iff p.2 q.2).mp (Subtype.ext_iff.mp h),
      fun v ↦ by
        obtain ⟨x, y, h, hv⟩ := exists_pointPlace_eq v.2
        exact ⟨⟨(x, y), h⟩, Subtype.ext hv⟩⟩

/-- The dictionary sends a point to its place. -/
@[simp]
theorem coe_equationEquivPointPlace (p : {xy : F × F // W.Equation xy.1 xy.2}) :
    (equationEquivPointPlace W p : HeightOneSpectrum W.CoordinateRing) = pointPlace p.2 := (rfl)

variable (W) in
/-- **The point–place dictionary on the point group** of an elliptic curve: the affine points are
the degree-one places of the coordinate ring, and the point at infinity is the one further place —
here the element `WithZero` adjoins, since the place at infinity lives on the function field and
is not a prime of the coordinate ring. -/
noncomputable def pointEquivPointPlace [W.IsElliptic] :
    W.Point ≃ WithZero {v : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ v.asIdeal) = 1} :=
  (pointEquiv W).trans (equationEquivPointPlace W).optionCongr

/-- The dictionary sends the point at infinity to the adjoined element. -/
@[simp]
theorem pointEquivPointPlace_zero [W.IsElliptic] : pointEquivPointPlace W .zero = none := (rfl)

/-- The dictionary sends an affine point to its place. -/
@[simp]
theorem pointEquivPointPlace_mk [W.IsElliptic] {y : F} (h : W.Equation x y) :
    pointEquivPointPlace W (.mk h) =
      .some ⟨pointPlace h, pointPlace.finrank_residueField_eq_one h⟩ := (rfl)

end WeierstrassCurve.Affine.CoordinateRing

end TauCeti

end
