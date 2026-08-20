/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
import TauCeti.RingTheory.Valuation.Polynomial
import Mathlib.RingTheory.Valuation.Integral

/-!
# An isogeny carries the place at infinity to the place at infinity

An isogeny of affine Weierstrass curves is a coordinate pullback `φ : R(W₂) → K(W₁)` carrying the
integrality condition `MapsInfinity`, the algebraic form of `φ(O₁) = O₂`. This file reads that
condition off as a statement about **places**: restricting the place at infinity of `W₁` along the
function-field pullback gives the place at infinity of `W₂`,

`((W₁.infinityPlace).comap φ.fieldPullback).IsEquiv W₂.infinityPlace`.

The proof is the pole of `x`. Suppose the pulled-back coordinate `φ x₂` had no pole at `O₁`. The
Weierstrass equation of `W₂`, pulled back, then forces `φ y₂` to have no pole either — a pole of
`φ y₂` would make the left-hand side dominate a right-hand side of value at most `1` — so the whole
image `φ(R(W₂))` lies in the valuation ring at infinity of `W₁`. That ring is integrally closed,
so `MapsInfinity` puts `x₁` in it as well, contradicting the double pole `v_∞ x₁ = exp 2`. Hence
`φ x₂` has a pole at `O₁`, and
`WeierstrassCurve.Affine.isEquiv_infinityPlace_of_one_lt` identifies the restricted valuation.

Nothing here uses ellipticity, separability, or the degree of `φ`: only the pullback, the
integrality condition, and the Weierstrass equation of the target.

## Main results

* `TauCeti.Isogeny.one_lt_infinityPlace_pullback_X`: **the pulled-back coordinate has a pole at
  infinity**, `1 < v_∞ (φ x₂)`.
* `TauCeti.Isogeny.isEquiv_comap_infinityPlace`: **the place at infinity restricts to the place at
  infinity** along an isogeny.
* `TauCeti.Isogeny.comap_infinityPlace_apply_algebraMap`: the restricted valuation, evaluated on
  the image of the target coordinate ring, is `v_∞ ∘ φ` — the computation rule the other two are
  stated through.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, whose dual-isogeny milestone asks for "an
unpointed induced-place map for finite function-field embeddings, with the named criterion
`MapsInfinity λ ↔ λ_*(O₂) = O₃`, and functoriality of induced places along `λ ∘ φ = ψ` — which
yields `λ_*(O₂) = λ_*(φ_*(O₁)) = ψ_*(O₁) = O₃` at the level of places, *then* `λ` is packaged".
This file supplies the direction that the milestone applies to `φ` and to `ψ`: an isogeny pushes
the place at infinity forward to the place at infinity. It is also the Layer-0 `inducedPlace` of
`W₁.infinityPlace` along an isogeny, computed.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.
-/

public section

namespace TauCeti

open Polynomial WeierstrassCurve.Affine

open scoped Polynomial.Bivariate

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)

/-- A polynomial in the function field is the evaluation of that polynomial at the coordinate
function `x`: the structure map `F[X] → F(W)` is `aeval x`, both being `F`-algebra maps sending
`X` to `x`. -/
private theorem algebraMap_eq_aeval {W : WeierstrassCurve.Affine F} (q : F[X]) :
    algebraMap F[X] W.FunctionField q
      = Polynomial.aeval (algebraMap F[X] W.FunctionField Polynomial.X) q := by
  have h : Polynomial.aeval (R := F) (algebraMap F[X] W.FunctionField Polynomial.X)
      = IsScalarTower.toAlgHom F F[X] W.FunctionField :=
    Polynomial.algHom_ext (by simp)
  rw [h, IsScalarTower.toAlgHom_apply]

/-- The restriction of the place at infinity along an isogeny is trivial on the base field, the
pullback being an `F`-algebra map. -/
instance : ((infinityPlace W₁).comap φ.fieldPullback.toRingHom).IsTrivialOn F where
  eq_one c hc := by
    rw [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    exact Valuation.IsTrivialOn.eq_one c hc

/-- **The restricted place, evaluated on an affine function of the target**: it is the value at
infinity of the pullback of that function. -/
@[simp]
theorem comap_infinityPlace_apply_algebraMap (c : W₂.CoordinateRing) :
    ((infinityPlace W₁).comap φ.fieldPullback.toRingHom)
        (algebraMap W₂.CoordinateRing W₂.FunctionField c)
      = infinityPlace W₁ (φ.pullback c) := by
  rw [Valuation.comap_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fieldPullback_algebraMap]

/-- **The pullback of the target's coordinate `x` has a pole at the source's point at infinity.**
If it did not, then neither would the pullback of `y` — by the Weierstrass equation of the target —
so the whole pulled-back coordinate ring would lie in the valuation ring at infinity of the source;
that ring is integrally closed, so `MapsInfinity` would put the source coordinate `x₁` in it,
against its double pole. -/
theorem one_lt_infinityPlace_pullback_X :
    1 < infinityPlace W₁ (φ.pullback (algebraMap F[X] W₂.CoordinateRing Polynomial.X)) := by
  rw [← comap_infinityPlace_apply_algebraMap φ,
    ← IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField]
  set u := (infinityPlace W₁).comap φ.fieldPullback.toRingHom with hu
  by_contra hle
  rw [not_lt] at hle
  -- With `x₂` in the valuation ring, so is every polynomial in it.
  have hpoly : ∀ q : F[X], u (algebraMap F[X] W₂.FunctionField q) ≤ 1 := fun q ↦ by
    rw [algebraMap_eq_aeval]
    exact u.aeval_le_one hle q
  -- And so is `y₂`: a pole of `y₂` would make the left-hand side of the Weierstrass equation of
  -- `W₂` — the product of two factors, each of value `v y₂` — dominate its right-hand side, which
  -- is a polynomial in `x₂` and so has value at most `1`.
  have hy : u (algebraMap W₂.CoordinateRing W₂.FunctionField (CoordinateRing.mk W₂ Y)) ≤ 1 := by
    by_contra hy
    rw [not_le] at hy
    have h1 := congrArg u (mk_Y_mul_add_eq W₂)
    rw [map_mul, u.map_add_eq_of_lt_left (lt_of_le_of_lt (hpoly _) hy)] at h1
    exact absurd (h1 ▸ hpoly _) (not_le.2 (one_lt_mul_of_lt_of_le hy hy.le))
  -- The basis `{1, Y}` then puts the whole coordinate ring of `W₂` in the valuation ring.
  have hcr : ∀ c : W₂.CoordinateRing,
      u (algebraMap W₂.CoordinateRing W₂.FunctionField c) ≤ 1 := by
    intro c
    obtain ⟨a, b, rfl⟩ := CoordinateRing.exists_smul_basis_eq c
    rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_one, mul_one,
      ← IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField,
      ← IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField]
    refine (u.map_add _ _).trans (max_le (hpoly a) ?_)
    rw [map_mul]
    exact mul_le_one' (hpoly b) hy
  have hmem : ∀ c : W₂.CoordinateRing, φ.pullback c ∈ (infinityPlace W₁).integer := by
    intro c
    have h := hcr c
    rwa [hu, comap_infinityPlace_apply_algebraMap] at h
  -- `MapsInfinity` is integrality over `R(W₂)` acting through the pullback; corestricting the
  -- pullback to the valuation ring at infinity makes it integrality over that ring, which is
  -- integrally closed. So `x₁` would lie in it, against its double pole.
  let _ : Algebra W₂.CoordinateRing W₁.FunctionField := φ.pullback.toRingHom.toAlgebra
  let _ : Algebra W₂.CoordinateRing (infinityPlace W₁).integer :=
    (φ.pullback.toRingHom.codRestrict _ hmem).toAlgebra
  have : IsScalarTower W₂.CoordinateRing (infinityPlace W₁).integer W₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hint : IsIntegral (infinityPlace W₁).integer
      (algebraMap W₁.CoordinateRing W₁.FunctionField
        (algebraMap F[X] W₁.CoordinateRing Polynomial.X)) :=
    (((CoordinatePullback.mapsInfinity_iff φ.pullback).1 φ.mapsInfinity) _).tower_top
  have hle₁ := (Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers _)).1 hint
  rw [← IsScalarTower.algebraMap_apply F[X] W₁.CoordinateRing W₁.FunctionField] at hle₁
  exact absurd hle₁ (not_le.2 (one_lt_infinityPlace_X W₁))

/-- **An isogeny carries the place at infinity to the place at infinity**: the restriction of the
source's place at infinity along the function-field pullback is equivalent to the target's. This is
the place-level reading of `MapsInfinity`, that is, of `φ(O₁) = O₂`. -/
theorem isEquiv_comap_infinityPlace :
    ((infinityPlace W₁).comap φ.fieldPullback.toRingHom).IsEquiv (infinityPlace W₂) := by
  refine isEquiv_infinityPlace_of_one_lt _ ?_
  rw [IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField,
    comap_infinityPlace_apply_algebraMap]
  exact one_lt_infinityPlace_pullback_X φ

end Isogeny

end TauCeti

end
