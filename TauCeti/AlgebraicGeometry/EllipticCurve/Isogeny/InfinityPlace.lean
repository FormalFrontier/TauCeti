/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FunctionField
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.RingTheory.Valuation.IntegralOfValuationLeOne
import TauCeti.RingTheory.Valuation.Polynomial
import Mathlib.RingTheory.Valuation.Integral

/-!
# Pointedness at the place at infinity

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

Conversely, a bare function-field embedding is a pointed coordinate pullback when it carries the
place at infinity to the place at infinity. The proof uses
`TauCeti.isIntegral_of_forall_valuation_le_one`: a valuation bounded on the pulled-back coordinate
ring is either trivial, or its proper valuation subring is the ring of a place. If the source
coordinate had a pole there, uniqueness would identify that place with infinity, contradicting
boundedness of the pulled-back target coordinate. This makes the source coordinate integral;
integrality of the coordinate ring over the polynomial ring then gives `MapsInfinity`.

Neither direction uses ellipticity, separability, or the degree of an isogeny.

## Main results

* `TauCeti.Isogeny.one_lt_infinityPlace_pullback_X`: **the pulled-back coordinate has a pole at
  infinity**, `1 < v_∞ (φ x₂)`.
* `TauCeti.Isogeny.isEquiv_comap_infinityPlace`: **the place at infinity restricts to the place at
  infinity** along an isogeny.
* `TauCeti.Isogeny.comap_infinityPlace_apply_algebraMap`: the restricted valuation, evaluated on
  the image of the target coordinate ring, is `v_∞ ∘ φ` — the computation rule the other two are
  stated through.
* `TauCeti.CoordinatePullback.mapsInfinity_iff_isEquiv_comap_infinityPlace`: **the pointedness
  criterion**, `MapsInfinity σ ↔ σ_*(O₁) = O₂`, for an embedding `σ` of function fields.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**, whose dual-isogeny milestone asks for "an
unpointed induced-place map for finite function-field embeddings, with the named criterion
`MapsInfinity λ ↔ λ_*(O₂) = O₃`, and functoriality of induced places along `λ ∘ φ = ψ` — which
yields `λ_*(O₂) = λ_*(φ_*(O₁)) = ψ_*(O₁) = O₃` at the level of places, *then* `λ` is packaged".
This file supplies both the named criterion and the direction it applies to `φ` and to `ψ`: an
isogeny pushes the place at infinity forward to the place at infinity. It is also the Layer-0
`inducedPlace` of `W₁.infinityPlace` along an isogeny, computed.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.
-/

public section

namespace TauCeti

open _root_.Polynomial WeierstrassCurve.Affine

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
    exact u.aeval_le_one (Valuation.IsTrivialOn.valuation_algebraMap_le_one u) hle q
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

namespace CoordinatePullback

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- Once an `F`-algebra map into the function field of `W₁` sends some element to one with a pole
at infinity, the affine coordinate of `W₁` is integral over the image of that map. -/
private theorem isIntegral_X_over_range_of_one_lt_infinityPlace {A : Type*} [CommSemiring A]
    [Algebra F A] (f : A →ₐ[F] W₁.FunctionField) (a : A) (h : 1 < infinityPlace W₁ (f a)) :
    IsIntegral f.range.toSubring (algebraMap F[X] W₁.FunctionField X) :=
  isIntegral_of_forall_valuation_le_one fun v hvle ↦ by
    let _ : ValuativeRel W₁.FunctionField := v
    let u := ValuativeRel.valuation W₁.FunctionField
    have hmemV : ∀ c : A, f c ∈ u.valuationSubring := fun c ↦
      (Valuation.mem_valuationSubring_iff _ _).2
        ((Valuation.vle_one_iff u).1 (hvle (f c) ⟨c, rfl⟩))
    have hFV : ∀ c : F, algebraMap F W₁.FunctionField c ∈ u.valuationSubring := fun c ↦ by
      rw [← f.commutes]
      exact hmemV _
    by_cases hu : u.valuationSubring = ⊤
    · exact (Valuation.vle_one_iff u).2
        ((Valuation.mem_valuationSubring_iff _ _).1 (hu ▸ trivial))
    · set P := Place.ofValuationSubring W₁.isFunctionField hFV hu
      have hPint : P.integers = u.valuationSubring :=
        Place.integers_ofValuationSubring _ hFV hu
      by_contra hx
      have hpole : 1 < P.valuation (algebraMap F[X] W₁.FunctionField X) :=
        not_le.1 fun hle ↦ hx ((Valuation.vle_one_iff u).2
          ((Valuation.mem_valuationSubring_iff _ _).1
            (hPint ▸ P.mem_integers_iff.2 hle)))
      have hequiv := isEquiv_infinityPlace_of_one_lt (W := W₁) (v := P.valuation) hpole
      refine absurd ((Valuation.isEquiv_iff_val_le_one.1 hequiv).1 ?_) (not_le.2 h)
      exact P.mem_integers_iff.1 (hPint ▸ hmemV _)

/-- **An embedding of function fields under which `x` acquires a pole at infinity maps infinity
to infinity.** -/
theorem mapsInfinity_of_one_lt_infinityPlace (σ : W₂.FunctionField →ₐ[F] W₁.FunctionField)
    (h : 1 < infinityPlace W₁ (σ (algebraMap F[X] W₂.FunctionField X))) :
    MapsInfinity (σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)) := by
  rw [mapsInfinity_iff]
  let f := σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)
  let _ := f.toRingHom.toAlgebra
  set C := integralClosure W₂.CoordinateRing W₁.FunctionField
  -- The affine coordinate of `W₁` is integral over the pulled-back coordinate ring.
  have hx₁ : algebraMap F[X] W₁.FunctionField X ∈ C := by
    rw [mem_integralClosure_iff]
    have hf : Function.Injective f :=
      σ.injective.comp (IsFractionRing.injective W₂.CoordinateRing W₂.FunctionField)
    have hfX : f (algebraMap F[X] W₂.CoordinateRing X) = σ (algebraMap F[X] W₂.FunctionField X) :=
      (congrArg σ (IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField X)).symm
    let e := (AlgEquiv.ofInjective f hf).toRingEquiv
    exact (e.isIntegral_iff (by rfl) _).2
      (isIntegral_X_over_range_of_one_lt_infinityPlace f _ (by rw [hfX]; exact h))
  -- Every polynomial in that coordinate is then integral, so `F[X]` acts on the integral closure.
  have hmemq : ∀ q : F[X], algebraMap F[X] W₁.FunctionField q ∈ C := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply F F[X] W₁.FunctionField,
        IsScalarTower.algebraMap_apply F W₂.CoordinateRing W₁.FunctionField]
      exact Subalgebra.algebraMap_mem C _
    | add p q hp hq => simpa using C.add_mem hp hq
    | monomial n a hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact C.mul_mem hn hx₁
  let _ := ((algebraMap F[X] W₁.FunctionField).codRestrict C hmemq).toAlgebra
  have : IsScalarTower F[X] C W₁.FunctionField := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- The coordinate ring of `W₁` is integral over `F[X]`, hence over the integral closure.
  intro z
  refine isIntegral_trans (A := C) _ (IsIntegral.tower_top (R := F[X]) ?_)
  exact (Algebra.IsIntegral.isIntegral (R := F[X]) z).map
    (IsScalarTower.toAlgHom F[X] W₁.CoordinateRing W₁.FunctionField)

/-- **The pointedness criterion.** An embedding `σ : F(W₂) → F(W₁)` restricts to a coordinate
pullback which maps infinity to infinity exactly when the source's place at infinity restricts
along `σ` to the target's place at infinity. -/
theorem mapsInfinity_iff_isEquiv_comap_infinityPlace
    (σ : W₂.FunctionField →ₐ[F] W₁.FunctionField) :
    MapsInfinity (σ.comp (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField)) ↔
      ((infinityPlace W₁).comap σ.toRingHom).IsEquiv (infinityPlace W₂) := by
  constructor
  · intro hσ
    have hfield : ({ pullback := _, mapsInfinity := hσ } :
        Isogeny W₁ W₂).fieldPullback = σ :=
      (Isogeny.fieldPullback_unique _ σ fun _ ↦ rfl).symm
    exact hfield ▸ Isogeny.isEquiv_comap_infinityPlace ⟨_, hσ⟩
  · intro hσ
    refine mapsInfinity_of_one_lt_infinityPlace σ (not_le.1 fun hle ↦ ?_)
    exact absurd ((Valuation.isEquiv_iff_val_le_one.1 hσ).1 hle)
      (not_le.2 (one_lt_infinityPlace_X W₂))

end CoordinatePullback

end TauCeti

end
