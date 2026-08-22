/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Place
public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime

/-!
# Rational points as degree-one places of an elliptic function field

For an elliptic Weierstrass curve `W` over a field `F`, this file completes the point--place
dictionary.  It first packages the already constructed valuation at infinity as a normalized
`TauCeti.Place F W.FunctionField`.  A place at which `x` has no pole contains the whole coordinate
ring: the coordinate ring is integral over `F[X]`, while valuation rings are integrally closed.
The general affine-model correspondence therefore identifies it with the place of a unique
height-one prime.  If `x` does have a pole, uniqueness of the elliptic valuation at infinity
identifies the place with the one at infinity.

The place at infinity has degree one.  Together with the existing equivalence between equation
solutions and degree-one primes of the coordinate ring, the preceding dichotomy gives the desired
equivalence

```
W.Point ≃ {P : TauCeti.Place F W.FunctionField // P.degree = 1}.
```

The point at infinity is sent to the place at infinity, and an affine point `(x, y)` is sent to
the normalized adic place of the maximal ideal `(X - x, Y - y)`.

## Main definitions

* `TauCeti.Place.infinity`: the normalized place at infinity of an affine Weierstrass curve.
* `WeierstrassCurve.Affine.pointEquivDegreeOnePlace`: the point--place dictionary.

## Main results

* `TauCeti.Place.exists_eq_ofPrime_iff_valuation_X_le_one`: a place is on the affine chart
  exactly when `x` has no pole there.
* `TauCeti.Place.eq_infinity_or_existsUnique_eq_ofPrime`: every place is either the place at
  infinity or the place of a unique height-one prime of the coordinate ring.
* `TauCeti.Place.degree_infinity`: the place at infinity has degree one.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0, **The point--place dictionary**: for elliptic
`W`, identify `W.toAffine.Point` with the degree-one places, taking `O` to `infinityPlace` and an
affine point to its maximal ideal.

## Provenance

Not ported.  The proof composes Tau Ceti's generic normalized-place and affine-model APIs with the
existing elliptic infinity valuation and affine point--prime dictionary.  Mathlib supplies the
coordinate ring, its finite `F[X]`-module structure, and the valuation machinery, but contains no
point--place equivalence for Weierstrass function fields.
-/

public section

open Polynomial Polynomial.Bivariate WeierstrassCurve IsDedekindDomain
open scoped RatFunc WithZero

namespace TauCeti

namespace Place

variable {F : Type*} [Field F]
variable (W : _root_.WeierstrassCurve.Affine F)

/-- The normalized place induced by `W.infinityPlace`, with value group `ℤᵐ⁰`. -/
noncomputable def infinity : Place F W.FunctionField where
  valuation := W.infinityPlace
  valuation_surjective := by
    intro z
    rcases GroupWithZero.eq_zero_or_unit z with rfl | ⟨z, rfl⟩
    · exact ⟨0, map_zero _⟩
    · refine ⟨(algebraMap W.CoordinateRing W.FunctionField
          (algebraMap F[X] W.CoordinateRing Polynomial.X) /
          algebraMap W.CoordinateRing W.FunctionField
            (WeierstrassCurve.Affine.CoordinateRing.mk W Y)) ^
          (-WithZero.log z.val), ?_⟩
      rw [map_zpow₀, WeierstrassCurve.Affine.infinityPlace.X_div_mk_Y W,
        ← WithZero.exp_zsmul]
      simp [WithZero.exp_log]
  isTrivialOn := inferInstance

@[simp]
theorem valuation_infinity : (infinity W).valuation = W.infinityPlace := by
  rw [infinity]

private theorem exists_sub_C_eq_zero_or_intDegree_neg (A : RatFunc F)
    (hA : A.intDegree ≤ 0) :
    ∃ c : F, A - RatFunc.C c = 0 ∨ (A - RatFunc.C c).intDegree < 0 := by
  classical
  by_cases hA0 : A = 0
  · exact ⟨0, by simp [hA0]⟩
  have hnum0 : A.num ≠ 0 := RatFunc.num_ne_zero hA0
  have hden0 : A.denom ≠ 0 := A.denom_ne_zero
  have hdegree : A.num.natDegree ≤ A.denom.natDegree := by
    rw [RatFunc.intDegree] at hA
    omega
  -- A strictly smaller numerator already has zero residue.  In the equal-degree case,
  -- subtract the quotient of leading coefficients to cancel the leading term.
  rcases hdegree.lt_or_eq with hdegree | hdegree
  · refine ⟨0, Or.inr ?_⟩
    simpa [hA0, RatFunc.intDegree] using
      (show (A.num.natDegree : ℤ) - A.denom.natDegree < 0 by omega)
  · let c := A.num.leadingCoeff / A.denom.leadingCoeff
    refine ⟨c, ?_⟩
    by_cases hsub : A - RatFunc.C c = 0
    · exact Or.inl hsub
    · right
      have hc0 : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hnum0)
        (Polynomial.leadingCoeff_ne_zero.mpr hden0)
      have hdenMap0 : algebraMap F[X] (RatFunc F) A.denom ≠ 0 := by
        simpa using hden0
      have hquotient : A - RatFunc.C c =
          algebraMap F[X] (RatFunc F) (A.num - Polynomial.C c * A.denom) /
            algebraMap F[X] (RatFunc F) A.denom := calc
        A - RatFunc.C c =
            algebraMap F[X] (RatFunc F) A.num /
              algebraMap F[X] (RatFunc F) A.denom - RatFunc.C c :=
          congrArg (fun z ↦ z - RatFunc.C c) (RatFunc.num_div_denom A).symm
        _ = algebraMap F[X] (RatFunc F) (A.num - Polynomial.C c * A.denom) /
              algebraMap F[X] (RatFunc F) A.denom := by
          rw [← RatFunc.algebraMap_C, map_sub, map_mul]
          field_simp [hdenMap0]
      have hpoly0 : A.num - Polynomial.C c * A.denom ≠ 0 := by
        intro h
        apply hsub
        rw [hquotient, h, map_zero, zero_div]
      have hdegrees : A.num.degree = A.denom.degree := by
        rw [Polynomial.degree_eq_natDegree hnum0, Polynomial.degree_eq_natDegree hden0, hdegree]
      have hleading : A.num.leadingCoeff =
          (Polynomial.C c * A.denom).leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
        dsimp [c]
        field_simp [Polynomial.leadingCoeff_ne_zero.mpr hden0]
      -- The cancellation makes the new numerator have smaller degree than the denominator.
      have hdegreeSub :
          (A.num - Polynomial.C c * A.denom).natDegree < A.denom.natDegree :=
        (Polynomial.natDegree_lt_natDegree_iff hpoly0).mpr <| by
          apply (Polynomial.degree_sub_lt_left
            (hdegrees.trans (Polynomial.degree_C_mul hc0).symm) hnum0 hleading).trans_eq
          exact hdegrees
      have hpolyMap0 :
          algebraMap F[X] (RatFunc F) (A.num - Polynomial.C c * A.denom) ≠ 0 :=
        (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] (RatFunc F))).mpr hpoly0
      rw [hquotient, RatFunc.intDegree_div hpolyMap0 (by simpa),
        RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
      omega

variable {W}

/-- A normalized place of `F(W) / F` lies on the affine chart exactly when `x` has no pole at
that place. -/
theorem exists_eq_ofPrime_iff_valuation_X_le_one [IsDedekindDomain W.CoordinateRing]
    (P : Place F W.FunctionField) :
    (∃ 𝔭 : HeightOneSpectrum W.CoordinateRing,
        ofPrime F W.FunctionField 𝔭 = P) ↔
      P.valuation (algebraMap F[X] W.FunctionField Polynomial.X) ≤ 1 := by
  rw [exists_eq_ofPrime_iff]
  constructor
  · intro hR
    simpa only [IsScalarTower.algebraMap_apply F[X] W.CoordinateRing W.FunctionField] using
      P.mem_integers_iff.mp (hR (algebraMap F[X] W.CoordinateRing Polynomial.X))
  · intro hx r
    apply P.mem_integers_of_isIntegral
      (R := F[X]) (fun p ↦ ?_) ((Algebra.IsIntegral.isIntegral r).map
        (IsScalarTower.toAlgHom F[X] W.CoordinateRing W.FunctionField))
    apply P.adjoin_le_integers_iff.mpr (P.mem_integers_iff.mpr hx)
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
    have heval :
        (Polynomial.aeval (algebraMap F[X] W.FunctionField Polynomial.X) :
            F[X] →ₐ[F] W.FunctionField) =
          IsScalarTower.toAlgHom F F[X] W.FunctionField := by
      apply Polynomial.algHom_ext
      rw [Polynomial.aeval_X, IsScalarTower.toAlgHom_apply]
    exact ⟨p, congrArg (fun f : F[X] →ₐ[F] W.FunctionField ↦ f p) heval⟩

/-- If the coordinate ring is Dedekind, every normalized place of a Weierstrass function field is
either the place at infinity or the place of a unique height-one prime of the coordinate ring. -/
theorem eq_infinity_or_existsUnique_eq_ofPrime [IsDedekindDomain W.CoordinateRing]
    (P : Place F W.FunctionField) :
    P = infinity W ∨ ∃! 𝔭 : HeightOneSpectrum W.CoordinateRing,
      ofPrime F W.FunctionField 𝔭 = P := by
  rcases lt_or_ge 1 (P.valuation (algebraMap F[X] W.FunctionField Polynomial.X)) with hx | hx
  · left
    exact P.eq_of_isEquiv (W.isEquiv_infinityPlace_of_one_lt (v := P.valuation) hx)
  · right
    obtain ⟨𝔭, h𝔭⟩ := (exists_eq_ofPrime_iff_valuation_X_le_one P).mpr hx
    refine ⟨𝔭, h𝔭, fun 𝔮 h𝔮 ↦ ?_⟩
    exact ofPrime_injective F W.FunctionField (h𝔮.trans h𝔭.symm)

/-- The place at infinity is rational: its residue field has degree one over the base field. -/
@[simp]
theorem degree_infinity : (infinity W).degree = 1 := by
  classical
  rw [(infinity W).degree_eq_one_iff_forall_exists_valuation_sub_lt_one]
  intro f hf
  rw [(infinity W).mem_integers_iff, valuation_infinity] at hf
  -- Write an integral function as `A + B y`, with rational functions `A`, `B`.
  obtain ⟨A, B, hAB⟩ := WeierstrassCurve.Affine.exists_ratFunc_add_mul_mk_Y W f
  have hdegrees := (WeierstrassCurve.Affine.val_add_mul_mk_Y_le_one_iff W.infinityPlace
    (WeierstrassCurve.Affine.one_lt_infinityPlace_X W) A B).mp (hAB.symm ▸ hf)
  have hAdegree : A.intDegree ≤ 0 := hdegrees.1.elim (fun h ↦ h ▸ by simp) id
  -- The residue is the leading-coefficient ratio of `A`; after subtracting it, both summands
  -- `A - c` and `B y` lie in the maximal ideal at infinity.
  obtain ⟨c, hAc⟩ := exists_sub_C_eq_zero_or_intDegree_neg A hAdegree
  refine ⟨c, ?_⟩
  have hAval : W.infinityPlace
      (algebraMap (RatFunc F) W.FunctionField (A - RatFunc.C c)) < 1 := by
    rcases hAc with hAc | hAc
    · simp [hAc]
    · have hAc0 : A - RatFunc.C c ≠ 0 := by
        intro h
        simp [h] at hAc
      rw [WeierstrassCurve.Affine.infinityPlace.algebraMap_eq_sq,
        sq_lt_one_iff₀ zero_le, RatFunc.inftyValuation_apply,
        RatFunc.inftyValuation_of_nonzero F hAc0, ← WithZero.exp_zero,
        WithZero.exp_lt_exp]
      exact hAc
  have hBval : W.infinityPlace
      (algebraMap (RatFunc F) W.FunctionField B *
        algebraMap W.CoordinateRing W.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W Y)) < 1 := by
    rcases hdegrees.2 with hB | hBdegree
    · simp [hB]
    · by_cases hB0 : B = 0
      · simp [hB0]
      · have hBnegative : 2 * B.intDegree + 3 < 0 := by omega
        rw [map_mul, WeierstrassCurve.Affine.infinityPlace.algebraMap_eq_sq,
          RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hB0,
          WeierstrassCurve.Affine.infinityPlace.mk_Y, ← WithZero.exp_nsmul,
          ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        simpa [two_nsmul] using hBnegative
  calc
    W.infinityPlace (f - algebraMap F W.FunctionField c) =
        W.infinityPlace
          (algebraMap (RatFunc F) W.FunctionField (A - RatFunc.C c) +
            algebraMap (RatFunc F) W.FunctionField B *
              algebraMap W.CoordinateRing W.FunctionField
                (WeierstrassCurve.Affine.CoordinateRing.mk W Y)) := by
      congr 1
      rw [← hAB, map_sub, IsScalarTower.algebraMap_apply F (RatFunc F) W.FunctionField,
        RatFunc.algebraMap_eq_C]
      ring
    _ < 1 := W.infinityPlace.map_add_lt hAval hBval

/-- The place at infinity is different from the place of every prime on the affine chart. -/
@[simp]
theorem infinity_ne_ofPrime [IsDedekindDomain W.CoordinateRing]
    (𝔭 : HeightOneSpectrum W.CoordinateRing) :
    infinity W ≠ ofPrime F W.FunctionField 𝔭 := by
  intro h
  have hvaluation := congrArg Place.valuation h
  rw [valuation_infinity, valuation_ofPrime] at hvaluation
  exact WeierstrassCurve.Affine.infinityPlace_ne_heightOneSpectrum_valuation W 𝔭 hvaluation

variable (W) [IsDedekindDomain W.CoordinateRing]

/-- Send the point at infinity and the degree-one affine primes to normalized degree-one places.
-/
private noncomputable def affineOrInfinityToDegreeOnePlace :
    WithZero { 𝔭 : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ 𝔭.asIdeal) = 1 } →
      { P : Place F W.FunctionField // P.degree = 1 }
  | none => ⟨infinity W, degree_infinity (W := W)⟩
  | some 𝔭 => ⟨ofPrime F W.FunctionField 𝔭.1, by
      rw [degree_ofPrime]
      exact 𝔭.2⟩

private theorem affineOrInfinityToDegreeOnePlace_bijective :
    Function.Bijective (affineOrInfinityToDegreeOnePlace W) := by
  constructor
  · rintro (_ | 𝔭) (_ | 𝔮) h
    · rfl
    · exact (infinity_ne_ofPrime (W := W) 𝔮.1 (congrArg Subtype.val h)).elim
    · exact (infinity_ne_ofPrime (W := W) 𝔭.1 (congrArg Subtype.val h).symm).elim
    · congr 1
      apply Subtype.ext
      exact ofPrime_injective F W.FunctionField (congrArg Subtype.val h)
  · intro P
    rcases eq_infinity_or_existsUnique_eq_ofPrime P.1 with hP | ⟨𝔭, h𝔭, -⟩
    · refine ⟨none, Subtype.ext hP.symm⟩
    · have hdegree : Module.finrank F (W.CoordinateRing ⧸ 𝔭.asIdeal) = 1 := by
        rw [← degree_ofPrime F W.FunctionField 𝔭, h𝔭]
        exact P.2
      exact ⟨some ⟨𝔭, hdegree⟩, Subtype.ext h𝔭⟩

/-- The degree-one normalized places are exactly the place at infinity together with the
degree-one height-one primes of the affine coordinate ring. -/
noncomputable def degreeOneAffineOrInfinityEquiv :
    WithZero { 𝔭 : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ 𝔭.asIdeal) = 1 } ≃
      { P : Place F W.FunctionField // P.degree = 1 } :=
  Equiv.ofBijective (affineOrInfinityToDegreeOnePlace W)
    (affineOrInfinityToDegreeOnePlace_bijective W)

@[simp]
theorem coe_degreeOneAffineOrInfinityEquiv_none :
    (degreeOneAffineOrInfinityEquiv W (0 : WithZero
      { 𝔭 : HeightOneSpectrum W.CoordinateRing //
        Module.finrank F (W.CoordinateRing ⧸ 𝔭.asIdeal) = 1 })).1 = infinity W := by
  rfl

@[simp]
theorem coe_degreeOneAffineOrInfinityEquiv_some
    (𝔭 : { 𝔭 : HeightOneSpectrum W.CoordinateRing //
      Module.finrank F (W.CoordinateRing ⧸ 𝔭.asIdeal) = 1 }) :
    (degreeOneAffineOrInfinityEquiv W (𝔭 : WithZero _)).1 =
      ofPrime F W.FunctionField 𝔭.1 := by
  rfl

end Place

end TauCeti

namespace WeierstrassCurve.Affine

open TauCeti TauCeti.WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : _root_.WeierstrassCurve.Affine F) [W.IsElliptic]

local instance : IsDedekindDomain W.CoordinateRing :=
  isDedekindDomain_coordinateRing W

/-- **The point--place dictionary for an elliptic curve**: rational points correspond to the
degree-one normalized places of the function field.  The point at infinity goes to
`Place.infinity W`, while `(x, y)` goes to the adic place of `(X - x, Y - y)`. -/
noncomputable def pointEquivDegreeOnePlace :
    W.Point ≃ { P : Place F W.FunctionField // P.degree = 1 } :=
  W.pointEquiv.trans <|
    (CoordinateRing.equationEquivDegreeOnePlace W).optionCongr.trans
      (Place.degreeOneAffineOrInfinityEquiv W)

/-- The point--place dictionary sends the point at infinity to the place at infinity. -/
@[simp]
theorem coe_pointEquivDegreeOnePlace_zero :
    (pointEquivDegreeOnePlace W .zero).1 = Place.infinity W := by
  exact Place.coe_degreeOneAffineOrInfinityEquiv_none W

/-- The point--place dictionary sends `(x, y)` to the normalized place of its maximal ideal. -/
@[simp]
theorem coe_pointEquivDegreeOnePlace_mk {x y : F} (h : W.Equation x y) :
    (pointEquivDegreeOnePlace W (.mk h)).1 =
      Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h) := by
  rw [← CoordinateRing.equationEquivDegreeOnePlace_apply_coe ⟨(x, y), h⟩]
  exact Place.coe_degreeOneAffineOrInfinityEquiv_some W
    (CoordinateRing.equationEquivDegreeOnePlace W ⟨(x, y), h⟩)

/-- Reading the place at infinity backwards through the dictionary recovers the point at
infinity. -/
@[simp]
theorem pointEquivDegreeOnePlace_symm_infinity :
    (pointEquivDegreeOnePlace W).symm
      ⟨Place.infinity W, Place.degree_infinity (W := W)⟩ = .zero := by
  apply (pointEquivDegreeOnePlace W).injective
  apply Subtype.ext
  simp

/-- Reading the place of an affine point backwards through the dictionary recovers that point. -/
@[simp]
theorem pointEquivDegreeOnePlace_symm_ofPrime {x y : F} (h : W.Equation x y) :
    (pointEquivDegreeOnePlace W).symm
      ⟨Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h), by
        rw [Place.degree_ofPrime]
        exact CoordinateRing.pointPlace.finrank_residueField_eq_one h⟩ = .mk h := by
  apply (pointEquivDegreeOnePlace W).injective
  apply Subtype.ext
  simp

end WeierstrassCurve.Affine

end
