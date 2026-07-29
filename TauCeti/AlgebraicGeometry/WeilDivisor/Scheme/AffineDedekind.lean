/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor.Effectivity
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Basic
import Mathlib.AlgebraicGeometry.Properties

/-!
# Weil--Cartier divisors on affine Dedekind schemes

For an affine scheme `X` whose coordinate ring is Dedekind, Cartier divisors can be presented by
invertible fractional ideals of `Γ(X, ⊤)`. This file connects that affine presentation to the
scheme-theoretic Weil divisors `SchemeWeilDivisor X`.

First, codimension-one points are transported across scheme isomorphisms, and the nonzero prime
ideals of a Dedekind ring are identified with the codimension-one points of its spectrum. Transport
along `X.isoSpec` then identifies the height-one spectrum of `Γ(X, ⊤)` with the codimension-one
points of `X`. Composing this point equivalence with
`WeilDivisor.fractionalIdealDivisorAddEquiv` gives

`AffineDedekindCartierDivisor X K ≃+ SchemeWeilDivisor X`.

The equivalence identifies the integral fractional ideals with effective Weil divisors, yielding
the restricted correspondence

`AffineDedekindIntegralCartierDivisor X K ≃+
  WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X)`.

This supplies the affine-local scheme-level comparison needed for the smooth-curve
`Weil ≃ Cartier` target in Layer A of `TauCetiRoadmap/JacobianChallenge/README.md`. It does not
assert the global gluing theorem or the divisor--line-bundle dictionary.
-/

public section

open CategoryTheory IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Order AlgebraicGeometry
open scoped nonZeroDivisors

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

noncomputable section

/-- The nonzero prime ideals of a Dedekind ring are exactly the codimension-one points of its
spectrum. -/
@[expose] def heightOneSpectrumEquivCodimensionOnePoint
    (R : CommRingCat.{u}) [IsDedekindDomain R] :
    HeightOneSpectrum R ≃ CodimensionOnePoint (Spec R) where
  toFun v := ⟨⟨v.asIdeal, v.isPrime⟩, by
    rw [← AlgebraicGeometry.idealHeight_eq_coheight]
    apply le_antisymm
    · exact_mod_cast (v.asIdeal.height_le_ringKrullDim_of_isPrime).trans
        (Order.KrullDimLE.krullDim_le (n := 1))
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact v.ne_bot⟩
  invFun x :=
    ⟨x.1.asIdeal, x.1.isPrime, by
      apply Ideal.ne_bot_of_height_eq_one
      rw [AlgebraicGeometry.idealHeight_eq_coheight]
      exact x.2⟩
  left_inv v := by
    apply HeightOneSpectrum.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    rfl

/-- The codimension-one point associated to a height-one prime has that prime as its underlying
ideal. -/
@[simp]
lemma heightOneSpectrumEquivCodimensionOnePoint_apply_asIdeal
    (R : CommRingCat.{u}) [IsDedekindDomain R] (v : HeightOneSpectrum R) :
    (heightOneSpectrumEquivCodimensionOnePoint R v).1.asIdeal = v.asIdeal :=
  rfl

/-- The height-one prime associated to a codimension-one point of a spectrum is its underlying
prime ideal. -/
@[simp]
lemma heightOneSpectrumEquivCodimensionOnePoint_symm_apply_asIdeal
    (R : CommRingCat.{u}) [IsDedekindDomain R] (x : CodimensionOnePoint (Spec R)) :
    ((heightOneSpectrumEquivCodimensionOnePoint R).symm x).asIdeal = x.1.asIdeal :=
  rfl

/-- For an affine scheme with Dedekind coordinate ring, height-one prime ideals of its coordinate
ring are equivalent to codimension-one points of the scheme. -/
@[expose] def affineDedekindPointEquiv (X : Scheme.{u}) [IsAffine X]
    [IsDedekindDomain Γ(X, ⊤)] :
    HeightOneSpectrum Γ(X, ⊤) ≃ CodimensionOnePoint X :=
  (heightOneSpectrumEquivCodimensionOnePoint Γ(X, ⊤)).trans
    (codimensionOnePointEquivOfIso X.isoSpec).symm

/-- Mapping the affine codimension-one point associated to a height-one prime back to the spectrum
recovers that prime ideal. -/
@[simp]
lemma affineDedekindPointEquiv_apply_asIdeal (X : Scheme.{u}) [IsAffine X]
    [IsDedekindDomain Γ(X, ⊤)] (v : HeightOneSpectrum Γ(X, ⊤)) :
    (X.isoSpec.hom (affineDedekindPointEquiv X v).1).asIdeal = v.asIdeal := by
  have h := congrArg (fun x : CodimensionOnePoint (Spec Γ(X, ⊤)) ↦ x.1.asIdeal)
    ((codimensionOnePointEquivOfIso X.isoSpec).apply_symm_apply
      (heightOneSpectrumEquivCodimensionOnePoint Γ(X, ⊤) v))
  simpa only [affineDedekindPointEquiv, Equiv.trans_apply,
    codimensionOnePointEquivOfIso_apply_coe,
    codimensionOnePointEquivOfIso_symm_apply_coe,
    heightOneSpectrumEquivCodimensionOnePoint_apply_asIdeal] using h

/-- The height-one prime associated to an affine codimension-one point is the prime ideal obtained
by mapping that point to the spectrum. -/
@[simp]
lemma affineDedekindPointEquiv_symm_apply_asIdeal (X : Scheme.{u}) [IsAffine X]
    [IsDedekindDomain Γ(X, ⊤)] (x : CodimensionOnePoint X) :
    ((affineDedekindPointEquiv X).symm x).asIdeal = (X.isoSpec.hom x.1).asIdeal :=
  rfl

/-- Cartier divisors on an affine Dedekind scheme, presented as invertible fractional ideals of
its coordinate ring in a chosen fraction field. -/
abbrev AffineDedekindCartierDivisor (X : Scheme.{u}) (K : Type u)
    [Field K] [Algebra Γ(X, ⊤) K] :=
  Additive (FractionalIdeal (Γ(X, ⊤))⁰ K)ˣ

/-- Integral Cartier divisors on an affine Dedekind scheme, presented as the invertible fractional
ideals contained in its coordinate ring. -/
abbrev AffineDedekindIntegralCartierDivisor (X : Scheme.{u}) (K : Type u)
    [Field K] [Algebra Γ(X, ⊤) K] [IsFractionRing Γ(X, ⊤) K]
    [IsDedekindDomain Γ(X, ⊤)] :=
  WeilDivisor.integralFractionalIdealSubmonoid Γ(X, ⊤) K

/-- The Weil--Cartier correspondence for an affine Dedekind scheme. It sends an invertible
fractional ideal to its height-one multiplicities, indexed by the corresponding codimension-one
points of the scheme. -/
@[expose] def affineDedekindWeilCartierAddEquiv (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)] :
    AffineDedekindCartierDivisor X K ≃+ SchemeWeilDivisor X :=
  (WeilDivisor.fractionalIdealDivisorAddEquiv Γ(X, ⊤) K).trans
    (Finsupp.domCongr (affineDedekindPointEquiv X))

/-- The coefficient of the Weil divisor associated to an affine Cartier divisor is its
multiplicity at the corresponding height-one prime. -/
@[simp]
lemma coeff_affineDedekindWeilCartierAddEquiv (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)]
    (I : AffineDedekindCartierDivisor X K) (x : CodimensionOnePoint X) :
    WeilDivisor.coeff (affineDedekindWeilCartierAddEquiv X K I) x =
      FractionalIdeal.count K ((affineDedekindPointEquiv X).symm x)
        (Units.val (Additive.toMul I)) := by
  calc
    WeilDivisor.coeff (affineDedekindWeilCartierAddEquiv X K I) x =
        WeilDivisor.coeff (WeilDivisor.fractionalIdealDivisor Γ(X, ⊤) K I)
          ((affineDedekindPointEquiv X).symm x) := by
      rw [affineDedekindWeilCartierAddEquiv, AddEquiv.trans_apply,
        WeilDivisor.fractionalIdealDivisorAddEquiv_apply, Finsupp.domCongr_apply]
      simpa only [WeilDivisor.coeff] using
        Finsupp.equivMapDomain_apply (affineDedekindPointEquiv X)
          (WeilDivisor.fractionalIdealDivisor Γ(X, ⊤) K I) x
    _ = _ := WeilDivisor.coeff_fractionalIdealDivisor
      (R := Γ(X, ⊤)) (K := K) I _

/-- An affine Cartier divisor has an effective associated Weil divisor exactly when its
fractional ideal is integral. -/
lemma isEffective_affineDedekindWeilCartierAddEquiv_iff
    (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)]
    (I : AffineDedekindCartierDivisor X K) :
    WeilDivisor.IsEffective (affineDedekindWeilCartierAddEquiv X K I) ↔
      I ∈ AffineDedekindIntegralCartierDivisor X K := by
  constructor
  · intro hI
    rw [WeilDivisor.mem_integralFractionalIdealSubmonoid]
    apply WeilDivisor.le_one_of_isEffective_fractionalIdealDivisor I
    rw [WeilDivisor.isEffective_iff]
    intro v
    rw [WeilDivisor.coeff_fractionalIdealDivisor]
    have hv := (WeilDivisor.isEffective_iff _).mp hI (affineDedekindPointEquiv X v)
    simpa only [coeff_affineDedekindWeilCartierAddEquiv, Equiv.symm_apply_apply] using hv
  · intro hI
    rw [WeilDivisor.isEffective_iff]
    intro x
    rw [coeff_affineDedekindWeilCartierAddEquiv]
    have hFractional :=
      (WeilDivisor.isEffective_fractionalIdealDivisor_iff_mem I).mpr hI
    simpa only [WeilDivisor.coeff_fractionalIdealDivisor] using
      (WeilDivisor.isEffective_iff _).mp hFractional
        ((affineDedekindPointEquiv X).symm x)

/-- The affine Weil--Cartier correspondence restricted to positive objects: integral Cartier
divisors correspond exactly to effective scheme-theoretic Weil divisors. -/
@[expose] def affineDedekindEffectiveWeilCartierAddEquiv (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)] :
    AffineDedekindIntegralCartierDivisor X K ≃+
      WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X) where
  toFun I :=
    ⟨affineDedekindWeilCartierAddEquiv X K I,
      (WeilDivisor.mem_effectiveSubmonoid _).mpr
        ((isEffective_affineDedekindWeilCartierAddEquiv_iff X K I).mpr I.property)⟩
  invFun D :=
    ⟨(affineDedekindWeilCartierAddEquiv X K).symm D,
      (isEffective_affineDedekindWeilCartierAddEquiv_iff X K
        ((affineDedekindWeilCartierAddEquiv X K).symm D)).mp <| by
        simpa only [AddEquiv.apply_symm_apply] using
          (WeilDivisor.mem_effectiveSubmonoid (D : SchemeWeilDivisor X)).mp D.property⟩
  left_inv I := Subtype.ext <| (affineDedekindWeilCartierAddEquiv X K).symm_apply_apply I
  right_inv D := Subtype.ext <| (affineDedekindWeilCartierAddEquiv X K).apply_symm_apply D
  map_add' I J := Subtype.ext <|
    (affineDedekindWeilCartierAddEquiv X K).map_add
      (I : AffineDedekindCartierDivisor X K) J

/-- The restricted affine Weil--Cartier equivalence agrees with the unrestricted equivalence after
forgetting integrality and effectivity. -/
@[simp]
lemma coe_affineDedekindEffectiveWeilCartierAddEquiv
    (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)]
    (I : AffineDedekindIntegralCartierDivisor X K) :
    ((affineDedekindEffectiveWeilCartierAddEquiv X K I :
        WeilDivisor.effectiveSubmonoid (CodimensionOnePoint X)) :
      SchemeWeilDivisor X) =
      affineDedekindWeilCartierAddEquiv X K I :=
  rfl

/-- The prime fractional ideal at `v` corresponds to the point divisor at the associated
codimension-one point of the affine scheme. -/
@[simp]
lemma affineDedekindWeilCartierAddEquiv_asIdeal (X : Scheme.{u}) (K : Type u)
    [IsAffine X] [Field K] [Algebra Γ(X, ⊤) K]
    [IsFractionRing Γ(X, ⊤) K] [IsDedekindDomain Γ(X, ⊤)]
    (v : HeightOneSpectrum Γ(X, ⊤)) :
    affineDedekindWeilCartierAddEquiv X K
        (Additive.ofMul
          (Units.mk0 (v.asIdeal : FractionalIdeal (Γ(X, ⊤))⁰ K)
            (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))) =
      WeilDivisor.ofPoint (affineDedekindPointEquiv X v) := by
  rw [affineDedekindWeilCartierAddEquiv, AddEquiv.trans_apply,
    WeilDivisor.fractionalIdealDivisorAddEquiv_apply, Finsupp.domCongr_apply,
    WeilDivisor.fractionalIdealDivisor_asIdeal]
  apply WeilDivisor.ext
  intro x
  calc
    WeilDivisor.coeff
        (Finsupp.equivMapDomain (affineDedekindPointEquiv X)
          (WeilDivisor.ofPoint v)) x =
        WeilDivisor.coeff (WeilDivisor.ofPoint v)
          ((affineDedekindPointEquiv X).symm x) := by
      simpa only [WeilDivisor.coeff] using
        Finsupp.equivMapDomain_apply (affineDedekindPointEquiv X)
          (WeilDivisor.ofPoint v) x
    _ = WeilDivisor.coeff (WeilDivisor.ofPoint (affineDedekindPointEquiv X v)) x := by
      by_cases hx : x = affineDedekindPointEquiv X v
      · subst x
        rw [Equiv.symm_apply_apply, WeilDivisor.coeff_ofPoint_self,
          WeilDivisor.coeff_ofPoint_self]
      · have hx' : (affineDedekindPointEquiv X).symm x ≠ v := fun h ↦
          hx (by simpa using congrArg (affineDedekindPointEquiv X) h)
        rw [WeilDivisor.coeff_ofPoint_of_ne hx', WeilDivisor.coeff_ofPoint_of_ne hx]

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
