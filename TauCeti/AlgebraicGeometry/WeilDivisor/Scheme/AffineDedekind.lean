/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.FractionalIdealDivisor
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

/-- A scheme isomorphism identifies the codimension-one points of its source and target. -/
def codimensionOnePointEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    CodimensionOnePoint X ≃ CodimensionOnePoint Y where
  toFun x := ⟨e.hom x, (coheight_eq_of_isOpenImmersion e.hom).trans x.2⟩
  invFun y := ⟨e.inv y, (coheight_eq_of_isOpenImmersion e.inv).trans y.2⟩
  left_inv x := by
    apply Subtype.ext
    change (e.hom ≫ e.inv) x = x
    rw [e.hom_inv_id]
    rfl
  right_inv y := by
    apply Subtype.ext
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl

/-- The nonzero prime ideals of a Dedekind ring are exactly the codimension-one points of its
spectrum. -/
def heightOneSpectrumEquivCodimensionOnePoint (R : CommRingCat.{u}) [IsDedekindDomain R] :
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

/-- For an affine scheme with Dedekind coordinate ring, height-one prime ideals of its coordinate
ring are equivalent to codimension-one points of the scheme. -/
def affineDedekindPointEquiv (X : Scheme.{u}) [IsAffine X]
    [IsDedekindDomain Γ(X, ⊤)] :
    HeightOneSpectrum Γ(X, ⊤) ≃ CodimensionOnePoint X :=
  (heightOneSpectrumEquivCodimensionOnePoint Γ(X, ⊤)).trans
    (codimensionOnePointEquivOfIso X.isoSpec).symm

/-- Cartier divisors on an affine Dedekind scheme, presented as invertible fractional ideals of
its coordinate ring in a chosen fraction field. -/
abbrev AffineDedekindCartierDivisor (X : Scheme.{u}) (K : Type u)
    [Field K] [Algebra Γ(X, ⊤) K] :=
  Additive (FractionalIdeal (Γ(X, ⊤))⁰ K)ˣ

/-- The Weil--Cartier correspondence for an affine Dedekind scheme. It sends an invertible
fractional ideal to its height-one multiplicities, indexed by the corresponding codimension-one
points of the scheme. -/
def affineDedekindWeilCartierAddEquiv (X : Scheme.{u}) (K : Type u)
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
      change Finsupp.equivMapDomain (affineDedekindPointEquiv X)
          (WeilDivisor.fractionalIdealDivisor Γ(X, ⊤) K I) x = _
      exact Finsupp.equivMapDomain_apply _ _ _
    _ = _ := WeilDivisor.coeff_fractionalIdealDivisor
      (R := Γ(X, ⊤)) (K := K) I _

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
    WeilDivisor.fractionalIdealDivisorAddEquiv_apply, Finsupp.domCongr_apply]
  change Finsupp.equivMapDomain (affineDedekindPointEquiv X)
      (WeilDivisor.fractionalIdealDivisor Γ(X, ⊤) K
        (Additive.ofMul
          (Units.mk0 (v.asIdeal : FractionalIdeal (Γ(X, ⊤))⁰ K)
            (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)))) = _
  rw [WeilDivisor.fractionalIdealDivisor_asIdeal]
  apply WeilDivisor.ext
  intro x
  change Finsupp.equivMapDomain (affineDedekindPointEquiv X)
      (WeilDivisor.ofPoint v) x =
    WeilDivisor.coeff (WeilDivisor.ofPoint (affineDedekindPointEquiv X v)) x
  rw [Finsupp.equivMapDomain_apply]
  change WeilDivisor.coeff (WeilDivisor.ofPoint v)
      ((affineDedekindPointEquiv X).symm x) =
    WeilDivisor.coeff (WeilDivisor.ofPoint (affineDedekindPointEquiv X v)) x
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
