/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MapsInfinity
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Basic
-- Proof-only, named in no statement here: the monic witness `Φₙ − C c * ΨSqₙ` with its root
-- equation.
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Integral

/-!
# `[n]` maps infinity to infinity

`Isogeny/MulByInt/Basic.lean` builds the coordinate pullback of `[n]` and records that the
`MapsInfinity` condition — and so `[n]` as an `Isogeny W W` — is not proved there. This file
proves it, for every `n` with `ψₙ` nonvanishing at the generic point.

## The argument

`CoordinatePullback.mapsInfinity_iff_isIntegralElem_genericX` reduces pointedness to a single
integral witness, so all that is `[n]`-specific is the generic `x`-coordinate: `[n]*x · ΨSqₙ(x) =
Φₙ(x)` makes it a root of `Φₙ − C ([n]*x) * ΨSqₙ`, monic by `monic_Φ_sub_C_mul_ΨSq`, with `[n]*x`
the pullback of the class of `X`.

## Main results

* `TauCeti.Isogeny.mapsInfinity_mulByIntPullback`: the pullback of `[n]` maps infinity to
  infinity.
* `TauCeti.Isogeny.mulByIntIsogeny`: `[n]` as an `Isogeny W W`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.

## Provenance

The integral witness is adapted from the AINTLIB `HasseWeil` project
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) pinned at
`513e83879e2f8cbc626eb9e04d660e92be16ccba`, `HasseWeil/MulByIntPullback.lean`, declaration
`mulByInt_x_transcendental`, which builds the same polynomial
`Φₙ.map (algebraMap F S) − C c * ΨSqₙ.map (algebraMap F S)` and the same root step, there to
contradict transcendence of the generic `x`-coordinate rather than to establish `MapsInfinity`.
Its monicity half is already in this repository as `monic_Φ_sub_C_mul_ΨSq`, itself ported from
that project's `NagellLutz`.

The `MapsInfinity` packaging is not from that source and has no counterpart in it: its `Isogeny`
carries a function-field `AlgHom` obtained by localizing an injective coordinate homomorphism,
with no pointedness field, so it never needs the `y`-coordinate step or the reduction to the two
coordinates.
-/

public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

-- Private: `mapsInfinity_mulByIntPullback` below states the stronger fact for every element of
-- the coordinate ring, so a consumer wanting this one specialises `mapsInfinity_iff` instead.
private theorem isIntegralElem_genericX [W.IsElliptic] {n : ℤ}
    (hn : psiFunctionField W n ≠ 0) :
    RingHom.IsIntegralElem (mulByIntPullback W hn).toRingHom W.genericX := by
  let _ : Algebra W.CoordinateRing W.FunctionField :=
    (mulByIntPullback W hn).toRingHom.toAlgebra
  have hmap : (algebraMap W.CoordinateRing W.FunctionField).comp
      (algebraMap F W.CoordinateRing) = algebraMap F W.FunctionField := by
    ext x; rw [RingHom.algebraMap_toAlgebra]; exact (mulByIntPullback W hn).commutes x
  -- Monicity and the root equation are the two halves of the division-polynomial criterion, and
  -- both are already available: the witness is `Φₙ − C ([n]*x) * ΨSqₙ` over the coordinate ring.
  refine ⟨(W.map (algebraMap F W.CoordinateRing)).Φ n -
      C (AdjoinRoot.of W.polynomial X) * (W.map (algebraMap F W.CoordinateRing)).ΨSq n,
    TauCeti.WeierstrassCurve.monic_Φ_sub_C_mul_ΨSq _ n _, ?_⟩
  refine TauCeti.WeierstrassCurve.aeval_Φ_sub_C_mul_ΨSq_eq_zero _ ?_
  have hx : algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.of W.polynomial X) =
      mulByIntX W n := mulByIntPullback_X W hn
  simp only [hx, _root_.WeierstrassCurve.baseChange, _root_.WeierstrassCurve.map_Φ,
    _root_.WeierstrassCurve.map_ΨSq, Polynomial.map_map, hmap, ← eval₂_eq_eval_map, ← aeval_def]
  exact mulByIntX_mul_aeval_ΨSq W n hn

/-- **The pullback of `[n]` maps infinity to infinity**, so `[n]` is an isogeny. -/
theorem mapsInfinity_mulByIntPullback [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntPullback W hn).MapsInfinity :=
  (CoordinatePullback.mapsInfinity_iff_isIntegralElem_genericX _).2
    (isIntegralElem_genericX W hn)

/-- **Multiplication by `n` as an isogeny**, for every `n` whose division polynomial does not
vanish at the generic point. -/
noncomputable def mulByIntIsogeny [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    _root_.TauCeti.Isogeny W W where
  pullback := mulByIntPullback W hn
  mapsInfinity := mapsInfinity_mulByIntPullback W hn

@[simp]
theorem mulByIntIsogeny_pullback [W.IsElliptic] {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    (mulByIntIsogeny W hn).pullback = mulByIntPullback W hn :=
  (rfl)

/-- **Multiplication by `n` as an isogeny, for every `n ≠ 0`**, the non-vanishing hypothesis
discharged by `psiFunctionField_ne_zero_of_Δ_ne_zero` as in `mulByIntPullbackOfNeZero`. -/
noncomputable abbrev mulByIntIsogenyOfNeZero [W.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    _root_.TauCeti.Isogeny W W :=
  mulByIntIsogeny W (psiFunctionField_ne_zero_of_Δ_ne_zero W W.isUnit_Δ.ne_zero hn)

end Isogeny

end TauCeti
