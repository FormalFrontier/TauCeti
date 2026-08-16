/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FrobeniusTower
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The Frobenius isogeny

Over a finite field `F` with `q = Nat.card F` elements, raising to the `q`-th power is an
`F`-algebra endomorphism of any `F`-algebra (`FiniteField.frobeniusAlgHom`). Composing it with
the embedding of the coordinate ring into the function field gives a coordinate pullback, and
that pullback maps infinity to infinity, so it is an isogeny of `W` with itself. Its degree
is `q`.

The declarations take `[Finite F]` rather than `[Fintype F]`, matching
`Affine/FrobeniusTower.lean`, and state the exponent as `Nat.card F`: a `Fintype` instance is
chosen enumeration data, and neither the definitions nor the statements should depend on it. The
instance Mathlib's map needs is installed locally where it is required.

## Main definitions

* `TauCeti.Isogeny.frobeniusPullback`: the coordinate pullback `x ↦ x ^ q`.
* `TauCeti.Isogeny.frobeniusIsogeny`: the same map packaged as an `Isogeny W W`.

## Main results

* `TauCeti.Isogeny.fieldPullback_frobeniusIsogeny`: the induced map of function fields is the
  `q`-power map `FiniteField.frobeniusAlgHom F W.FunctionField`.
* `TauCeti.Isogeny.degree_frobeniusIsogeny`: the Frobenius isogeny has degree `q`.

The `MapsInfinity` condition says that each `x` of the coordinate ring is integral over the
pulled-back copy. It holds because `x` is a `q`-th root of its own pullback, so `IsIntegral.of_pow`
reduces it to integrality of an element the pullback already produces. That is what "Frobenius
fixes the point at infinity" amounts to here.

The degree is the field-theoretic
`TauCeti.WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom`, `[K(W) : K(W)^q] = q`,
transported along the identification of `fieldPullback` with the `q`-power map on `K(W)`. That
identification is `Isogeny.fieldPullback_unique`: both maps restrict to `x ↦ x ^ q` on the
coordinate ring, and only one extension to the fraction field exists.

This is the `frobeniusIsogeny` seed of `TauCetiRoadmap/EllipticCurves/README.md` §Layer 1, where
it is described as "`f ↦ f ^ q` out of the coordinate ring into the function field … whose
`MapsInfinity` is the integrality of the coordinates over their `q`-th powers". The seed follows
Silverman, *The Arithmetic of Elliptic Curves*, II.2.11, whose part (c) is the degree. The
roadmap's `Suggested.lean` states both with `sorry`; the proofs here are original.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Finite F] (W : WeierstrassCurve.Affine F)

namespace Isogeny

/-- The Frobenius coordinate pullback: an element of the coordinate ring is sent to its `q`-th
power, viewed in the function field, where `q = Nat.card F`. -/
noncomputable def frobeniusPullback : CoordinatePullback W W :=
  letI := Fintype.ofFinite F
  (IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField).comp
    (FiniteField.frobeniusAlgHom F W.CoordinateRing)

/-- The Frobenius pullback raises to the `q`-th power. -/
@[simp]
theorem frobeniusPullback_apply (x : W.CoordinateRing) :
    frobeniusPullback W x = algebraMap W.CoordinateRing W.FunctionField (x ^ Nat.card F) := by
  let _ := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, frobeniusPullback]
  simp only [AlgHom.comp_apply, FiniteField.coe_frobeniusAlgHom, IsScalarTower.toAlgHom_apply]

/-- **Frobenius maps the point at infinity to itself.** An element of the coordinate ring is a
`q`-th root of its own pullback, so it is integral over the pulled-back copy. -/
theorem mapsInfinity_frobeniusPullback : (frobeniusPullback W).MapsInfinity := by
  rw [CoordinatePullback.mapsInfinity_iff]
  let _ := (frobeniusPullback W).toRingHom.toAlgebra
  intro x
  refine IsIntegral.of_pow (n := Nat.card F) Nat.card_pos ?_
  rw [← map_pow, ← frobeniusPullback_apply]
  exact isIntegral_algebraMap

/-- **The Frobenius isogeny** of a Weierstrass curve over a finite field. -/
noncomputable def frobeniusIsogeny : Isogeny W W where
  pullback := frobeniusPullback W
  mapsInfinity := mapsInfinity_frobeniusPullback W

/-- The Frobenius isogeny's pullback is the `q`-th power map. -/
@[simp]
theorem frobeniusIsogeny_pullback : (frobeniusIsogeny W).pullback = frobeniusPullback W := (rfl)

/-- The function field pullback of the Frobenius isogeny is the `q`-power map of the function
field: the two agree on the coordinate ring, and an isogeny's `fieldPullback` is the only such
extension. -/
theorem fieldPullback_frobeniusIsogeny :
    letI := Fintype.ofFinite F
    (frobeniusIsogeny W).fieldPullback = FiniteField.frobeniusAlgHom F W.FunctionField := by
  let _ := Fintype.ofFinite F
  refine ((frobeniusIsogeny W).fieldPullback_unique _ fun x ↦ ?_).symm
  simp only [FiniteField.coe_frobeniusAlgHom, frobeniusIsogeny_pullback, frobeniusPullback_apply,
    Nat.card_eq_fintype_card, map_pow]

/-- **The Frobenius isogeny has degree `q`.** Its function-field pullback is the `q`-power map,
so the extension the degree measures is `K(W)` over its subfield of `q`-th powers. -/
@[simp]
theorem degree_frobeniusIsogeny : (frobeniusIsogeny W).degree = Nat.card F := by
  let _ := Fintype.ofFinite F
  rw [degree_def, fieldPullback_frobeniusIsogeny W]
  exact WeierstrassCurve.Affine.finrank_fieldRange_frobeniusAlgHom W

end Isogeny

end TauCeti

end
