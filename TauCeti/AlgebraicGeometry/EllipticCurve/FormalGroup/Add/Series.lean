/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Chord
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Inverse

/-!
# The addition series of a Weierstrass curve

`FormalGroup/Chord.lean` produces `formalThirdRoot`, the parameter of the third point in which
the chord through the points with parameters `z₁` and `z₂` meets the curve, and
`FormalGroup/Inverse.lean` produces `formalInverse`, the parameter of the negative of a point.
The group law is the composite: the sum of two points is the *negative* of the third point of
their chord, so its parameter is

`F(z₁, z₂) = ι(z₃(z₁, z₂))`.

That series is `formalAdd`, and it is the series underlying the elliptic formal group law.

## Main definitions

* `WeierstrassCurve.formalAdd`: the addition series `F(z₁, z₂)` of `W`, in `R⟦z₁, z₂⟧`.

## Main results

* `WeierstrassCurve.constantCoeff_formalAdd`: `F(0, 0) = 0`, so `F` may itself be substituted
  into a power series, which every later statement about the group law needs. Mathlib's
  `FormalGroup` carries this as its `zero_constantCoeff` field.
* `WeierstrassCurve.rename_swap_formalAdd`: `F(z₂, z₁) = F(z₁, z₂)`. The chord does not depend
  on the order of its two points, so the group law is commutative.
* `WeierstrassCurve.map_formalAdd`: `F` commutes with base change along a ring homomorphism,
  completing the base-change block that `Chord.lean` and `Inverse.lean` already carry for the
  two series `F` is built from.

## Implementation notes

`formalAdd` is a substitution of the two-variable `formalThirdRoot` into the one-variable
`formalInverse`, so it lands in `MvPowerSeries (Unit ⊕ Unit) R` — the indexing `Chord.lean`
uses. Mathlib's `RingTheory/FormalGroup` indexes by `Fin 2` instead; the bridge between the two
belongs with the `FormalGroup` instance itself and is deliberately not built here, so that this
file stays a statement about the chord construction.

The commutativity proof reassociates the substitution rather than computing coefficients:
renaming along `Sum.swap` commutes past the outer substitution, and what is left is the
swap-invariance of `formalThirdRoot` already proved in `Chord.lean`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeierstrassFormalGroup/Chord.lean` — declarations `addSeries`,
`hasSubst_thirdRootSeries`, `constantCoeff_addSeries`, `rename_swap_addSeries` and
`map_addSeries`.

The source's `addSeries` is named `formalAdd` here, continuing the renaming this repository
already applies to the rest of that file: the source's `wSeries`, `vSeries`, `slopeSeries`,
`interceptSeries`, `thirdRootSeries` and `inverseSeries` are `formalW`, `formalU`,
`formalSlope`, `formalIntercept`, `formalThirdRoot` and `formalInverse`. `formalAdd` pairs with
`formalInverse` as the two operations of the formal group.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The two-variable family that substitutes `formalThirdRoot` for the single variable of a
one-variable series. -/
theorem hasSubst_formalThirdRoot :
    HasSubst (fun _ : Unit ↦ formalThirdRoot W) :=
  hasSubst_of_constantCoeff_zero fun _ ↦ constantCoeff_formalThirdRoot W

/-- The **addition series** of the chord construction: `F(z₁, z₂) = ι(z₃(z₁, z₂))`, the
parameter of the sum of the points with parameters `z₁` and `z₂`.

This is the series underlying the elliptic formal group law: the sum of two points is the
negative of the third point of the chord through them. -/
noncomputable def formalAdd : MvPowerSeries (Unit ⊕ Unit) R :=
  subst (fun _ : Unit ↦ formalThirdRoot W) (formalInverse W)

/-- The defining formula for `formalAdd`. -/
theorem formalAdd_def :
    formalAdd W = subst (fun _ : Unit ↦ formalThirdRoot W) (formalInverse W) :=
  (rfl)

/-- The addition series vanishes at the origin: `F(0, 0) = 0`, so `O + O = O`. This is what
allows `formalAdd` to be substituted into a power series in its turn. -/
@[simp]
theorem constantCoeff_formalAdd : constantCoeff (formalAdd W) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_formalThirdRoot W)
    (fun _ ↦ constantCoeff_formalThirdRoot W) (constantCoeff_formalInverse W)

/-- **The addition series is symmetric**: `F(z₂, z₁) = F(z₁, z₂)`. The chord through two points
does not depend on their order, so the formal group law is commutative. -/
theorem rename_swap_formalAdd : rename Sum.swap (formalAdd W) = formalAdd W := by
  rw [formalAdd_def, rename_eq_subst,
    subst_comp_subst_apply (hasSubst_formalThirdRoot W) (HasSubst.X_comp _)]
  congr 1
  funext u
  rw [← rename_eq_subst, rename_swap_formalThirdRoot W]

section BaseChange

variable {S : Type*} [CommRing S] (φ : R →+* S)

/-- **The addition series commutes with base change.** -/
@[simp]
theorem map_formalAdd :
    formalAdd (W.map φ) = MvPowerSeries.map φ (formalAdd W) := by
  rw [formalAdd_def, formalAdd_def, MvPowerSeries.map_subst (hasSubst_formalThirdRoot W)]
  congr 1
  · funext _
    exact map_formalThirdRoot W φ
  · exact map_formalInverse W φ

end BaseChange

end WeierstrassCurve
