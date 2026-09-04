/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Fin2
public import Mathlib.RingTheory.FormalGroup.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The formal group law of a Weierstrass curve

The chord construction at the point at infinity gives an addition series `formalAdd W`. This file
packages that series as Mathlib's one-dimensional `FormalGroup`: the two variables are reindexed
from the named sum `Unit ⊕ Unit` to `Fin 2`, and the previously established constant, linear, and
associativity identities supply the structure fields.

The resulting formal group is commutative because the chord addition series is symmetric. Thus
Mathlib's `FormalGroup.Point` construction gives an additive commutative monoid of
power-series-valued points whose constant coefficient is nilpotent.

## Main definitions

* `WeierstrassCurve.formalGroup`: the one-dimensional formal group law attached to a Weierstrass
  curve.

## Main results

* `WeierstrassCurve.isComm_formalGroup`: the elliptic formal group law is commutative.
* `WeierstrassCurve.map_formalGroup`: the construction commutes with base change.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.

## Provenance

The addition series and its laws are adapted in the imported modules from Michael Stoll's
`EllipticCurves` project (`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`. The packaging here is original: that source uses its
own formal-group-law structure, whereas this development refounds the construction on Mathlib's
`RingTheory/FormalGroup` API.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries

variable {R : Type*} [CommRing R]

/-- The one-dimensional commutative formal group law of a Weierstrass curve, obtained by
reindexing the chord addition series from `Unit ⊕ Unit` to Mathlib's `Fin 2` convention. -/
noncomputable def formalGroup (W : WeierstrassCurve R) : FormalGroup R where
  toPowerSeries := rename unitSumUnitEquivFinTwo (formalAdd W)
  zero_constantCoeff := by simp
  lin_coeff_X := coeff_single_zero_rename_unitSumUnitEquivFinTwo_formalAdd W
  lin_coeff_Y := coeff_single_one_rename_unitSumUnitEquivFinTwo_formalAdd W
  assoc := rename_unitSumUnitEquivFinTwo_assoc (formalAdd W) (constantCoeff_formalAdd W)
    (formalAdd_assoc W)

/-- The underlying `Fin 2`-indexed series of the formal group law is the reindexed chord addition
series. -/
@[simp]
theorem formalGroup_toPowerSeries (W : WeierstrassCurve R) :
    (formalGroup W).toPowerSeries = rename unitSumUnitEquivFinTwo (formalAdd W) :=
  by simp [formalGroup]

/-- Base change of a Weierstrass curve commutes with passage to its formal group law. -/
@[simp]
theorem map_formalGroup {S : Type*} [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S) :
    formalGroup (W.map φ) = (formalGroup W).map φ := by
  apply FormalGroup.ext
  simp [formalGroup, MvPowerSeries.rename_map]

/-- The formal group law of a Weierstrass curve is commutative. This makes its power-series-valued
points whose constant coefficient is nilpotent an additive commutative monoid through Mathlib's
standard instance. -/
noncomputable instance isComm_formalGroup (W : WeierstrassCurve R) :
    (formalGroup W).IsComm where
  comm := by
    rw [formalGroup_toPowerSeries,
      MvPowerSeries.subst_rename unitSumUnitEquivFinTwo _ HasSubst.X_X]
    nth_rw 1 [← rename_swap_formalAdd W]
    rw [rename_rename, rename_eq_subst]
    congr 1
    funext s
    rcases s with u | u <;> cases u <;>
      simp [Function.comp_def]

end WeierstrassCurve
