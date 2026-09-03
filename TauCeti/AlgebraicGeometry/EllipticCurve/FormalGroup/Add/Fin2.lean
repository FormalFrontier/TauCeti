/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Unit
public import TauCeti.Data.Fin.Sum
import TauCeti.RingTheory.MvPowerSeries.Rename

/-!
# The addition series presented over `Fin 2`

`formalAdd` is indexed by `Unit ⊕ Unit`, one variable per chord parameter, which is the shape every
series-level lemma about it is stated in. Mathlib's `FormalGroup`, by contrast, carries a power
series in `MvPowerSeries (Fin 2) R`. This file transports the two linear coefficients along the
reindexing `unitSumUnitEquivFinTwo`.

Those two are the `lin_coeff_X` and `lin_coeff_Y` fields of the eventual `FormalGroup` instance.
The other fields need no lemma of their own: `zero_constantCoeff` is discharged by `simp` from
`MvPowerSeries.constantCoeff_rename` and `constantCoeff_formalAdd`, and the substitution law that
will carry associativity into the `assoc` field's shape is the general
`MvPowerSeries.subst_rename`, applied at the construction site.

`formalAdd` over `Unit ⊕ Unit` stays the working object: nothing here re-founds it over `Fin 2`,
and the `Fin 2` presentation is not a second public spelling of the addition series — it exists to
be the `toPowerSeries` field of the instance.

## Main results

* `WeierstrassCurve.coeff_single_zero_rename_unitSumUnitEquivFinTwo_formalAdd` and
  `WeierstrassCurve.coeff_single_one_rename_unitSumUnitEquivFinTwo_formalAdd`:
  the two linear coefficients.

## Provenance

No external source. Michael Stoll's development states the group law over `Unit`-indexed sums
throughout and bundles it into his own `FormalGroupLaw` structure, so the reindexing has no
counterpart there; it is the cost of refounding on Mathlib's `FormalGroup`, whose `assoc` field is
stated over `Fin 2`.
-/

public section

namespace WeierstrassCurve

open MvPowerSeries Filter Finsupp

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The linear coefficient of the reindexed addition series in the variable `0` is `1` — the
`lin_coeff_X` field. -/
@[simp]
theorem coeff_single_zero_rename_unitSumUnitEquivFinTwo_formalAdd :
    coeff (single (0 : Fin 2) 1)
      (rename unitSumUnitEquivFinTwo (formalAdd W)) = 1 := by
  have h := coeff_single_rename unitSumUnitEquivFinTwo.toEmbedding (formalAdd W) (Sum.inl ()) 1
  simpa using h.trans (coeff_single_inl_formalAdd W)

/-- The linear coefficient of the reindexed addition series in the variable `1` is `1` — the
`lin_coeff_Y` field. -/
@[simp]
theorem coeff_single_one_rename_unitSumUnitEquivFinTwo_formalAdd :
    coeff (single (1 : Fin 2) 1)
      (rename unitSumUnitEquivFinTwo (formalAdd W)) = 1 := by
  have h := coeff_single_rename unitSumUnitEquivFinTwo.toEmbedding (formalAdd W) (Sum.inr ()) 1
  simpa using h.trans (coeff_single_inr_formalAdd W)

end WeierstrassCurve
