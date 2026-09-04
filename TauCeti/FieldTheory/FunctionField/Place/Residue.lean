/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# The residue of a function at a place, and its norm to the constants

A function `f` that is a unit at a place `P` has a nonzero residue `f(P)` in the residue field
`F_P`, and pushing that residue down to the constants `k` by the field norm gives a value that
does not depend on `P` for its home. This file builds those two maps and extends the second by
`1` to a total function of the place.

The norm is what makes a *product over places* possible at all: `f(P)` lives in `F_P`, which
varies with `P`, so without a common target the factors of a product like Weil reciprocity's
`f(div g)` would live in different fields.

**The norm is the classical field norm exactly when `F_P` is finite over `k`.** `Algebra.norm` is
`LinearMap.det` of multiplication, so on a residue field that is *not* module-finite over `k` it
takes Mathlib's junk value `1` (`Algebra.norm_eq_one_of_not_module_finite`), and then so does
`normResidue`. That regime never arises where this API is meant to be used: over a function field
every place has finite residue degree, by `TauCeti.Place.finiteDimensional_residueField`. The
definitions below are stated without a finiteness hypothesis for the reason
`TauCeti.Place.degree` is — the hypothesis would be unused in the term, since `Algebra.norm` does
not consume one — so the guarantee is recorded here rather than in the signature.

## Main definitions

* `TauCeti.Place.residueUnit`: the residue `f(P)` of a function that is a unit at `P`, as a unit
  of the residue field.
* `TauCeti.Place.normResidue`: the norm to `k` of that residue, as a unit of `k`.
* `TauCeti.Place.normResidueOrOne`: the same, extended by `1` at the places where `f` is not a
  unit, so that it is a total function of the place. Totality is what lets
  `TauCeti.Divisor.eval` be a homomorphism outright.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 — the local factors
  of the divisor evaluation used there to construct the Weil pairing.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The residue `f(P)` of a function that is a unit at `P`**, as a unit of the residue field.
Being a unit is what makes the residue nonzero, which is what lets it be raised to a negative
power in `TauCeti.Divisor.eval`. -/
noncomputable def residueUnit (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    P.ResidueFieldˣ :=
  -- `f` lies in `𝒪_P` because `0 ≤ ord_P f`, and the coercion back to `F` of the element of
  -- `𝒪_P` so named is `rfl`, which is why `hf` and `Units.ne_zero f` apply to it verbatim.
  Units.mk0 (IsLocalRing.residue P.integers ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩)
    (by rw [Ne, P.residue_eq_zero_iff_ord_pos (Units.ne_zero f), hf]; omega)

/-- **The norm to `k` of the residue of a function that is a unit at `P`.** The residue field
varies with `P`; the norm is what puts the value in `k`, the one field all the local factors of
`TauCeti.Divisor.eval` have to share.

This is the classical field norm precisely when `Module.Finite k P.ResidueField` — which
`TauCeti.Place.finiteDimensional_residueField` supplies for every place of a function field.
Absent that, `Algebra.norm` is the junk value `1`
(`Algebra.norm_eq_one_of_not_module_finite`), exactly as `TauCeti.Place.degree` is junk `0`
absent the same hypothesis. The hypothesis is not in the signature because `Algebra.norm` does
not consume one, so requiring it here would leave it unused. -/
noncomputable def normResidue (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) : kˣ :=
  Units.map (Algebra.norm k) (P.residueUnit f hf)

/-- `normResidue` extended by `1` where `f` is not a unit, making it a total function of the
place. `1` is the only workable neutral value: the coefficient of a place in a divisor is an
*integer*, so the local factor is raised to a possibly negative power, and only a value in `kˣ`
survives that. -/
noncomputable def normResidueOrOne (P : Place k F) (f : Fˣ) : kˣ :=
  if hf : P.ord (f : F) = 0 then P.normResidue f hf else 1

@[simp]
theorem normResidueOrOne_of_ord_eq_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.normResidueOrOne f = P.normResidue f hf := by
  simp [normResidueOrOne, hf]

@[simp]
theorem normResidueOrOne_of_ord_ne_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) ≠ 0) :
    P.normResidueOrOne f = 1 := by
  simp [normResidueOrOne, hf]

end TauCeti.Place
