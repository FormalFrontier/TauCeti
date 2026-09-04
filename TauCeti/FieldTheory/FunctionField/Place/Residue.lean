/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic
public import TauCeti.RingTheory.Norm.Units

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

## Main results

* `TauCeti.Place.coe_residueUnit` and `TauCeti.Place.coe_normResidue`: the underlying field values
  of the two units: `IsLocalRing.residue` and the `Algebra.norm` of it. Both are `@[simp]`, and
  are named after `TauCeti.Algebra.coe_normUnits`, the adjacent lemma of the same shape.
* `TauCeti.Place.normResidueOrOne_of_ord_eq_zero` and
  `TauCeti.Place.normResidueOrOne_of_ord_ne_zero`: the two branches of the total extension.
* The group laws in the function: `residueUnit_one`, `residueUnit_mul`, `residueUnit_inv` and
  their `normResidue` counterparts, together with `normResidueOrOne_one`, `normResidueOrOne_mul`
  and `normResidueOrOne_inv` for the total form. Each of the partial ones takes the order
  hypothesis of the *combined* function as an argument of its own, since that proof is what
  indexes the left-hand side; the total form takes no such argument, which is what makes it the
  form `TauCeti.Divisor.eval` is built on. The total form is asymmetric:
  `normResidueOrOne_mul` needs both factors admissible, while `normResidueOrOne_inv` needs
  nothing, since `ord_P f⁻¹ = -ord_P f` vanishes exactly when `ord_P f` does.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 — the local factors
  of the divisor evaluation used there to construct the Weil pairing.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A function of order zero at `P` lies in the unit group of `𝒪_P`: order zero is valuation one,
which is exactly `ValuationSubring.mem_unitGroup_iff`. -/
theorem mem_unitGroup_of_ord_eq_zero (P : Place k F) {f : Fˣ} (hf : P.ord (f : F) = 0) :
    f ∈ P.integers.unitGroup :=
  -- Routed through `IsUnit` rather than through `Valuation.mem_unitGroup_iff`, which would ask
  -- unification to see `P.integers` as `P.valuation.valuationSubring`: `Place.integers` is not
  -- an exposed definition, so that unfolding is unavailable here and the attempt exhausts the
  -- heartbeat budget at `whnf`. Both lemmas used below are generic in the valuation subring.
  (ValuationSubring.mem_unitGroup_iff _ f).2 <|
    (ValuationSubring.valuation_eq_one_iff _ _).1
      ((P.isUnit_iff_ord_eq_zero (x := ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩)
        (Units.ne_zero f)).2 hf)

/-- **The residue `f(P)` of a function that is a unit at `P`**, as a unit of the residue field.
Being a unit is what makes the residue nonzero, which is what lets it be raised to a negative
power in `TauCeti.Divisor.eval`.

This is Mathlib's `ValuationSubring.unitGroupToResidueFieldUnits` at the unit-group element `f`
names, rather than a residue paired with a separate proof that it is nonzero. -/
-- Being the image of a `MonoidHom` is what makes the group laws below `map_one`, `map_mul` and
-- `map_inv`, and the `normResidue` ones those composed with `Algebra.normUnits`, itself a
-- `MonoidHom`.
noncomputable def residueUnit (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    P.ResidueFieldˣ :=
  P.integers.unitGroupToResidueFieldUnits ⟨f, P.mem_unitGroup_of_ord_eq_zero hf⟩

/-- The residue field element underlying `residueUnit`: the residue of `f` in `𝒪_P / 𝔪_P`. -/
@[simp]
theorem coe_residueUnit (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    (P.residueUnit f hf : P.ResidueField)
      = IsLocalRing.residue P.integers ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩ := by
  rw [residueUnit, ValuationSubring.coe_unitGroupToResidueFieldUnits_apply]
  rfl

/-- **The norm to `k` of the residue of a function that is a unit at `P`.** The residue field
varies with `P`; the norm is what puts the value in `k`, the one field all the local factors of
`TauCeti.Divisor.eval` have to share.

This is the classical field norm precisely when `Module.Finite k P.ResidueField` — which
`TauCeti.Place.finiteDimensional_residueField` supplies for every place of a function field.
Absent that, `Algebra.norm` is the junk value `1`
(`Algebra.norm_eq_one_of_not_module_finite`), exactly as `TauCeti.Place.degree` is junk `0`
absent the same hypothesis. -/
-- Finiteness is documented rather than assumed: `Algebra.normUnits` consumes no such argument, so
-- a hypothesis here would be unused, which `unusedArguments` rejects. `TauCeti.Place.degree`
-- records the same convention for `Module.finrank`.
noncomputable def normResidue (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) : kˣ :=
  Algebra.normUnits k (P.residueUnit f hf)

/-- The element of `k` underlying `normResidue`: the norm of the residue. -/
@[simp]
theorem coe_normResidue (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    (P.normResidue f hf : k) = Algebra.norm k (P.residueUnit f hf : P.ResidueField) := by
  simp [normResidue]

/-- `normResidue` extended by `1` where `f` is not a unit, making it a total function of the
place. `1` is the only workable neutral value: the coefficient of a place in a divisor is an
*integer*, so the local factor is raised to a possibly negative power, and only a value in `kˣ`
survives that. -/
noncomputable def normResidueOrOne (P : Place k F) (f : Fˣ) : kˣ :=
  if hf : P.ord (f : F) = 0 then P.normResidue f hf else 1

/-- Where `f` is a unit at `P`, the total local factor is the genuine norm of the residue. -/
@[simp]
theorem normResidueOrOne_of_ord_eq_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.normResidueOrOne f = P.normResidue f hf := by
  simp [normResidueOrOne, hf]

/-- Where `f` is not a unit at `P`, the total local factor is the neutral value `1`. -/
@[simp]
theorem normResidueOrOne_of_ord_ne_zero {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) ≠ 0) :
    P.normResidueOrOne f = 1 := by
  simp [normResidueOrOne, hf]

/-- **The residue is multiplicative in the function**, at a place where both factors are units:
`(f g)(P) = f(P) · g(P)`. -/
theorem residueUnit_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) (hfg : P.ord ((f * g : Fˣ) : F) = 0) :
    P.residueUnit (f * g) hfg = P.residueUnit f hf * P.residueUnit g hg := by
  rw [residueUnit, residueUnit, residueUnit, ← map_mul]
  rfl

/-- **The norm of the residue is multiplicative in the function**, at a place where both factors
are units. -/
theorem normResidue_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) (hfg : P.ord ((f * g : Fˣ) : F) = 0) :
    P.normResidue (f * g) hfg = P.normResidue f hf * P.normResidue g hg := by
  rw [normResidue, normResidue, normResidue, residueUnit_mul hf hg hfg, map_mul]

/-- **The residue of the constant `1` is `1`.** -/
@[simp]
theorem residueUnit_one (P : Place k F) (hf : P.ord ((1 : Fˣ) : F) = 0) :
    P.residueUnit 1 hf = 1 := by
  rw [residueUnit, ← map_one P.integers.unitGroupToResidueFieldUnits]
  rfl

/-- **The residue inverts with the function**: `f⁻¹(P) = f(P)⁻¹`. -/
theorem residueUnit_inv {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0)
    (hfinv : P.ord ((f⁻¹ : Fˣ) : F) = 0) :
    P.residueUnit f⁻¹ hfinv = (P.residueUnit f hf)⁻¹ := by
  rw [residueUnit, residueUnit, ← map_inv]
  rfl

/-- **The norm of the residue inverts with the function**: `N(f⁻¹(P)) = N(f(P))⁻¹`. -/
theorem normResidue_inv {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0)
    (hfinv : P.ord ((f⁻¹ : Fˣ) : F) = 0) :
    P.normResidue f⁻¹ hfinv = (P.normResidue f hf)⁻¹ := by
  rw [normResidue, normResidue, residueUnit_inv hf hfinv, map_inv]

/-- **The total local factor is multiplicative in the function**, at a place where both factors
are units. The hypotheses cannot be dropped: at a place where `f` and `g` have opposite nonzero
orders, `f * g` is a unit while neither factor is, so the left side is a genuine norm and the
right side is `1`. -/
theorem normResidueOrOne_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.normResidueOrOne (f * g) = P.normResidueOrOne f * P.normResidueOrOne g := by
  have hfg : P.ord ((f * g : Fˣ) : F) = 0 := by
    rw [Units.val_mul, P.ord_mul (Units.ne_zero f) (Units.ne_zero g), hf, hg, add_zero]
  rw [normResidueOrOne_of_ord_eq_zero hfg, normResidueOrOne_of_ord_eq_zero hf,
    normResidueOrOne_of_ord_eq_zero hg, normResidue_mul hf hg hfg]

-- Not `@[simp]`: since `normResidueOrOne_of_ord_eq_zero` is `@[simp]` and `simp` can discharge
-- `ord_P 1 = 0` on its own, the total form is rewritten to `normResidue` before this could fire.
-- `normResidue_one` below is the `@[simp]` rule for that normal form.
/-- The constant `1` has local factor `1`. -/
theorem normResidueOrOne_one (P : Place k F) : P.normResidueOrOne (1 : Fˣ) = 1 := by
  -- read off multiplicativity at `f = g = 1` rather than from the residue: `a = a * a` in a
  -- group forces `a = 1`, which avoids all of the subtype-coercion work
  have h1 : P.ord ((1 : Fˣ) : F) = 0 := by simp
  have h := normResidueOrOne_mul (P := P) (f := 1) (g := 1) h1 h1
  rw [one_mul] at h
  exact right_eq_mul.1 h

/-- The residue of the constant `1` has norm `1`. -/
@[simp]
theorem normResidue_one (P : Place k F) (hf : P.ord ((1 : Fˣ) : F) = 0) :
    P.normResidue 1 hf = 1 := by
  rw [← normResidueOrOne_of_ord_eq_zero hf, normResidueOrOne_one]

/-- **Inversion needs no admissibility hypothesis.** `ord_P f⁻¹ = -ord_P f` vanishes exactly when
`ord_P f` does, so the two places of `normResidueOrOne`'s case split correspond under inversion
and both branches invert. Contrast `normResidueOrOne_mul`, where the hypotheses cannot be
dropped: a product can leave the subgroup `{ord_P = 0}` open on neither factor. -/
@[simp]
theorem normResidueOrOne_inv (P : Place k F) (f : Fˣ) :
    P.normResidueOrOne f⁻¹ = (P.normResidueOrOne f)⁻¹ := by
  by_cases hf : P.ord (f : F) = 0
  · refine eq_inv_of_mul_eq_one_left ?_
    have hfinv : P.ord ((f⁻¹ : Fˣ) : F) = 0 := by
      rw [Units.val_inv_eq_inv_val, P.ord_inv, hf, neg_zero]
    rw [← normResidueOrOne_mul hfinv hf, inv_mul_cancel, normResidueOrOne_one]
  · have hfinv : P.ord ((f⁻¹ : Fˣ) : F) ≠ 0 := by
      rw [Units.val_inv_eq_inv_val, P.ord_inv]
      simpa using hf
    rw [normResidueOrOne_of_ord_ne_zero hfinv, normResidueOrOne_of_ord_ne_zero hf, inv_one]

end TauCeti.Place
