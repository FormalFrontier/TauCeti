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
* `TauCeti.Place.ord_mul_eq_zero`, `ord_inv_eq_zero` and `ord_div_eq_zero`
  (in `Place/Basic.lean`): admissibility is a subgroup condition on `Fˣ`. They are public because
  `residueUnit` carries its admissibility proof as an argument, so a law about `f * g`, `f⁻¹` or
  `f / g` has to name a proof for the *composite* in its own left-hand side; these are those
  names. The identity case needs no such lemma — `((1 : Fˣ) : F)` is `1` definitionally, so
  `TauCeti.Place.ord_one` already has the right type.
* The group laws in the function: `residueUnit_one`, `residueUnit_mul`, `residueUnit_inv`,
  `residueUnit_div` and their `normResidue` counterparts, together with `normResidueOrOne_one`,
  `normResidueOrOne_mul`, `normResidueOrOne_inv` and `normResidueOrOne_div` for the total form.
  Each partial law assumes only what its *inputs* need — `residueUnit_one` and `normResidue_one`
  assume nothing at all — and derives the composite's order itself. The total form is asymmetric:
  `normResidueOrOne_mul` and `normResidueOrOne_div` need both arguments admissible, while
  `normResidueOrOne_inv` needs nothing, since `ord_P f⁻¹ = -ord_P f` vanishes exactly when
  `ord_P f` does.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 — the local factors
  of the divisor evaluation used there to construct the Weil pairing.
-/

public section

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- A function of order zero at `P` lies in the unit group of `𝒪_P`: order zero is valuation one,
which is exactly `ValuationSubring.mem_unitGroup_iff`. -/
private theorem mem_unitGroup_of_ord_eq_zero (P : Place k F) {f : Fˣ} (hf : P.ord (f : F) = 0) :
    f ∈ P.integers.unitGroup :=
  -- Routed through `IsUnit` rather than through `Valuation.mem_unitGroup_iff`, which would ask
  -- unification to see `P.integers` as `P.valuation.valuationSubring`: `Place.integers` is not
  -- an exposed definition, so that unfolding is unavailable here and the attempt exhausts the
  -- heartbeat budget at `whnf`. Both lemmas used below are generic in the valuation subring.
  (ValuationSubring.mem_unitGroup_iff _ f).2 <|
    (ValuationSubring.valuation_eq_one_iff _ _).1
      ((P.isUnit_iff_ord_eq_zero (x := ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩)
        (Units.ne_zero f)).2 hf)

/-- The element of `𝒪_P`'s unit group named by a unit of order zero.

This is the **only** place the subtype representation of `ValuationSubring.unitGroup` is used.
That group is a subgroup of `Fˣ`, so its operations are computed on values, and the four laws
below — product, identity, inverse, integer power — are therefore `rfl`. Every group law for
`residueUnit` and `normResidue` is one of them pushed through a `MonoidHom`, or, in the case of
the quotient laws, a product and an inverse composed. -/
private def unitGroupMk (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    P.integers.unitGroup :=
  ⟨f, P.mem_unitGroup_of_ord_eq_zero hf⟩

private theorem coe_unitGroupMulEquiv_unitGroupMk (P : Place k F) (f : Fˣ)
    (hf : P.ord (f : F) = 0) :
    ((P.integers.unitGroupMulEquiv (P.unitGroupMk f hf) : P.integersˣ) : P.integers)
      = ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩ := rfl

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
  P.integers.unitGroupToResidueFieldUnits (P.unitGroupMk f hf)

/-- The residue field element underlying `residueUnit`: the residue of `f` in `𝒪_P / 𝔪_P`. -/
@[simp]
theorem coe_residueUnit (P : Place k F) (f : Fˣ) (hf : P.ord (f : F) = 0) :
    (P.residueUnit f hf : P.ResidueField)
      = IsLocalRing.residue P.integers ⟨(f : F), P.mem_integers_iff_ord_nonneg.2 hf.ge⟩ := by
  rw [residueUnit, ValuationSubring.coe_unitGroupToResidueFieldUnits_apply,
    coe_unitGroupMulEquiv_unitGroupMk]
  -- what remains is `IsLocalRing.residue`'s own definition as `Ideal.Quotient.mk` of the maximal
  -- ideal, not a fact about how the unit group is represented.
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

private theorem unitGroupMk_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.unitGroupMk (f * g) (ord_mul_eq_zero hf hg)
      = P.unitGroupMk f hf * P.unitGroupMk g hg := rfl

private theorem unitGroupMk_one (P : Place k F) :
    P.unitGroupMk 1 P.ord_one = 1 := rfl

private theorem unitGroupMk_inv {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.unitGroupMk f⁻¹ (ord_inv_eq_zero hf) = (P.unitGroupMk f hf)⁻¹ := rfl

private theorem unitGroupMk_zpow {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) (n : ℤ) :
    P.unitGroupMk (f ^ n) (ord_zpow_eq_zero hf n) = P.unitGroupMk f hf ^ n := rfl

/-- **The residue is multiplicative in the function**, at a place where both factors are units:
`(f g)(P) = f(P) · g(P)`. -/
@[simp]
theorem residueUnit_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.residueUnit (f * g) (ord_mul_eq_zero hf hg) =
      P.residueUnit f hf * P.residueUnit g hg := by
  rw [residueUnit, residueUnit, residueUnit, ← map_mul, unitGroupMk_mul hf hg]

/-- **The norm of the residue is multiplicative in the function**, at a place where both factors
are units. -/
@[simp]
theorem normResidue_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.normResidue (f * g) (ord_mul_eq_zero hf hg) =
      P.normResidue f hf * P.normResidue g hg := by
  rw [normResidue, normResidue, normResidue, residueUnit_mul hf hg, map_mul]

/-- **The residue of the constant `1` is `1`.** -/
@[simp]
theorem residueUnit_one (P : Place k F) :
    P.residueUnit 1 P.ord_one = 1 := by
  rw [residueUnit, ← map_one P.integers.unitGroupToResidueFieldUnits, unitGroupMk_one]

/-- **The residue inverts with the function**: `f⁻¹(P) = f(P)⁻¹`. -/
@[simp]
theorem residueUnit_inv {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.residueUnit f⁻¹ (ord_inv_eq_zero hf) = (P.residueUnit f hf)⁻¹ := by
  rw [residueUnit, residueUnit, ← map_inv, unitGroupMk_inv hf]

/-- **The residue takes powers with the function**: `(f ^ n)(P) = f(P) ^ n`. -/
@[simp]
theorem residueUnit_zpow {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) (n : ℤ) :
    P.residueUnit (f ^ n) (ord_zpow_eq_zero hf n) = P.residueUnit f hf ^ n := by
  rw [residueUnit, residueUnit, ← map_zpow, unitGroupMk_zpow hf]

/-- **The residue divides with the function**: `(f / g)(P) = f(P) / g(P)`, at a place where both
are units. -/
@[simp]
theorem residueUnit_div {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.residueUnit (f / g) (ord_div_eq_zero hf hg) =
      P.residueUnit f hf / P.residueUnit g hg := by
  -- division is multiplication by an inverse, so this needs no representation lemma of its own
  conv_rhs => rw [div_eq_mul_inv, ← residueUnit_inv hg]
  exact residueUnit_mul hf (ord_inv_eq_zero hg)

/-- **The norm of the residue inverts with the function**: `N(f⁻¹(P)) = N(f(P))⁻¹`. -/
@[simp]
theorem normResidue_inv {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) :
    P.normResidue f⁻¹ (ord_inv_eq_zero hf) = (P.normResidue f hf)⁻¹ := by
  rw [normResidue, normResidue, residueUnit_inv hf, map_inv]

/-- **The norm of the residue divides with the function**: `N((f / g)(P)) = N(f(P)) / N(g(P))`. -/
@[simp]
theorem normResidue_div {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.normResidue (f / g) (ord_div_eq_zero hf hg) =
      P.normResidue f hf / P.normResidue g hg := by
  rw [normResidue, normResidue, normResidue, residueUnit_div hf hg, map_div]

/-- **The norm of the residue takes powers with the function**: `N((f ^ n)(P)) = N(f(P)) ^ n`. -/
@[simp]
theorem normResidue_zpow {P : Place k F} {f : Fˣ} (hf : P.ord (f : F) = 0) (n : ℤ) :
    P.normResidue (f ^ n) (ord_zpow_eq_zero hf n) = P.normResidue f hf ^ n := by
  rw [normResidue, normResidue, residueUnit_zpow hf, map_zpow]

/-- **The total local factor is multiplicative in the function**, at a place where both factors
are units. The hypotheses cannot be dropped: at a place where `f` and `g` have opposite nonzero
orders, `f * g` is a unit while neither factor is, so the left side is a genuine norm and the
right side is `1`. -/
@[simp]
theorem normResidueOrOne_mul {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.normResidueOrOne (f * g) = P.normResidueOrOne f * P.normResidueOrOne g := by
  rw [normResidueOrOne_of_ord_eq_zero (ord_mul_eq_zero hf hg),
    normResidueOrOne_of_ord_eq_zero hf, normResidueOrOne_of_ord_eq_zero hg,
    normResidue_mul hf hg]

/-- The residue of the constant `1` has norm `1`. -/
@[simp]
theorem normResidue_one (P : Place k F) :
    P.normResidue 1 P.ord_one = 1 := by
  rw [normResidue, residueUnit_one, map_one]

-- Not `@[simp]`: since `normResidueOrOne_of_ord_eq_zero` is `@[simp]` and `simp` can discharge
-- `ord_P 1 = 0` on its own, the total form is rewritten to `normResidue` before this could fire.
-- `normResidue_one` above is the `@[simp]` rule for that normal form.
/-- The constant `1` has local factor `1`. -/
theorem normResidueOrOne_one (P : Place k F) : P.normResidueOrOne (1 : Fˣ) = 1 := by
  rw [normResidueOrOne_of_ord_eq_zero P.ord_one, normResidue_one]

/-- **Inversion needs no admissibility hypothesis.** `ord_P f⁻¹ = -ord_P f` vanishes exactly when
`ord_P f` does, so the two places of `normResidueOrOne`'s case split correspond under inversion
and both branches invert. Contrast `normResidueOrOne_mul`, where the hypotheses cannot be
dropped: a product can leave the subgroup `{ord_P = 0}` open on neither factor. -/
@[simp]
theorem normResidueOrOne_inv (P : Place k F) (f : Fˣ) :
    P.normResidueOrOne f⁻¹ = (P.normResidueOrOne f)⁻¹ := by
  by_cases hf : P.ord (f : F) = 0
  · rw [normResidueOrOne_of_ord_eq_zero (ord_inv_eq_zero hf),
      normResidueOrOne_of_ord_eq_zero hf, normResidue_inv hf]
  · have hfinv : P.ord ((f⁻¹ : Fˣ) : F) ≠ 0 :=
      fun h ↦ hf (by simpa using ord_inv_eq_zero h)
    rw [normResidueOrOne_of_ord_ne_zero hfinv, normResidueOrOne_of_ord_ne_zero hf, inv_one]

/-- **Powers need no admissibility hypothesis**, for the same reason as `normResidueOrOne_inv`:
where `f` is not a unit neither is any nonzero power of it, and both sides are `1`. -/
@[simp]
theorem normResidueOrOne_zpow (P : Place k F) (f : Fˣ) (n : ℤ) :
    P.normResidueOrOne (f ^ n) = P.normResidueOrOne f ^ n := by
  by_cases hf : P.ord (f : F) = 0
  · rw [normResidueOrOne_of_ord_eq_zero (ord_zpow_eq_zero hf n),
      normResidueOrOne_of_ord_eq_zero hf, normResidue_zpow hf]
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h : P.ord ((f ^ n : Fˣ) : F) ≠ 0 := by
        rw [Units.val_zpow_eq_zpow_val, P.ord_zpow]
        exact mul_ne_zero hn hf
      rw [normResidueOrOne_of_ord_ne_zero h, normResidueOrOne_of_ord_ne_zero hf, one_zpow]

/-- **The total local factor divides in the function**, at a place where both arguments are
units. Like `normResidueOrOne_mul`, and unlike `normResidueOrOne_inv`, the hypotheses cannot be
dropped: a quotient can be a unit where neither argument is. -/
@[simp]
theorem normResidueOrOne_div {P : Place k F} {f g : Fˣ} (hf : P.ord (f : F) = 0)
    (hg : P.ord (g : F) = 0) :
    P.normResidueOrOne (f / g) = P.normResidueOrOne f / P.normResidueOrOne g := by
  rw [div_eq_mul_inv, normResidueOrOne_mul hf (ord_inv_eq_zero hg),
    normResidueOrOne_inv, div_eq_mul_inv]

end TauCeti.Place
