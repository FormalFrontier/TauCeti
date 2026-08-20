/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.ConvexSubgroup

/-!
# Coarsening a valuation by a convex subgroup

Collapsing a convex subgroup `H` of the value units of `Γ₀` coarsens any `Γ₀`-valued
valuation: values are pushed along `Γ₀ ≃ WithZero Γ₀ˣ → WithZero (Γ₀ˣ ⧸ H)`, which is
monotone precisely because `H` is convex. The support is unchanged, bounds by `1` survive,
and a value that is at most `1` whose unit avoids `H` lands strictly below `1` — the three
facts the height-one generization of Wedhorn's Lemma 7.45 consumes.

## Main definitions

* `TauCeti.coarsenMapOfValueGroup` : the monoid-with-zero map
  `Γ₀ → WithZero (Γ₀ˣ ⧸ H.toSubgroup)`.
* `Valuation.coarsenByUnits` : the coarsened valuation.

## Main results

* `Valuation.coarsenByUnits_supp` : coarsening preserves the support.
* `Valuation.coarsenByUnits_lt_one_of_notMem` : the collapse detects non-membership — a value
  at most `1` whose unit avoids `H` drops strictly below `1`. (Bounds by `1` come from
  `coarsenMapOfValueGroup_monotone` directly; no specialization is exported for them.)

## Provenance

Adapted from AINTLIB (see References), `projects/AdicSpaces/Adic spaces/ValuationCoarsening.lean`:
the constructions and statements are that file's, with its local `WithZero.mapMonoidWithZeroHom`
block replaced by Mathlib's `WithZero.map'` and the composite shaped as in Mathlib's own
`LinearOrderedCommGroupWithZero` locally-finite instance.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), around Lemma 7.45.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/ValuationCoarsening.lean`.
-/

namespace TauCeti

public section

open TauCeti.ConvexSubgroup

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

open Classical in
/-- The coarsening map `Γ₀ → WithZero (Γ₀ˣ ⧸ H.toSubgroup)`: identify `Γ₀` with
`WithZero Γ₀ˣ` and collapse `H`. -/
noncomputable def coarsenMapOfValueGroup (H : ConvexSubgroup Γ₀ˣ) :
    Γ₀ →*₀ WithZero (Γ₀ˣ ⧸ H.toSubgroup) :=
  (WithZero.map' (QuotientGroup.mk' H.toSubgroup)).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom

open Classical in
/-- The coarsening map is monotone; convexity of `H` is what orders the quotient. -/
theorem coarsenMapOfValueGroup_monotone (H : ConvexSubgroup Γ₀ˣ) :
    Monotone (coarsenMapOfValueGroup H) :=
  (WithZero.map'_mono H.quotientMk_monotone).comp
    (OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toOrderIso.monotone

open Classical in
/-- The coarsening map sends the value of a unit to its class. -/
@[simp]
theorem coarsenMapOfValueGroup_apply_coe (H : ConvexSubgroup Γ₀ˣ) (g : Γ₀ˣ) :
    coarsenMapOfValueGroup H (g : Γ₀) = (QuotientGroup.mk' H.toSubgroup g :) := by
  have h : ((OrderMonoidIso.withZeroUnits (α := Γ₀)).symm.toMonoidWithZeroHom (g : Γ₀))
      = (g : WithZero Γ₀ˣ) := WithZero.withZeroUnitsEquiv_symm_apply_coe g
  rw [coarsenMapOfValueGroup, MonoidWithZeroHom.comp_apply, h, WithZero.map'_coe]

end

end TauCeti

namespace Valuation

public section

open TauCeti

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening a valuation by a convex subgroup of the units of its value monoid. -/
noncomputable def coarsenByUnits (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    Valuation R (WithZero (Γ₀ˣ ⧸ H.toSubgroup)) :=
  v.map (coarsenMapOfValueGroup H) (coarsenMapOfValueGroup_monotone H)

/-- Coarsening applies the coarsening map to each value. -/
@[simp]
theorem coarsenByUnits_apply (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) (r : R) :
    v.coarsenByUnits H r = coarsenMapOfValueGroup H (v r) :=
  Valuation.map_apply _ _ _ _

/-- A value at most `1` whose unit avoids `H` lands strictly below `1` after coarsening. -/
theorem coarsenByUnits_lt_one_of_notMem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {a : R} (ha_ne : v a ≠ 0) (ha_le : v a ≤ 1)
    (hm : Units.mk0 (v a) ha_ne ∉ H) : v.coarsenByUnits H a < 1 := by
  have hle : Units.mk0 (v a) ha_ne ≤ 1 := by
    rw [← Units.val_le_val, Units.val_mk0, Units.val_one]
    exact ha_le
  rw [coarsenByUnits_apply, ← Units.val_mk0 ha_ne, coarsenMapOfValueGroup_apply_coe]
  exact_mod_cast H.quotientMk_lt_one_of_notMem hle hm

section Supp

-- `Valuation.supp` is defined only over a commutative ring, so this one statement asks for
-- more than the rest of the file; the construction above needs no commutativity.
variable {S : Type*} [CommRing S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Coarsening preserves the support. -/
theorem coarsenByUnits_supp (v : Valuation S Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    (v.coarsenByUnits H).supp = v.supp := by
  -- the coarsening map is a `→*₀` out of a `GroupWithZero`, so Mathlib's `map_eq_zero` already
  -- says it kills no nonzero value; nothing about the construction has to be reopened
  ext r
  simp only [mem_supp_iff, coarsenByUnits_apply, map_eq_zero]

end Supp

end

end Valuation
