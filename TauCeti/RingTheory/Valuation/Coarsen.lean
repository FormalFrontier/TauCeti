/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.Cofinal
public import TauCeti.RingTheory.Valuation.CharacteristicGroup

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
* `Valuation.cofinalValue_coarsenByUnits_restrict` : coarsening by a proper convex subgroup
  preserves cofinality of a value. This needs no topology on `A`.

## Provenance

The coarsening construction itself is adapted from AINTLIB (see References),
`projects/AdicSpaces/Adic spaces/ValuationCoarsening.lean`: `TauCeti.coarsenMapOfValueGroup`,
`Valuation.coarsenByUnits` and the collapse statements about them are that file's, with its local
`WithZero.mapMonoidWithZeroHom` block replaced by Mathlib's `WithZero.map'` and the composite
shaped as in Mathlib's own `LinearOrderedCommGroupWithZero` locally-finite instance.

`Valuation.cofinalValue_coarsenByUnits_restrict` is not from that development. It is the
topology-free cofinality ingredient of Wedhorn's Remark 7.11(2), not the remark itself: the
continuity statement the remark makes is `Valuation.IsContinuous.coarsenByUnits_restrict` in
`TauCeti.RingTheory.Huber.Continuous.Coarsen`, which consumes this one. The order-level step it
rests on is `TauCeti.IsCofinalElement.quotientMk`, which is Wedhorn Corollary 1.21 and already on
hand; nothing about strictness is redone here.

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
@[simp]
theorem coarsenByUnits_supp (v : Valuation S Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    (v.coarsenByUnits H).supp = v.supp := by
  -- the coarsening map is a `→*₀` out of a `GroupWithZero`, so Mathlib's `map_eq_zero` already
  -- says it kills no nonzero value; nothing about the construction has to be reopened
  ext r
  simp only [mem_supp_iff, coarsenByUnits_apply, map_eq_zero]

end Supp

open MonoidWithZeroHom in
/-- **Coarsening by a proper convex subgroup preserves cofinality of a value.** This is the half of
Wedhorn Remark 7.11(2) that properness is needed for: the coarsening map is monotone but not
strictly so, and properness is exactly what supplies the room to recover a strict inequality.

The recovery itself is not redone here. Cofinality of `v a` says that the powers of the unit
`v a` fall below every element of the value group, which is `TauCeti.IsCofinalElement` for that
group; `TauCeti.IsCofinalElement.quotientMk` — Wedhorn Corollary 1.21 — carries that to the
quotient by `H`, and properness is the hypothesis it asks for. What is left is bookkeeping: the
coarsened value monoid embeds in `WithZero (Γˣ ⧸ H)`, so a cofinal element of the *whole*
quotient group is in particular below every value the coarsened valuation attains. -/
theorem cofinalValue_coarsenByUnits_restrict {A : Type*} [Ring A] {v : Valuation A Γ₀}
    {H : ConvexSubgroup (ValueGroup₀ (.ofClass v))ˣ} (hH : H ≠ ⊤) {a : A}
    (hcof : CofinalValue v a) : CofinalValue (v.restrict.coarsenByUnits H) a := by
  rcases eq_or_ne (v.restrict a) 0 with h0 | h0
  · -- a vanishing value stays vanishing, and `0` is below every positive element
    rw [cofinalValue_iff]
    intro γ hγ
    have hz : (v.restrict.coarsenByUnits H).restrict a = 0 := by
      rw [Valuation.restrict_eq_zero_iff, coarsenByUnits_apply, h0, map_zero]
    exact ⟨1, by rwa [pow_one, hz]⟩
  · set g : (ValueGroup₀ (.ofClass v))ˣ := Units.mk0 (v.restrict a) h0 with hgdef
    -- cofinality of the value, read in the value group rather than the value monoid
    have hcofg : TauCeti.IsCofinalElement (⊤ : Subgroup (ValueGroup₀ (.ofClass v))ˣ) g :=
      isCofinalElement_def.mpr fun h _ ↦ by
        obtain ⟨n, hn⟩ := cofinalValue_iff.mp hcof (h : ValueGroup₀ (.ofClass v))
          (zero_lt_iff.mpr h.ne_zero)
        exact ⟨n, by rwa [← Units.val_lt_val, Units.val_pow_eq_pow_val, hgdef, Units.val_mk0]⟩
    have hquot := hcofg.quotientMk hH
    rw [cofinalValue_iff]
    intro γ hγ
    -- a positive element of the coarsened value monoid embeds as the class of some `q`
    have hemb : ValueGroup₀.embedding γ ≠ 0 := by simpa using hγ.ne'
    obtain ⟨q, hq⟩ := WithZero.ne_zero_iff_exists.mp hemb
    obtain ⟨n, hn⟩ := isCofinalElement_def.mp hquot q (Subgroup.mem_top q)
    refine ⟨n, ?_⟩
    rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, ← hq, coarsenByUnits_apply, map_pow,
      ← Units.val_mk0 h0, ← hgdef, ← Units.val_pow_eq_pow_val, coarsenMapOfValueGroup_apply_coe,
      map_pow]
    exact_mod_cast hn

end

end Valuation
