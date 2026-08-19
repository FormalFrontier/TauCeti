/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Algebra.Order.Group.ConvexSubgroup

/-!
# Restricting a valuation to a convex subgroup

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

Given a valuation `v` and a convex subgroup `H` of the units of its value monoid, the
**restriction of `v` to `H`** keeps those values whose unit lies in `H` and sends every other
value to `0`. It is the construction underlying the retraction `r_I : Spv A → Spv (A, I)`.

That this is again a valuation is not formal: multiplicativity fails for an arbitrary subgroup,
because two units outside `H` can have a product inside it. Convexity of `H` together with the
hypothesis that `H` absorbs every attained value `≥ 1` is what rules that out: a unit outside
`H` must lie below `1`, so a product of two such is below each factor.

## Main definitions

* `Valuation.restrictToConvex` : the restricted valuation, with codomain
  `WithZero H.toSubgroup`.

## Main results

* `Valuation.restrictToConvex_apply_of_mem`, `Valuation.restrictToConvex_apply_of_notMem` and
  `Valuation.restrictToConvex_apply_of_eq_zero` : the three branches, which are the intended
  interface — the definition itself is a `dite` chain and is not meant to be unfolded.
* `Valuation.restrictToConvex_eq_zero_iff` : where the restriction vanishes, totally.
* `Valuation.restrictToConvex_le_iff` : how restricted values compare, totally.
* `Valuation.restrictToConvex_lt_coe_iff` and `Valuation.coe_le_restrictToConvex_iff` : a
  restricted value compared against an abstract member of `H`.
* `Valuation.one_le_restrictToConvex` : a value at least `1` stays at least `1`.
* `Valuation.mk0_mem_of_inv_le_of_le` : `H` keeps every value bracketed by an attained value
  `≥ 1` and its inverse — so the characteristic values of `v` all survive the restriction.
(A convex subgroup of a *value group* has to be carried onto the units of the value monoid
before it can be restricted to; that transport ships with the retraction that needs it.)

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2

## Provenance

Ported from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, project `projects/AdicSpaces/`,
file `Adic spaces/ValuationContinuity.lean`, declarations `convexRestrictFun` and
`restrictToConvexBounded`. That development carries
`set_option backward.isDefEq.respectTransparency false` on the definition and several proofs;
TauCeti's CI forbids `set_option`, and it turns out not to be needed — stating the `dite` chain
as `restrictToConvexFun_unfold` and rewriting through it, rather than unfolding the definition in
place, lets the instances be synthesised in the consumer's context.
-/

public section

namespace Valuation

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

open TauCeti

open Classical in
/-- The underlying function of `Valuation.restrictToConvex`: keep a value when its unit lies in
`H`, and send everything else to `0`. -/
private noncomputable def restrictToConvexFun (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (r : R) : WithZero H.toSubgroup :=
  if h : v r = 0 then 0
  else if hm : Units.mk0 (v r) h ∈ H then ((⟨Units.mk0 (v r) h, hm⟩ : H.toSubgroup) : WithZero _)
  else 0

open Classical in
private theorem restrictToConvexFun_unfold (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (r : R) :
    restrictToConvexFun v H r =
      (if h : v r = 0 then (0 : WithZero H.toSubgroup)
       else if hm : Units.mk0 (v r) h ∈ H
            then ((⟨Units.mk0 (v r) h, hm⟩ : H.toSubgroup) : WithZero _)
            else 0) :=
  rfl

/-- If `H` absorbs every attained value `≥ 1`, then a unit outside `H` is below `1`. This is
what makes the restriction multiplicative: it forces both factors below `1`, and convexity then
keeps their product outside `H` too. -/
private theorem lt_one_of_unit_notMem {v : Valuation R Γ₀} {H : ConvexSubgroup Γ₀ˣ}
    {r : R} (hr : v r ≠ 0) (hH : 1 ≤ v r → Units.mk0 (v r) hr ∈ H)
    (hm : Units.mk0 (v r) hr ∉ H) : v r < 1 := by
  by_contra hge
  push Not at hge
  exact hm (hH hge)

/-- The nonzero branch: on a value that does not vanish, the restriction is `0` at `r` exactly
when the unit of `v r` avoids `H`. -/
private theorem restrictToConvexFun_eq_zero_iff (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {r : R} (hr : v r ≠ 0) :
    restrictToConvexFun v H r = 0 ↔ Units.mk0 (v r) hr ∉ H := by
  classical
  rw [restrictToConvexFun_unfold, dite_eq_right hr]
  by_cases hm : Units.mk0 (v r) hr ∈ H
  · simp [hm]
  · simp [hm]

/-- On a value whose unit lies in `H`, the restriction is that unit. -/
private theorem restrictToConvexFun_of_mem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    {r : R} (hr : v r ≠ 0) (hm : Units.mk0 (v r) hr ∈ H) :
    restrictToConvexFun v H r = ((⟨Units.mk0 (v r) hr, hm⟩ : H.toSubgroup) : WithZero _) := by
  classical
  rw [restrictToConvexFun_unfold, dite_eq_right hr, dite_eq_left hm]

/-- Units outside `H` are absorbing for the product, given that `H` takes every attained value
`≥ 1`. Two units outside a general subgroup can multiply back into it; convexity is what rules
that out here. -/
private theorem mul_notMem_of_notMem {v : Valuation R Γ₀} {H : ConvexSubgroup Γ₀ˣ}
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {x y : R} (hx : v x ≠ 0) (hy : v y ≠ 0) (hm : Units.mk0 (v x) hx ∉ H) :
    Units.mk0 (v x) hx * Units.mk0 (v y) hy ∉ H := by
  by_cases hy' : Units.mk0 (v y) hy ∈ H
  · -- the product and `y`'s unit are both in `H`, so `x`'s unit would be too
    exact fun hmem => hm ((mul_mem_cancel_right hy').mp hmem)
  · -- both units are below `1`, so the product is below `x`'s unit, which `H` already excludes
    have hy1 : Units.mk0 (v y) hy ≤ 1 := by
      have := lt_one_of_unit_notMem hy (fun h => hH y hy h) hy'
      simpa [← Units.val_le_val] using this.le
    have hx1 : Units.mk0 (v x) hx < 1 := by
      have := lt_one_of_unit_notMem hx (fun h => hH x hx h) hm
      simpa [← Units.val_lt_val] using this
    exact H.not_mem_of_not_mem_of_le_lt_one hm hx1
      (mul_le_of_le_one_right' (a := Units.mk0 (v x) hx) hy1)

/-- `H` is closed upwards along attained values: a member below an attained unit forces that
unit in too, whether it sits below `1` (by convexity) or above (by hypothesis). -/
private theorem mem_of_mem_of_le {v : Valuation R Γ₀} {H : ConvexSubgroup Γ₀ˣ}
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {x : R} (hx : v x ≠ 0) {u : Γ₀ˣ} (hu : u ∈ H) (hle : u ≤ Units.mk0 (v x) hx) :
    Units.mk0 (v x) hx ∈ H := by
  rcases le_or_gt (Units.mk0 (v x) hx) 1 with h1 | h1
  · exact ConvexSubgroup.mem_of_le_le_one hu hle h1
  · exact hH x hx (by simpa using Units.val_le_val.mpr h1.le)

private theorem restrictToConvexFun_map_zero (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    restrictToConvexFun v H 0 = 0 := by
  classical
  rw [restrictToConvexFun_unfold, dite_eq_left (by simp)]

private theorem restrictToConvexFun_map_one (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ) :
    restrictToConvexFun v H 1 = 1 := by
  classical
  have h1 : v 1 ≠ 0 := by simp
  have hunit : Units.mk0 (v 1) h1 = 1 := by ext; simp
  have hm : Units.mk0 (v 1) h1 ∈ H := hunit ▸ one_mem H
  rw [restrictToConvexFun_of_mem v H h1 hm]
  norm_cast
  ext
  simp

private theorem restrictToConvexFun_map_mul (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) (x y : R) :
    restrictToConvexFun v H (x * y)
      = restrictToConvexFun v H x * restrictToConvexFun v H y := by
  classical
  by_cases hx : v x = 0
  · rw [restrictToConvexFun_unfold v H (x * y), dite_eq_left (by simp [hx]),
      restrictToConvexFun_unfold v H x, dite_eq_left hx, zero_mul]
  by_cases hy : v y = 0
  · rw [restrictToConvexFun_unfold v H (x * y), dite_eq_left (by simp [hy]),
      restrictToConvexFun_unfold v H y, dite_eq_left hy, mul_zero]
  have hxy : v (x * y) ≠ 0 := by simp [hx, hy]
  have hfac : Units.mk0 (v (x * y)) hxy = Units.mk0 (v x) hx * Units.mk0 (v y) hy := by
    ext; simp
  by_cases hmx : Units.mk0 (v x) hx ∈ H
  · by_cases hmy : Units.mk0 (v y) hy ∈ H
    · have hmxy : Units.mk0 (v (x * y)) hxy ∈ H := by rw [hfac]; exact mul_mem hmx hmy
      rw [restrictToConvexFun_of_mem v H hxy hmxy, restrictToConvexFun_of_mem v H hx hmx,
        restrictToConvexFun_of_mem v H hy hmy, ← WithZero.coe_mul, WithZero.coe_inj]
      ext
      simp
    · have hmxy : Units.mk0 (v (x * y)) hxy ∉ H := by
        rw [hfac, mul_comm]; exact mul_notMem_of_notMem hH hy hx hmy
      rw [(restrictToConvexFun_eq_zero_iff v H hxy).mpr hmxy,
        (restrictToConvexFun_eq_zero_iff v H hy).mpr hmy, mul_zero]
  · have hmxy : Units.mk0 (v (x * y)) hxy ∉ H := by
      rw [hfac]; exact mul_notMem_of_notMem hH hx hy hmx
    rw [(restrictToConvexFun_eq_zero_iff v H hxy).mpr hmxy,
      (restrictToConvexFun_eq_zero_iff v H hx).mpr hmx, zero_mul]

/-- The dominating side of `v (x + y) ≤ max (v x) (v y)` bounds the restriction. Stated for one
side so that `map_add_le_max` can apply it to whichever side achieves the maximum. -/
private theorem restrictToConvexFun_le_of_le (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {z x : R} (hz : v z ≠ 0) (hmz : Units.mk0 (v z) hz ∈ H) (hle : v z ≤ v x) :
    restrictToConvexFun v H z ≤ restrictToConvexFun v H x := by
  classical
  have hx : v x ≠ 0 := fun h0 => hz (le_antisymm (h0 ▸ hle) (zero_le))
  have hu : Units.mk0 (v z) hz ≤ Units.mk0 (v x) hx := by
    simpa [← Units.val_le_val] using hle
  have hmx : Units.mk0 (v x) hx ∈ H := mem_of_mem_of_le hH hx hmz hu
  rw [restrictToConvexFun_of_mem v H hz hmz, restrictToConvexFun_of_mem v H hx hmx,
    WithZero.coe_le_coe]
  exact hu

private theorem restrictToConvexFun_map_add_le_max (v : Valuation R Γ₀)
    (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) (x y : R) :
    restrictToConvexFun v H (x + y)
      ≤ max (restrictToConvexFun v H x) (restrictToConvexFun v H y) := by
  classical
  by_cases hxy : v (x + y) = 0
  · rw [restrictToConvexFun_unfold v H (x + y), dite_eq_left hxy]
    exact zero_le
  by_cases hmxy : Units.mk0 (v (x + y)) hxy ∈ H
  · rcases le_total (v y) (v x) with h | h
    · exact le_trans
        (restrictToConvexFun_le_of_le v H hH hxy hmxy
          ((v.map_add_le_max' x y).trans (max_le le_rfl h)))
        (le_max_left _ _)
    · exact le_trans
        (restrictToConvexFun_le_of_le v H hH hxy hmxy
          ((v.map_add_le_max' x y).trans (max_le h le_rfl)))
        (le_max_right _ _)
  · rw [(restrictToConvexFun_eq_zero_iff v H hxy).mpr hmxy]
    exact zero_le

/-- **The restriction of `v` to a convex subgroup `H` of its value units.** Values whose unit
lies in `H` are kept; every other value is sent to `0`.

The hypothesis says that `H` absorbs each attained value `≥ 1`. It cannot be dropped: without it
the result is not multiplicative, since two units outside `H` may have a product inside it. -/
noncomputable def restrictToConvex (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) :
    Valuation R (WithZero H.toSubgroup) where
  toFun := restrictToConvexFun v H
  map_zero' := restrictToConvexFun_map_zero v H
  map_one' := restrictToConvexFun_map_one v H
  map_mul' := restrictToConvexFun_map_mul v H hH
  map_add_le_max' := restrictToConvexFun_map_add_le_max v H hH

/-- On a value whose unit lies in `H`, the restriction keeps that unit. -/
-- Deliberately not `@[simp]`, unlike its three siblings: its right-hand side is a coercion of a
-- subtype element, which is not a normal form. Tagging it rewrites `v.restrictToConvex H hH 1`
-- to `↑⟨1, _⟩` instead of to `1`, which breaks `one_le_restrictToConvex` below.
theorem restrictToConvex_apply_of_mem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r ≠ 0) (hm : Units.mk0 (v r) hr ∈ H) :
    v.restrictToConvex H hH r = ((⟨Units.mk0 (v r) hr, hm⟩ : H.toSubgroup) : WithZero _) :=
  restrictToConvexFun_of_mem v H hr hm

/-- Off `H`, the restriction vanishes. -/
@[simp]
theorem restrictToConvex_apply_of_notMem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r ≠ 0) (hm : Units.mk0 (v r) hr ∉ H) :
    v.restrictToConvex H hH r = 0 :=
  (restrictToConvexFun_eq_zero_iff v H hr).mpr hm

/-- The restriction vanishes wherever `v` does. -/
@[simp]
theorem restrictToConvex_apply_of_eq_zero (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r = 0) : v.restrictToConvex H hH r = 0 := by
  classical
  exact (restrictToConvexFun_unfold v H r).trans (dite_eq_left hr)

/-- On values whose units lie in `H`, the restriction both preserves and reflects the order.
This is what lets an order fact about `v` be moved to the restricted valuation without
unfolding either.

Not `@[simp]`: `restrictToConvex_le_iff` is the simp-normal form for a comparison of restricted
values, and it rewrites this lemma's left-hand side, which `simpNF` rejects. -/
theorem restrictToConvex_le_iff_of_mem (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r s : R} (hr : v r ≠ 0) (hs : v s ≠ 0)
    (hmr : Units.mk0 (v r) hr ∈ H) (hms : Units.mk0 (v s) hs ∈ H) :
    v.restrictToConvex H hH r ≤ v.restrictToConvex H hH s ↔ v r ≤ v s := by
  rw [restrictToConvex_apply_of_mem v H hH hr hmr, restrictToConvex_apply_of_mem v H hH hs hms,
    WithZero.coe_le_coe]
  simp [← Units.val_le_val]

/-- **Comparison after restriction, totally.** A discarded value sits at the bottom, so it is
below everything; a kept value is below only kept values; and two kept values compare exactly
as they did under `v`. `restrictToConvex_le_iff_of_mem` is the both-kept branch, in the form
consumers holding membership hypotheses want.

The side conditions are stated as vanishing of the restriction rather than as membership in `H`,
so that `restrictToConvex_eq_zero_iff` discharges them without the caller naming `H`. -/
@[simp]
theorem restrictToConvex_le_iff (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) (r s : R) :
    v.restrictToConvex H hH r ≤ v.restrictToConvex H hH s ↔
      v.restrictToConvex H hH r = 0 ∨ v.restrictToConvex H hH s ≠ 0 ∧ v r ≤ v s := by
  by_cases hx : v.restrictToConvex H hH r = 0
  · simp [hx]
  by_cases hy : v.restrictToConvex H hH s = 0
  · simp [hx, hy]
  have hr : v r ≠ 0 := fun h0 ↦ hx (restrictToConvex_apply_of_eq_zero v H hH h0)
  have hs : v s ≠ 0 := fun h0 ↦ hy (restrictToConvex_apply_of_eq_zero v H hH h0)
  have hmr : Units.mk0 (v r) hr ∈ H := by
    by_contra hm; exact hx (restrictToConvex_apply_of_notMem v H hH hr hm)
  have hms : Units.mk0 (v s) hs ∈ H := by
    by_contra hm; exact hy (restrictToConvex_apply_of_notMem v H hH hs hm)
  simp [hx, hy, restrictToConvex_le_iff_of_mem v H hH hr hs hmr hms]

/-- A value at least `1` stays at least `1` under the restriction. Such a value is always kept,
since `H` absorbs the attained values `≥ 1` by hypothesis. -/
theorem one_le_restrictToConvex (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {c : R} (h1 : 1 ≤ v c) : 1 ≤ v.restrictToConvex H hH c := by
  have hc : v c ≠ 0 := (zero_lt_one.trans_le h1).ne'
  have hone : v (1 : R) ≠ 0 := by simp
  have hmone : Units.mk0 (v (1 : R)) hone ∈ H := by
    have h : Units.mk0 (v (1 : R)) hone = 1 := by ext; simp
    rw [h]; exact one_mem H
  have := (restrictToConvex_le_iff_of_mem v H hH hone hc hmone (hH c hc h1)).mpr (by simpa using h1)
  simpa using this

/-- `H` keeps every value sandwiched between an attained value `≥ 1` and its inverse. Since
`H` absorbs the attained values `≥ 1`, and is convex, it absorbs everything they bracket —
which is exactly the characteristic values of `v`. -/
theorem mk0_mem_of_inv_le_of_le (v : Valuation R Γ₀) {H : ConvexSubgroup Γ₀ˣ}
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {b c : R} (hb : v b ≠ 0) (h1 : 1 ≤ v c)
    (hlo : (v c)⁻¹ ≤ v b) (hhi : v b ≤ v c) : Units.mk0 (v b) hb ∈ H := by
  have hc : v c ≠ 0 := (zero_lt_one.trans_le h1).ne'
  have hmc : Units.mk0 (v c) hc ∈ H := hH c hc h1
  refine H.convex (inv_mem hmc) hmc ?_ ?_
  · simpa [← Units.val_le_val] using hlo
  · simpa [← Units.val_le_val] using hhi

/-- The restriction vanishes at a nonzero value exactly when its unit avoids `H`.

Not `@[simp]`: `restrictToConvex_eq_zero_iff` is the simp-normal form for a vanishing
restriction, and tagging this branch too would make normalisation depend on whether a
nonvanishing proof happens to be available. -/
theorem restrictToConvex_eq_zero_iff_of_ne (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    {r : R} (hr : v r ≠ 0) :
    v.restrictToConvex H hH r = 0 ↔ Units.mk0 (v r) hr ∉ H :=
  restrictToConvexFun_eq_zero_iff v H hr

/-- Comparing a restricted value against an arbitrary element of `H`, back in `Γ₀`.

Unlike `restrictToConvex_le_iff`, which relates two restricted values, this compares a
restricted value with an abstract member of `H` — the form a cofinality argument needs, where
the bound comes from the value group rather than from a ring element.

The discarded branch is the interesting one: a unit outside `H` lies below `1`, and convexity
then puts it strictly below *every* member of `H`, since otherwise `H` would have to contain
it. -/
theorem restrictToConvex_lt_coe_iff (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    (r : R) (u : H.toSubgroup) :
    v.restrictToConvex H hH r < (u : WithZero H.toSubgroup) ↔ v r < ((u : Γ₀ˣ) : Γ₀) := by
  by_cases hr : v r = 0
  · rw [restrictToConvex_apply_of_eq_zero v H hH hr, hr]
    simp [Units.ne_zero, pos_iff_ne_zero]
  · by_cases hmem : Units.mk0 (v r) hr ∈ H
    · rw [restrictToConvex_apply_of_mem v H hH hr hmem, WithZero.coe_lt_coe,
        ← Subtype.coe_lt_coe, ← Units.val_lt_val]
      simp
    · rw [restrictToConvex_apply_of_notMem v H hH hr hmem]
      have hlt1 : v r < 1 := lt_one_of_unit_notMem hr (fun h => hH r hr h) hmem
      have hu1 : Units.mk0 (v r) hr ≤ 1 := by simpa [← Units.val_le_val] using hlt1.le
      have hlt : Units.mk0 (v r) hr < (u : Γ₀ˣ) :=
        not_le.mp fun h => hmem (ConvexSubgroup.mem_of_le_le_one u.2 h hu1)
      simp only [pos_iff_ne_zero, ne_eq, WithZero.coe_ne_zero, not_false_eq_true, true_iff]
      simpa [← Units.val_lt_val] using hlt

/-- The companion of `restrictToConvex_lt_coe_iff` with the member of `H` on the left.

Both discarded branches work the same way: a value the restriction throws away sits strictly
below every member of `H`, so no member of `H` is below it. -/
theorem coe_le_restrictToConvex_iff (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H)
    (r : R) (u : H.toSubgroup) :
    (u : WithZero H.toSubgroup) ≤ v.restrictToConvex H hH r ↔ ((u : Γ₀ˣ) : Γ₀) ≤ v r := by
  rw [← not_lt, ← not_lt, not_iff_not]
  exact restrictToConvex_lt_coe_iff v H hH r u

/-- **Where the restriction vanishes, totally**: at the zeros of `v`, and where `v` is nonzero
but its unit avoids `H`. `restrictToConvex_eq_zero_iff_of_ne` is the nonzero branch, in the form
consumers holding a nonvanishing hypothesis want. -/
@[simp]
theorem restrictToConvex_eq_zero_iff (v : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH : ∀ a : R, ∀ ha : v a ≠ 0, 1 ≤ v a → Units.mk0 (v a) ha ∈ H) (r : R) :
    v.restrictToConvex H hH r = 0 ↔ v r = 0 ∨ ∃ hr : v r ≠ 0, Units.mk0 (v r) hr ∉ H := by
  by_cases hr : v r = 0
  · simp [restrictToConvex_apply_of_eq_zero v H hH hr, hr]
  · rw [restrictToConvex_eq_zero_iff_of_ne v H hH hr]
    simp only [hr, false_or]
    exact ⟨fun h ↦ ⟨hr, h⟩, fun ⟨_, h⟩ ↦ h⟩

end Valuation

