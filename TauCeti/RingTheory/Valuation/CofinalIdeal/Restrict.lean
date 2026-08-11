/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Valuation.CofinalIdeal.Greatest
public import TauCeti.RingTheory.Valuation.RestrictToConvex

/-!
# Restricting a valuation to `cΓ_v(I)`

**Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §7.1.2.**

`Valuation.restrictToConvex` restricts a valuation to an arbitrary convex subgroup of the units
of its value monoid. This file specialises it to the convex subgroup that matters for
`Spv (A, I)`: the characteristic subgroup `cΓ_v(I)` of an ideal, from Wedhorn's Definition 7.3.

Two things have to be arranged. `cΓ_v(I)` lives in the value *group*, so it is transported onto
the units of the value monoid by `ConvexSubgroup.comapUnitsWithZero`; and the restriction needs
`cΓ_v(I)` to absorb every attained value `≥ 1`, which holds because it contains `cΓ_v`.

The point-level map on `Spv A` that Wedhorn's retraction `r_I` is built from lives in
`TauCeti.AlgebraicGeometry.AdicSpace.RestrictToIdeal`.

## Main definitions

* `TauCeti.Valuation.RestrictedValues` : the value monoid the restriction lands in.
* `TauCeti.Valuation.restrictToIdeal` : the restricted valuation `v|cΓ_v(I)`.

## Main results

* `TauCeti.Valuation.restrictToIdeal_apply_of_notMem`,
  `TauCeti.Valuation.restrictToIdeal_apply_of_eq_zero` : the two vanishing branches.
* `TauCeti.Valuation.restrictToIdeal_eq_zero_iff` : where the restriction vanishes, totally.
* `TauCeti.Valuation.restrictToIdeal_le_iff` : how restricted values compare, totally.

The *characterisation* lemmas — the vanishing branches, `restrictToIdeal_eq_zero_iff` and
`restrictToIdeal_le_iff` — are phrased through `cΓ_v(I)` itself or through vanishing of the
restriction, so a consumer of them never names the transport. Two declarations necessarily do
name it: `RestrictedValues`, which *is* the transported subgroup with a zero adjoined, and
`restrictToIdeal_def`, whose content is the definitional unfolding and which therefore carries
the boundedness hypothesis over that subgroup. `one_le_restrictToIdeal` mentions neither, being
an order fact about `v.restrict`.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2

The construction is the one AINTLIB calls `restrictIdeal`
(`aintlib-adic-spaces`, `projects/AdicSpaces/Adic spaces/CharacteristicSubgroup.lean`), built on
`restrictToConvexBounded`. AINTLIB's `cGammaIdeal` is already phrased on `Γ₀ˣ` and so needs no
transport.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The units identification takes the unit of a restricted value to the value-group element it
names. This is the bridge between membership in a transported convex subgroup, which is phrased
through `OrderMonoidIso.unitsWithZero`, and the introduction rules for `cΓ_v(I)`, which are
phrased through `valueGroup.mk`. -/
private theorem unitsWithZeroEquiv_mk0_restrict (v : Valuation A Γ₀) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) (ha : v.restrict a ≠ 0) :
    OrderMonoidIso.unitsWithZero (Units.mk0 (v.restrict a) ha) =
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 := by
  rw [← WithZero.coe_inj, ← v.restrict_eq_mk h0]
  exact WithZero.coe_unitsWithZeroEquiv_eq_units_val _

/-- `cΓ_v(I)`, transported onto the units of the value monoid, absorbs every attained value
`≥ 1`. This is exactly the hypothesis `Valuation.restrictToConvex` needs, and it holds because
`cΓ_v(I)` contains `cΓ_v`, which contains every attained value `≥ 1`. -/
private theorem mk0_restrict_mem_comapUnitsWithZero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (a : A) (ha : v.restrict a ≠ 0) (h1 : 1 ≤ v.restrict a) :
    Units.mk0 (v.restrict a) ha ∈
      ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg) := by
  have h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0 := fun h => ha (v.restrict_eq_zero_iff.mpr h)
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZeroEquiv_mk0_restrict v h0 ha]
  refine characteristicSubgroup_le_characteristicSubgroupOfIdeal v I hfg
    (valueGroup_mk_mem_characteristicSubgroup_of_one_le_value h0 ?_)
  have hr : v.restrict 1 ≤ v.restrict a := by simpa using h1
  simpa using v.restrict_le_iff.mp hr

/-- The value monoid of the restricted valuation: `cΓ_v(I)`, transported onto the units of the
value monoid, with a zero adjoined. -/
-- Named rather than written inline because downstream statements need it as a
-- `LinearOrderedCommGroupWithZero`. `Valuation` asks only for the monoid class, so an inline
-- `WithZero …` elaborates with `WithZero`'s monoid instance, and then `CofinalValue`, which
-- needs the group class, cannot even be *stated* about the result -- a mismatch no `letI`
-- inside a later proof can repair.
abbrev RestrictedValues (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) : Type _ :=
  WithZero (ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg)).toSubgroup

/-- `RestrictedValues` is a linearly ordered commutative group with zero. -/
-- Registered explicitly so downstream statements find this instance rather than `WithZero`'s
-- monoid instance: without it the abbreviation unfolds and the monoid instance wins.
noncomputable instance instLinearOrderedCommGroupWithZeroRestrictedValues (v : Valuation A Γ₀)
    (I : Ideal A) (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    LinearOrderedCommGroupWithZero (RestrictedValues v I hfg) :=
  inferInstance

/-- **Wedhorn §7.1.2: the restriction `v ↦ v|cΓ_v(I)`.** Values whose unit lies in `cΓ_v(I)` are
kept; every other value is sent to `0`. -/
noncomputable def restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    Valuation A (RestrictedValues v I hfg) :=
  (v.restrict).restrictToConvex _ (mk0_restrict_mem_comapUnitsWithZero v I hfg)

/-- **The defining unfolding**, so that the lemmas below rewrite through it rather than relying
on `restrictToIdeal` unfolding implicitly. The boundedness hypothesis is taken as an argument;
by proof irrelevance any proof of it gives the same restriction. -/
theorem restrictToIdeal_def (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hH : ∀ a : A, ∀ ha : v.restrict a ≠ 0, 1 ≤ v.restrict a →
      Units.mk0 (v.restrict a) ha ∈
        ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg)) :
    v.restrictToIdeal I hfg = (v.restrict).restrictToConvex _ hH :=
  (rfl)

/-! ### The restriction, characterised through `cΓ_v(I)`

`restrictToIdeal` keeps or discards a value according to membership in the *transported*
`cΓ_v(I)`, which is not the form a consumer holds: the introduction rules for `cΓ_v(I)` speak
about the value group. The bridge below converts between the two, and the lemmas after it are
stated so that no consumer has to unfold the definition or mention the transport. -/

/-- **The bridge.** A value's unit lies in the transported `cΓ_v(I)` exactly when the value,
read in the value group, lies in `cΓ_v(I)` itself.

Private: it is the units-transport implementation, and every lemma below applies it internally,
so no consumer has to name `comapUnitsWithZero`. -/
private theorem mk0_restrict_mem_comapUnitsWithZero_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    Units.mk0 (v.restrict a) (fun h => h0 (v.restrict_eq_zero_iff.mp h)) ∈
        ConvexSubgroup.comapUnitsWithZero (characteristicSubgroupOfIdeal v I hfg) ↔
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∈ characteristicSubgroupOfIdeal v I hfg := by
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZeroEquiv_mk0_restrict v h0 _]

/-- Off `cΓ_v(I)`, the restriction vanishes. The hypothesis is non-membership in `cΓ_v(I)`
itself; the transport is applied internally.

Not `@[simp]`: `restrictToIdeal_eq_zero_iff` is the simp-normal form for a vanishing
restriction, and it rewrites this lemma's left-hand side, which `simpNF` rejects. -/
theorem restrictToIdeal_apply_of_notMem (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0)
    (hm : valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∉ characteristicSubgroupOfIdeal v I hfg) :
    v.restrictToIdeal I hfg a = 0 :=
by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact _root_.Valuation.restrictToConvex_apply_of_notMem _ _ _ _
    (fun hmem => hm ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0).mp hmem))

/-- The restriction vanishes wherever `v` does. -/
@[simp]
theorem restrictToIdeal_apply_of_eq_zero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a = 0) : v.restrictToIdeal I hfg a = 0 :=
by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact _root_.Valuation.restrictToConvex_apply_of_eq_zero _ _ _ (v.restrict_eq_zero_iff.mpr h0)

/-- **Where the restriction vanishes at a nonzero value**, stated through `cΓ_v(I)` itself.
`restrictToIdeal_eq_zero_iff` is the total form, and is the `@[simp]` one: tagging this
branch too makes its left-hand side reducible by that lemma, which `simpNF` rejects. -/
theorem restrictToIdeal_eq_zero_iff_of_ne (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0) :
    v.restrictToIdeal I hfg a = 0 ↔
      valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∉ characteristicSubgroupOfIdeal v I hfg :=
  by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact (_root_.Valuation.restrictToConvex_eq_zero_iff_of_ne _ _ _
      (fun h => h0 (v.restrict_eq_zero_iff.mp h))).trans
    (not_congr (mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0))

/-- **Where the restriction vanishes, totally**: at the zeros of `v`, and where `v` is nonzero
but its value escapes `cΓ_v(I)`. `restrictToIdeal_eq_zero_iff_of_ne` is the nonzero branch, in
the form consumers holding a nonvanishing hypothesis want. -/
@[simp]
theorem restrictToIdeal_eq_zero_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a : A) :
    v.restrictToIdeal I hfg a = 0 ↔ (MonoidWithZeroHom.ofClass v) a = 0 ∨
      ∃ h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0,
        valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∉ characteristicSubgroupOfIdeal v I hfg := by
  rw [restrictToIdeal, _root_.Valuation.restrictToConvex_eq_zero_iff]
  constructor
  · rintro (hz | ⟨hr, hnm⟩)
    · exact Or.inl (v.restrict_eq_zero_iff.mp hz)
    · refine Or.inr ⟨fun h => hr (v.restrict_eq_zero_iff.mpr h), fun hmem => hnm ?_⟩
      exact (mk0_restrict_mem_comapUnitsWithZero_iff v I hfg _).mpr hmem
  · rintro (hz | ⟨h0, hnm⟩)
    · exact Or.inl (v.restrict_eq_zero_iff.mpr hz)
    · refine Or.inr ⟨fun h => h0 (v.restrict_eq_zero_iff.mp h), fun hmem => hnm ?_⟩
      exact (mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0).mp hmem

/-- On values kept by the restriction, the order is both preserved and reflected — stated
through membership in `cΓ_v(I)` itself.

Not `@[simp]`: `restrictToIdeal_le_iff` is the simp-normal form for a comparison of restricted
values, and it rewrites this lemma's left-hand side, which `simpNF` rejects. -/
theorem restrictToIdeal_le_iff_of_mem (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a b : A}
    (h0a : v a ≠ 0) (h0b : v b ≠ 0)
    (hma : valueGroup.mk (.ofClass v) 1 a (by simp) h0a ∈ characteristicSubgroupOfIdeal v I hfg)
    (hmb : valueGroup.mk (.ofClass v) 1 b (by simp) h0b ∈ characteristicSubgroupOfIdeal v I hfg) :
    v.restrictToIdeal I hfg a ≤ v.restrictToIdeal I hfg b ↔ v a ≤ v b :=
by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg),
    _root_.Valuation.restrictToConvex_le_iff_of_mem _ _ _ _ _
      ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0a).mpr hma)
      ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0b).mpr hmb),
    _root_.Valuation.restrict_le_iff]

/-- **Comparison after restriction, totally**: a value discarded by the restriction is below
everything, a kept value is below only kept values, and two kept values compare exactly as they
did under `v`. `restrictToIdeal_le_iff_of_mem` is the both-kept branch, in the form consumers
holding membership hypotheses want.

The side conditions are stated as vanishing of the restriction, which
`restrictToIdeal_eq_zero_iff` turns into membership in `cΓ_v(I)`; so a caller never has to name
the transported subgroup. -/
@[simp]
theorem restrictToIdeal_le_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a b : A) :
    v.restrictToIdeal I hfg a ≤ v.restrictToIdeal I hfg b ↔
      v.restrictToIdeal I hfg a = 0 ∨ v.restrictToIdeal I hfg b ≠ 0 ∧ v a ≤ v b :=
by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg),
    _root_.Valuation.restrictToConvex_le_iff, _root_.Valuation.restrict_le_iff]

/-- A value at least `1` stays at least `1`: `cΓ_v(I)` keeps every attained value `≥ 1`. -/
theorem one_le_restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A} (h1 : 1 ≤ v.restrict a) :
    1 ≤ v.restrictToIdeal I hfg a := by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact _root_.Valuation.one_le_restrictToConvex _ _ _ h1

end TauCeti.Valuation
