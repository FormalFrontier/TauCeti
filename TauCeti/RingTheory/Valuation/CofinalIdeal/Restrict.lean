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

* `Valuation.RestrictedValues` : the value monoid the restriction lands in.
* `Valuation.restrictToIdeal` : the restricted valuation `v|cΓ_v(I)`.

## Main results

* `Valuation.restrictToIdeal_apply_of_notMem`,
  `Valuation.restrictToIdeal_apply_of_eq_zero` : the two vanishing branches.
* `Valuation.restrictToIdeal_eq_zero_iff` : where the restriction vanishes, totally.
* `Valuation.restrictToIdeal_le_iff` : how restricted values compare, totally.
* `Valuation.restrictToIdeal_ne_zero_of_le` : the restriction keeps every value above a
  kept value.
* `Valuation.exists_mem_restrictToIdeal_ne_zero` : **Wedhorn Lemma 7.5(3)**, that the
  restriction does not vanish identically on `I` unless `v` does.
* `Valuation.restrictToIdeal_ne_zero_of_isAdmissible` : it does not kill a denominator
  dominating an admissible numerator set.

The *characterisation* lemmas — the vanishing branches, `restrictToIdeal_eq_zero_iff` and
`restrictToIdeal_le_iff` — are phrased through `cΓ_v(I)` itself or through vanishing of the
restriction, so a consumer of them never names the transport. `one_le_restrictToIdeal` mentions
neither, being an order fact about `v.restrict`.

The transport is named by four declarations, each unavoidably. `RestrictedValues` *is* the
transported subgroup with a zero adjoined, and the private `restrictToIdeal_def` is the
definitional unfolding and so carries the boundedness hypothesis over it. The two comparison
lemmas against an abstract bound, `coe_le_restrictToIdeal_iff` and `restrictToIdeal_lt_coe_iff`,
quantify over a member of that subgroup: their whole point is to compare a restricted value
against a bound arriving from the value group rather than from a ring element, and such a bound
*is* an element of the transported subgroup. A cofinality argument needs them in that form.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §7.1.2

## Provenance

The construction is the one called `restrictIdeal` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch `dev/adic-spaces` at commit
`37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`, project `projects/AdicSpaces/`, file
`Adic spaces/CharacteristicSubgroup.lean`, built there on `restrictToConvexBounded`. The
port was checked against that source rather than copied: AINTLIB's `cGammaIdeal` is already
phrased on `Γ₀ˣ` and so needs no transport, whereas `cΓ_v(I)` here lives in the value group and
is carried across by `ConvexSubgroup.comapUnitsWithZero`.
-/

public section

namespace Valuation

open MonoidWithZeroHom TauCeti

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- The units identification takes the unit of a restricted value to the value-group element it
names. This is the bridge between membership in a transported convex subgroup, which is phrased
through `OrderMonoidIso.unitsWithZero`, and the introduction rules for `cΓ_v(I)`, which are
phrased through `valueGroup.mk`. -/
private theorem unitsWithZero_mk0_restrict (v : Valuation A Γ₀) {a : A}
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
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZero_mk0_restrict v h0 ha]
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
by proof irrelevance any proof of it gives the same restriction.

Private: it is stated against the `restrictToConvex` representation and makes the caller supply a
transport-level boundedness proof, neither of which a consumer should have to see. The
characterisation lemmas below are the public interface. -/
private theorem restrictToIdeal_def (v : Valuation A Γ₀) (I : Ideal A)
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
  rw [ConvexSubgroup.mem_comapUnitsWithZero, unitsWithZero_mk0_restrict v h0 _]

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
  exact restrictToConvex_apply_of_notMem _ _ _ _
    (fun hmem => hm ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0).mp hmem))

/-- The restriction vanishes wherever `v` does. -/
@[simp]
theorem restrictToIdeal_apply_of_eq_zero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a = 0) : v.restrictToIdeal I hfg a = 0 :=
by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact restrictToConvex_apply_of_eq_zero _ _ _ (v.restrict_eq_zero_iff.mpr h0)

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
  exact (restrictToConvex_eq_zero_iff_of_ne _ _ _
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
  rw [restrictToIdeal, restrictToConvex_eq_zero_iff]
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
    restrictToConvex_le_iff_of_mem _ _ _ _ _
      ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0a).mpr hma)
      ((mk0_restrict_mem_comapUnitsWithZero_iff v I hfg h0b).mpr hmb),
    restrict_le_iff]

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
    restrictToConvex_le_iff, restrict_le_iff]

/-- The companion of `restrictToIdeal_lt_coe_iff` with the member on the left. -/
theorem coe_le_restrictToIdeal_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a : A)
    (u : (ConvexSubgroup.comapUnitsWithZero
      (characteristicSubgroupOfIdeal v I hfg)).toSubgroup) :
    (u : RestrictedValues v I hfg) ≤ v.restrictToIdeal I hfg a ↔
      ((u : (ValueGroup₀ (.ofClass v))ˣ) : ValueGroup₀ (.ofClass v)) ≤ v.restrict a :=
  coe_le_restrictToConvex_iff _ _ _ a u

/-- Comparing a restricted value against an abstract member of the transported `cΓ_v(I)`,
back in the value monoid of `v`. This is the form a cofinality argument needs, where the
bound comes from the value group rather than from a ring element. -/
theorem restrictToIdeal_lt_coe_iff (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) (a : A)
    (u : (ConvexSubgroup.comapUnitsWithZero
      (characteristicSubgroupOfIdeal v I hfg)).toSubgroup) :
    v.restrictToIdeal I hfg a < (u : RestrictedValues v I hfg) ↔
      v.restrict a < ((u : (ValueGroup₀ (.ofClass v))ˣ) : ValueGroup₀ (.ofClass v)) :=
  restrictToConvex_lt_coe_iff _ _ _ a u

/-- A value at least `1` stays at least `1`: `cΓ_v(I)` keeps every attained value `≥ 1`. -/
theorem one_le_restrictToIdeal (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A} (h1 : 1 ≤ v.restrict a) :
    1 ≤ v.restrictToIdeal I hfg a := by
  rw [restrictToIdeal_def v I hfg (mk0_restrict_mem_comapUnitsWithZero v I hfg)]
  exact one_le_restrictToConvex _ _ _ h1

/-- The **meets** branch of `characteristicSubgroupOfIdeal_restrictToIdeal_eq_top`. When `I`
meets `cΓ_v`, Wedhorn's
`cΓ_v(I)` collapses to `cΓ_v` itself, so every element of the restricted value group is bracketed
by a characteristic generator `g ≥ 1` and its inverse; the ring element realising `g` is then the
witness that the restricted valuation has full characteristic group. -/
private theorem characteristicSubgroup_restrictToIdeal_eq_top_of_meets (w : Valuation A Γ₀)
    (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hm : IdealMeetsCharacteristicSubgroup w I) :
    characteristicSubgroup (w.restrictToIdeal I hfg) = ⊤ := by
  rw [← hasFullCharacteristicGroup_iff_characteristicSubgroup_eq_top,
    hasFullCharacteristicGroup_iff]
  intro γ hγ
  have hγ0 : ValueGroup₀.embedding γ ≠ 0 := fun h =>
    hγ.ne' (ValueGroup₀.embedding_injective (by simpa using h))
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hγ0
  -- rewriting the goal, not the hypothesis: `u`'s own type mentions `cΓ_v(I)`, so rewriting
  -- that away inside the hypothesis is not type correct
  have hmem : OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass w))ˣ)
      ∈ characteristicSubgroup w := by
    rw [← characteristicSubgroupOfIdeal_of_meets hfg hm]
    exact ConvexSubgroup.mem_comapUnitsWithZero.mp u.2
  obtain ⟨g, hg, hginv, hgle⟩ := mem_characteristicSubgroup_iff.mp hmem
  obtain ⟨hg1, a, hga⟩ := mem_characteristicGenerators.mp hg
  refine ⟨a, ?_, ?_⟩
  · -- `a` is kept by the restriction, since its value is the generator `g ≥ 1`
    have h1a : (1 : RestrictedValues w I hfg) ≤
        restrictToIdeal w I hfg a :=
      one_le_restrictToIdeal _ _ _ (by rw [hga]; exact_mod_cast hg1)
    rw [← ValueGroup₀.embedding_strictMono.le_iff_le, map_inv₀,
      Valuation.embedding_restrict, ← hu,
      inv_le_comm₀ (zero_lt_one.trans_le h1a) (pos_iff_ne_zero.mpr WithZero.coe_ne_zero),
      ← WithZero.coe_inv, coe_le_restrictToIdeal_iff, hga]
    have hcoe : ((OrderMonoidIso.unitsWithZero
          ((u⁻¹ : (ConvexSubgroup.comapUnitsWithZero
            (characteristicSubgroupOfIdeal w I hfg)).toSubgroup) :
            (ValueGroup₀ (.ofClass w))ˣ) :
          valueGroup (.ofClass w)) : ValueGroup₀ (.ofClass w)) =
        (((u⁻¹ : (ConvexSubgroup.comapUnitsWithZero
            (characteristicSubgroupOfIdeal w I hfg)).toSubgroup) :
          (ValueGroup₀ (.ofClass w))ˣ) : ValueGroup₀ (.ofClass w)) :=
      WithZero.coe_unitsWithZeroEquiv_eq_units_val _
    rw [← hcoe, WithZero.coe_le_coe]
    simp only [InvMemClass.coe_inv]
    simpa using inv_le_inv_iff.mpr hginv
  · rw [← ValueGroup₀.embedding_strictMono.le_iff_le, Valuation.embedding_restrict, ← hu,
      coe_le_restrictToIdeal_iff, hga]
    have hcoe : ((OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass w))ˣ) :
        valueGroup (.ofClass w)) : ValueGroup₀ (.ofClass w)) =
        ((u : (ValueGroup₀ (.ofClass w))ˣ) : ValueGroup₀ (.ofClass w)) :=
      WithZero.coe_unitsWithZeroEquiv_eq_units_val _
    rw [← hcoe, WithZero.coe_le_coe]
    exact hgle

/-- The **not-meets** branch of `characteristicSubgroupOfIdeal_restrictToIdeal_eq_top`. When
`I` does not meet `cΓ_v`,
`cΓ_v(I)` is the *greatest* ideal-cofinal convex subgroup, so each `a ∈ I` is already cofinal
below every member of it — and the members are exactly the nonzero values the restriction keeps,
so cofinality transfers to the restricted valuation. -/
private theorem cofinalValue_restrictToIdeal_of_not_meets (w : Valuation A Γ₀)
    (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hm : ¬ IdealMeetsCharacteristicSubgroup w I) :
    ∀ a ∈ I, CofinalValue (w.restrictToIdeal I hfg) a := by
  intro a ha
  have hgreat : IdealCofinalFor w
      (characteristicSubgroupOfIdeal w I hfg) I :=
    (isGreatestIdealCofinal_characteristicSubgroupOfIdeal hfg hm).1
  have hcof := cofinalValueFor_def.mp (idealCofinalFor_def.mp hgreat a ha)
  rw [cofinalValue_iff]
  intro γ hγ
  -- the bound is a nonzero element of the restricted value monoid, hence a member of `cΓ_v(I)`
  have hγ0 : ValueGroup₀.embedding γ ≠ 0 := fun h =>
    hγ.ne' (ValueGroup₀.embedding_injective (by simpa using h))
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hγ0
  -- its image in the value group of `v` lies in `cΓ_v(I)`, so `a` is cofinal below it
  have hmem := ConvexSubgroup.mem_comapUnitsWithZero.mp u.2
  obtain ⟨n, hn⟩ := hcof _ hmem
  refine ⟨n, ?_⟩
  rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding, ← hu,
    restrictToIdeal_lt_coe_iff, map_pow]
  -- `OrderMonoidIso.unitsWithZero` and `WithZero.unitsWithZeroEquiv` agree, but only up to
  -- defeq, so the bridge has to be stated rather than rewritten with
  have hcoe : ((OrderMonoidIso.unitsWithZero (u : (ValueGroup₀ (.ofClass w))ˣ) :
      valueGroup (.ofClass w)) : ValueGroup₀ (.ofClass w)) =
      ((u : (ValueGroup₀ (.ofClass w))ˣ) : ValueGroup₀ (.ofClass w)) :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val _
  rwa [hcoe] at hn

/-- **Wedhorn §7.1.2: the restricted valuation has full characteristic subgroup for `I`.** This
is the valuation-level content of the landing law — the restriction `v|cΓ_v(I)` satisfies the very
condition that cuts out `Spv (A, I)`. The point-level statement is
`TauCeti.ValuationSpectrum.restrictToIdeal_mem_spvOfIdeal`.

The proof is Wedhorn's case split on whether `I` meets `cΓ_v`, each branch above. -/
theorem characteristicSubgroupOfIdeal_restrictToIdeal_eq_top (w : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) :
    characteristicSubgroupOfIdeal (w.restrictToIdeal I hfg) I hfg = ⊤ := by
  rw [characteristicSubgroupOfIdeal_eq_top_iff]
  by_cases hm : IdealMeetsCharacteristicSubgroup w I
  · exact Or.inr (characteristicSubgroup_restrictToIdeal_eq_top_of_meets w I hfg hm)
  · exact Or.inl (cofinalValue_restrictToIdeal_of_not_meets w I hfg hm)

/-- **A value whose class lies in `cΓ_v(I)` is kept by the restriction.** The contrapositive of
the nonzero branch of `restrictToIdeal_eq_zero_iff`, in the form a consumer holding a membership
proof wants. -/
theorem restrictToIdeal_ne_zero_of_mem (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a : A}
    (h0 : (MonoidWithZeroHom.ofClass v) a ≠ 0)
    (hmem : valueGroup.mk (.ofClass v) 1 a (by simp) h0 ∈
      characteristicSubgroupOfIdeal v I hfg) :
    v.restrictToIdeal I hfg a ≠ 0 :=
  fun h ↦ (restrictToIdeal_eq_zero_iff_of_ne v I hfg h0).mp h hmem

/-- **The restriction keeps every value above a kept value.** A value discarded by `v|cΓ_v(I)`
cannot dominate a kept one: the kept value's class lies in `cΓ_v(I)`, and a larger class is
either below `1`, so convexity puts it in, or above `1`, so it is an attained characteristic
value and `cΓ_v ≤ cΓ_v(I)` puts it in.

This is the monotonicity that makes `r_I` a *horizontal* specialisation; Wedhorn uses it
without comment in the proof of Lemma 7.5(iii). -/
theorem restrictToIdeal_ne_zero_of_le (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {a b : A}
    (hb : v.restrictToIdeal I hfg b ≠ 0) (hab : v b ≤ v a) :
    v.restrictToIdeal I hfg a ≠ 0 := by
  intro ha
  have hb0 : (ofClass v) b ≠ 0 := fun h ↦ hb (restrictToIdeal_apply_of_eq_zero v I hfg h)
  have ha0 : (ofClass v) a ≠ 0 := fun h ↦ hb0 (le_antisymm (h ▸ hab) zero_le)
  have hbmem : valueGroup.mk (.ofClass v) 1 b (by simp) hb0 ∈
      characteristicSubgroupOfIdeal v I hfg := by
    by_contra hm
    exact hb (restrictToIdeal_apply_of_notMem v I hfg hb0 hm)
  have hamem : valueGroup.mk (.ofClass v) 1 a (by simp) ha0 ∉
      characteristicSubgroupOfIdeal v I hfg :=
    (restrictToIdeal_eq_zero_iff_of_ne v I hfg ha0).mp ha
  have hle : valueGroup.mk (.ofClass v) 1 b (by simp) hb0 ≤
      valueGroup.mk (.ofClass v) 1 a (by simp) ha0 := by
    have h := (v.restrict_le_iff (x := b) (y := a)).mpr hab
    rwa [v.restrict_eq_mk hb0, v.restrict_eq_mk ha0, WithZero.coe_le_coe] at h
  rcases le_or_gt (valueGroup.mk (.ofClass v) 1 a (by simp) ha0) 1 with h1 | h1
  · exact hamem (ConvexSubgroup.mem_of_le_le_one hbmem hle h1)
  · refine hamem (characteristicSubgroup_le_characteristicSubgroupOfIdeal v I hfg ?_)
    exact mem_characteristicSubgroup_iff.mpr
      ⟨_, mem_characteristicGenerators.mpr ⟨h1.le, a, v.restrict_eq_mk ha0⟩,
        Left.inv_le_self h1.le, le_rfl⟩

/-- **Wedhorn Lemma 7.5(3).** If `v` does not vanish identically on `I`, neither does its
restriction: `v(I) ≠ 0` implies `r_I(v)(I) ≠ 0`, so `I` is not contained in the support of the
restricted valuation. This is the form Wedhorn's Theorem 7.10 consumes. -/
theorem exists_mem_restrictToIdeal_ne_zero (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical)
    (hne : ∃ a ∈ I, (ofClass v) a ≠ 0) :
    ∃ a ∈ I, v.restrictToIdeal I hfg a ≠ 0 := by
  have hex : ∃ γ ∈ valueSet v I, γ ∈ characteristicSubgroupOfIdeal v I hfg := by
    by_cases hm : IdealMeetsCharacteristicSubgroup v I
    · obtain ⟨γ, hγI, hγc⟩ := idealMeetsCharacteristicSubgroup_iff.mp hm
      exact ⟨γ, hγI, characteristicSubgroup_le_characteristicSubgroupOfIdeal v I hfg hγc⟩
    · exact exists_mem_valueSet_mem_characteristicSubgroupOfIdeal hfg hm hne
  obtain ⟨γ, hγI, hγH⟩ := hex
  obtain ⟨a, haI, hav⟩ := mem_valueSet.mp hγI
  have ha0 : (ofClass v) a ≠ 0 := fun h ↦ by
    rw [v.restrict_eq_zero_iff.mpr h] at hav
    exact WithZero.coe_ne_zero hav.symm
  refine ⟨a, haI, restrictToIdeal_ne_zero_of_mem v I hfg ha0 ?_⟩
  have hcoe : (valueGroup.mk (.ofClass v) 1 a (by simp) ha0 :
      ValueGroup₀ (.ofClass v)) = γ := by
    rw [← v.restrict_eq_mk ha0, hav]
  rwa [WithZero.coe_inj.mp hcoe]

/-- **The restriction does not kill an admissible denominator.** If `u` dominates a set
`T` with `I ⊆ √((T ∪ {u}) · A)` and `v u ≠ 0`, then `v|cΓ_v(I)` keeps `u`.

This is one of the auxiliary claims in Wedhorn's proof of Lemma 7.5(1) — step (iii) there — and
it is what lets `restrictToIdealCodRestrict_preimage` compute the preimage of a rational
subset. -/
theorem restrictToIdeal_ne_zero_of_isAdmissible (v : Valuation A Γ₀) (I : Ideal A)
    (hfg : ∃ J : Ideal A, J.FG ∧ I.radical = J.radical) {T : Set A} {u : A}
    (hadm : I ≤ (Ideal.span (insert u T)).radical)
    (hu0 : v u ≠ 0) (hT : ∀ t ∈ T, v t ≤ v u) :
    v.restrictToIdeal I hfg u ≠ 0 := by
  intro hRu
  set R := v.restrictToIdeal I hfg with hR
  have hsupp : insert u T ⊆ (Valuation.supp R : Set A) := by
    rintro t (rfl | ht)
    · exact hRu
    · refine Valuation.mem_supp_iff R t |>.mpr ?_
      by_contra hRt
      exact absurd hRu (restrictToIdeal_ne_zero_of_le v I hfg hRt (hT t ht))
  have hI : ∀ a ∈ I, R a = 0 := by
    have h : I ≤ Valuation.supp R := by
      refine hadm.trans ?_
      rw [← (inferInstance : Ideal.IsPrime (Valuation.supp R)).radical]
      exact Ideal.radical_mono (Ideal.span_le.mpr hsupp)
    exact fun a ha ↦ (Valuation.mem_supp_iff R a).mp (h ha)
  by_cases hne : ∃ a ∈ I, (ofClass v) a ≠ 0
  · obtain ⟨a, haI, hane⟩ := exists_mem_restrictToIdeal_ne_zero v I hfg hne
    exact hane (hI a haI)
  · push Not at hne
    have htop : characteristicSubgroupOfIdeal v I hfg = ⊤ :=
      (characteristicSubgroupOfIdeal_eq_top_iff hfg).mpr
        (Or.inl fun a ha ↦ cofinalValueFor_top_iff.mp (cofinalValueFor_of_eq_zero (hne a ha)))
    exact restrictToIdeal_ne_zero_of_mem v I hfg hu0 (htop ▸ ConvexSubgroup.mem_top) hRu

end Valuation
