/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# The derived subgroup modulo its centre

Let `G` be a group. This file studies the group

```text
[G, G] / Z([G, G]),
```

the derived subgroup of `G` modulo the centre *of that derived subgroup*.

The construction is the last step of the standard recipe producing a finite group of Lie type: one
takes the fixed points `H` of a Steinberg endomorphism of a pinned algebraic group, passes to
`[H, H]`, and quotients by the centre of `[H, H]`. Taking the derived subgroup handles the
parameters at which `H` fails to be perfect, and the central quotient is what turns a quasisimple
group into a simple one. Everything in this file is carrier-independent: it needs only a group, so
it is available before any particular ambient group has been constructed.

Nothing here proves that the resulting group is finite or simple. What is proved is that the recipe
does nothing once it has succeeded: on a perfect group with trivial centre — in particular on any
nonabelian simple group — it returns the group itself, and by Grün's lemma its output is centreless
as soon as `[G, G]` is perfect, so a second application changes nothing.

## Main definitions

* `TauCeti.DerivedCentralQuotient`: the group `[G, G] / Z([G, G])`.
* `TauCeti.DerivedCentralQuotient.lift`: the factorisation of a surjection onto a centreless group.

## Main results

* `TauCeti.DerivedCentralQuotient.mulEquivOfCenterEqBot`: a perfect group with trivial centre is its
  own derived central quotient.
* `TauCeti.DerivedCentralQuotient.mulEquivOfIsSimpleGroup`: so is a nonabelian simple group.
* `TauCeti.DerivedCentralQuotient.center_eq_bot`: the output is centreless when `[G, G]` is perfect,
  and `TauCeti.DerivedCentralQuotient.mulEquivSelf` then makes the construction idempotent.
* `TauCeti.DerivedCentralQuotient.subsingleton_iff`: the output is trivial exactly when `[G, G]` is
  commutative.

## References

This is the derived-subgroup-modulo-centre half of milestone L3 of
`TauCetiRoadmap/CFSGStatement/README.md`, which fixes the recipe `H = fixedSubgroup F` and
`Group = [H, H] / Z([H, H])` and the reading of the centre as the centre of the derived subgroup
rather than of `H`. The construction is standard; see R. W. Carter, *Simple Groups of Lie Type*,
and D. Gorenstein, R. Lyons and R. Solomon, *The Classification of the Finite Simple Groups*.
-/

public section

namespace TauCeti

open _root_.Subgroup

variable {G : Type*} [Group G]

namespace IsSimpleGroup

/-- A nonabelian simple group has trivial centre. -/
theorem center_eq_bot_of_not_isMulCommutative [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    center G = ⊥ :=
  (Subgroup.Normal.eq_bot_or_eq_top inferInstance).resolve_right fun ht =>
    h (center_eq_top_iff.mp ht)

/-- A nonabelian simple group is perfect. -/
theorem isPerfect_of_not_isMulCommutative [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    Group.IsPerfect G := by
  refine ⟨(Subgroup.Normal.eq_bot_or_eq_top inferInstance).resolve_left fun hb => ?_⟩
  rw [commutator_def, commutator_top_right_eq_bot_iff_le_center, top_le_iff] at hb
  exact h (center_eq_top_iff.mp hb)

end IsSimpleGroup

/-! ## The derived subgroup modulo its centre -/

variable (G) in
/-- The derived subgroup of `G` modulo the centre of that derived subgroup, `[G, G] / Z([G, G])`.

This is the group-theoretic step turning the fixed points of a Steinberg endomorphism into a
candidate simple group. No finiteness or simplicity is asserted: the construction is available for
every group, and returns the trivial group whenever `[G, G]` is commutative. -/
abbrev DerivedCentralQuotient : Type _ :=
  ↥(commutator G) ⧸ center ↥(commutator G)

namespace DerivedCentralQuotient

/-- The derived central quotient is trivial exactly when the derived subgroup is commutative. In
particular it is trivial for every commutative `G`, whose derived subgroup is itself trivial. -/
theorem subsingleton_iff :
    Subsingleton (DerivedCentralQuotient G) ↔ IsMulCommutative ↥(commutator G) := by
  rw [QuotientGroup.subsingleton_iff, center_eq_top_iff]

instance [IsMulCommutative ↥(commutator G)] : Subsingleton (DerivedCentralQuotient G) :=
  subsingleton_iff.mpr ‹_›

/-- The order of the derived central quotient divides the order of the group. -/
theorem card_dvd_card : Nat.card (DerivedCentralQuotient G) ∣ Nat.card G :=
  ((center ↥(commutator G)).card_quotient_dvd_card).trans (commutator G).card_subgroup_dvd_card

/-! ### The universal property -/

/-- A surjection from `[G, G]` onto a group with trivial centre factors through the derived central
quotient. -/
def lift {K : Type*} [Group K] (f : ↥(commutator G) →* K) (hf : Function.Surjective f)
    (hK : center K = ⊥) : DerivedCentralQuotient G →* K :=
  QuotientGroup.lift _ f (TauCeti.MonoidHom.center_le_ker f hf hK)

@[simp]
theorem lift_mk {K : Type*} [Group K] (f : ↥(commutator G) →* K) (hf : Function.Surjective f)
    (hK : center K = ⊥) (x : ↥(commutator G)) :
    lift f hf hK (x : DerivedCentralQuotient G) = f x := by
  simp only [lift, QuotientGroup.lift_mk]

/-- The factorisation through the derived central quotient is unique. -/
theorem lift_unique {K : Type*} [Group K] (f : ↥(commutator G) →* K)
    (hf : Function.Surjective f) (hK : center K = ⊥) (g : DerivedCentralQuotient G →* K)
    (hg : ∀ x : ↥(commutator G), g (x : DerivedCentralQuotient G) = f x) :
    g = lift f hf hK :=
  QuotientGroup.monoidHom_ext _ <| MonoidHom.ext fun x => by
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, hg, lift_mk]

/-- The factorisation of a surjection through the derived central quotient is again surjective, so
the quotient sits between `[G, G]` and the centreless group it was mapped onto. -/
theorem lift_surjective {K : Type*} [Group K] (f : ↥(commutator G) →* K)
    (hf : Function.Surjective f) (hK : center K = ⊥) : Function.Surjective (lift f hf hK) :=
  QuotientGroup.lift_surjective_of_surjective _ f hf
    (TauCeti.MonoidHom.center_le_ker f hf hK)

/-! ### The recipe on groups it has already succeeded on -/

/-- **A perfect group with trivial centre is its own derived central quotient.** -/
def mulEquivOfCenterEqBot [Group.IsPerfect G] (h : center G = ⊥) :
    DerivedCentralQuotient G ≃* G :=
  let e : ↥(commutator G) ≃* G :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  have hc : center ↥(commutator G) = ⊥ := by
    rw [← TauCeti.Subgroup.map_center_eq_center e.symm, h, Subgroup.map_bot]
  (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)

@[simp]
theorem mulEquivOfCenterEqBot_mk [Group.IsPerfect G] (h : center G = ⊥)
    (x : ↥(commutator G)) :
    mulEquivOfCenterEqBot h (x : DerivedCentralQuotient G) = (x : G) := by
  simp only [mulEquivOfCenterEqBot, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk, MulEquiv.subgroupCongr_apply,
    Subgroup.topEquiv_apply]
  exact congrArg Subtype.val (by
    simpa only [QuotientGroup.quotientBot_symm_apply] using
      QuotientGroup.quotientBot.apply_symm_apply x)

/-- **The recipe returns a nonabelian simple group unchanged.**

So the construction is the identity on every nonabelian entry of the classification list. The
abelian cyclic entries instead collapse to the trivial group by `subsingleton_iff`. -/
def mulEquivOfIsSimpleGroup [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    DerivedCentralQuotient G ≃* G :=
  letI := IsSimpleGroup.isPerfect_of_not_isMulCommutative h
  mulEquivOfCenterEqBot (IsSimpleGroup.center_eq_bot_of_not_isMulCommutative h)

@[simp]
theorem mulEquivOfIsSimpleGroup_mk [IsSimpleGroup G] (h : ¬ IsMulCommutative G)
    (x : ↥(commutator G)) :
    mulEquivOfIsSimpleGroup h (x : DerivedCentralQuotient G) = (x : G) := by
  exact @mulEquivOfCenterEqBot_mk G _ (IsSimpleGroup.isPerfect_of_not_isMulCommutative h)
    (IsSimpleGroup.center_eq_bot_of_not_isMulCommutative h) x

/-- **Grün's lemma for the recipe**: when the derived subgroup is perfect, the derived central
quotient has trivial centre.

This is the reason the two steps compose in the stated order: the centre is removed once and for
all, and does not reappear. -/
theorem center_eq_bot [Group.IsPerfect ↥(commutator G)] :
    center (DerivedCentralQuotient G) = ⊥ :=
  Group.IsPerfect.center_quotient_center_eq_bot ↥(commutator G)

/-- **The construction is idempotent on a group with perfect derived subgroup.** -/
def mulEquivSelf [Group.IsPerfect ↥(commutator G)] :
    DerivedCentralQuotient (DerivedCentralQuotient G) ≃* DerivedCentralQuotient G :=
  mulEquivOfCenterEqBot center_eq_bot

@[simp]
theorem mulEquivSelf_mk [Group.IsPerfect ↥(commutator G)]
    (x : ↥(commutator (DerivedCentralQuotient G))) :
    mulEquivSelf (G := G) (x : DerivedCentralQuotient (DerivedCentralQuotient G)) =
      (x : DerivedCentralQuotient G) :=
  mulEquivOfCenterEqBot_mk center_eq_bot x

end DerivedCentralQuotient

end TauCeti
