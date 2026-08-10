/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

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

the derived subgroup of `G` modulo the centre *of that derived subgroup*, and the group obtained
by feeding it the fixed points of an endomorphism.

The construction is the last step of the standard recipe producing a finite group of Lie type: one
takes the fixed points `H` of a Steinberg endomorphism of a pinned algebraic group, passes to
`[H, H]`, and quotients by the centre of `[H, H]`. Taking the derived subgroup handles the
parameters at which `H` fails to be perfect, and the central quotient is what turns a quasisimple
group into a simple one. Everything in this file is carrier-independent: it needs only a group and,
for the second half, an endomorphism of it, so it is available before any particular ambient group
has been constructed.

Nothing here proves that the resulting group is finite or simple. What is proved is that the recipe
does nothing once it has succeeded: on a perfect group with trivial centre — in particular on any
nonabelian simple group — it returns the group itself, and by Grün's lemma its output is centreless
as soon as `[G, G]` is perfect, so a second application changes nothing. Its transport along
isomorphisms is recorded as well, so the output does not depend on the model of the input.

## Main definitions

* `TauCeti.DerivedCentralQuotient`: the group `[G, G] / Z([G, G])`.
* `TauCeti.DerivedCentralQuotient.congr`: transport along an isomorphism of groups.
* `TauCeti.DerivedCentralQuotient.lift`: the factorisation of a surjection onto a centreless group.
* `TauCeti.fixedSubgroup`: the subgroup of points fixed by an endomorphism, `F.eqLocus (.id G)`.
* `TauCeti.FixedPointCandidate`: the derived central quotient of a fixed subgroup.

## Main results

* `TauCeti.DerivedCentralQuotient.mulEquivOfCenterEqBot`: a perfect group with trivial centre is its
  own derived central quotient.
* `TauCeti.DerivedCentralQuotient.mulEquivOfIsSimpleGroup`: so is a nonabelian simple group.
* `TauCeti.DerivedCentralQuotient.center_eq_bot`: the output is centreless when `[G, G]` is perfect,
  and `TauCeti.DerivedCentralQuotient.mulEquivSelf` then makes the construction idempotent.
* `TauCeti.DerivedCentralQuotient.subsingleton_iff`: the output is trivial exactly when `[G, G]` is
  commutative.
* `TauCeti.fixedSubgroup_le_fixedSubgroup_pow`: fixed points of an endomorphism are fixed by all of
  its powers.
* `TauCeti.fixedPointCandidateCongr`: transport of the whole recipe along an isomorphism
  intertwining two endomorphisms.

## References

This is the carrier-independent half of milestone L3 of `TauCetiRoadmap/CFSGStatement/README.md`,
which fixes the recipe `H = fixedSubgroup F` and `Group = [H, H] / Z([H, H])` and the reading of the
centre as the centre of the derived subgroup rather than of `H`. The construction is standard; see
R. W. Carter, *Simple Groups of Lie Type*, and D. Gorenstein, R. Lyons and R. Solomon,
*The Classification of the Finite Simple Groups*.
-/

public section

namespace TauCeti

open Subgroup

variable {G G' : Type*} [Group G] [Group G']

/-! ## Centres and derived subgroups under an isomorphism -/

/-- An isomorphism of groups carries the centre onto the centre.

Mathlib's `Subgroup.centerCongr` records the resulting isomorphism of centres; the equality of
subgroups is what `QuotientGroup.congr` consumes. -/
theorem map_center (e : G ≃* G') : (center G).map (e : G →* G') = center G' := by
  ext y
  simp only [mem_map, mem_center_iff, MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩ g
    obtain ⟨h, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · refine fun hy => ⟨e.symm y, fun g => e.injective ?_, e.apply_symm_apply y⟩
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e g)

/-- A surjection of groups carries the derived subgroup onto the derived subgroup.

Mathlib's `map_commutator_eq` computes the image as the commutator of the range; this is the
special case in which the range is everything. -/
theorem map_commutator_of_surjective (f : G →* G') (hf : Function.Surjective f) :
    (commutator G).map f = commutator G' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective f hf]

/-- The isomorphism of derived subgroups induced by an isomorphism of groups.

This is exposed because `commutatorCongr_coe`, its value on elements, holds by definitional
unfolding, and a theorem exported from this module may only unfold exposed definitions. -/
@[expose]
def commutatorCongr (e : G ≃* G') : ↥(commutator G) ≃* ↥(commutator G') :=
  (e.subgroupMap (commutator G)).trans
    (MulEquiv.subgroupCongr (map_commutator_of_surjective _ (by simpa using e.surjective)))

@[simp]
theorem commutatorCongr_coe (e : G ≃* G') (x : ↥(commutator G)) :
    ((commutatorCongr e x : ↥(commutator G')) : G') = e (x : G) :=
  rfl

/-! ## Surjections onto a centreless group -/

/-- The centre of a group lies in the kernel of every surjection onto a group with trivial
centre. -/
theorem center_le_ker (f : G →* G') (hf : Function.Surjective f) (hG' : center G' = ⊥) :
    center G ≤ f.ker := by
  intro x hx
  have hcentral : f x ∈ center G' := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := hf g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
  rw [hG', mem_bot] at hcentral
  exact hcentral

/-! ## The derived subgroup modulo its centre -/

variable (G) in
/-- The derived subgroup of `G` modulo the centre of that derived subgroup, `[G, G] / Z([G, G])`.

This is the group-theoretic step turning the fixed points of a Steinberg endomorphism into a
candidate simple group. No finiteness or simplicity is asserted: the construction is available for
every group, and returns the trivial group whenever `[G, G]` is commutative. -/
abbrev DerivedCentralQuotient : Type _ :=
  ↥(commutator G) ⧸ center ↥(commutator G)

namespace DerivedCentralQuotient

/-- An element of the derived subgroup dies in the derived central quotient exactly when it is
central in the derived subgroup. -/
theorem mk_eq_one_iff (x : ↥(commutator G)) :
    (x : DerivedCentralQuotient G) = 1 ↔ x ∈ center ↥(commutator G) :=
  QuotientGroup.eq_one_iff x

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

/-! ### Transport along an isomorphism -/

/-- The derived central quotient transported along an isomorphism of groups.

This is exposed because `congr_mk`, its value on a representative, holds by definitional unfolding,
and a theorem exported from this module may only unfold exposed definitions. -/
@[expose]
def congr (e : G ≃* G') : DerivedCentralQuotient G ≃* DerivedCentralQuotient G' :=
  QuotientGroup.congr _ _ (commutatorCongr e) (map_center _)

@[simp]
theorem congr_mk (e : G ≃* G') (x : ↥(commutator G)) :
    congr e (x : DerivedCentralQuotient G) = (commutatorCongr e x : DerivedCentralQuotient G') :=
  rfl

@[simp]
theorem congr_refl : congr (MulEquiv.refl G) = MulEquiv.refl (DerivedCentralQuotient G) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

/-! ### The universal property -/

/-- **The derived central quotient is the largest centreless quotient of the derived subgroup**: a
surjection of `[G, G]` onto a group with trivial centre factors through it.

This is exposed because `lift_mk`, the equation defining it on representatives, holds by
definitional unfolding, and a theorem exported from this module may only unfold exposed
definitions. -/
@[expose]
def lift {K : Type*} [Group K] (f : ↥(commutator G) →* K) (hf : Function.Surjective f)
    (hK : center K = ⊥) : DerivedCentralQuotient G →* K :=
  QuotientGroup.lift _ f (center_le_ker f hf hK)

@[simp]
theorem lift_mk {K : Type*} [Group K] (f : ↥(commutator G) →* K) (hf : Function.Surjective f)
    (hK : center K = ⊥) (x : ↥(commutator G)) :
    lift f hf hK (x : DerivedCentralQuotient G) = f x :=
  rfl

theorem lift_surjective {K : Type*} [Group K] (f : ↥(commutator G) →* K)
    (hf : Function.Surjective f) (hK : center K = ⊥) : Function.Surjective (lift f hf hK) :=
  fun k => (hf k).elim fun x hx => ⟨(x : DerivedCentralQuotient G), hx⟩

/-! ### The recipe on groups it has already succeeded on -/

/-- **A perfect group with trivial centre is its own derived central quotient.** -/
def mulEquivOfCenterEqBot [Group.IsPerfect G] (h : center G = ⊥) :
    DerivedCentralQuotient G ≃* G :=
  let e : ↥(commutator G) ≃* G :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  have hc : center ↥(commutator G) = ⊥ := by
    rw [← map_center e.symm, h, Subgroup.map_bot]
  (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot.trans e)

/-- A nonabelian simple group has trivial centre. -/
theorem center_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    center G = ⊥ :=
  (Subgroup.Normal.eq_bot_or_eq_top inferInstance).resolve_right fun ht =>
    h (center_eq_top_iff.mp ht)

/-- A nonabelian simple group is perfect. -/
theorem isPerfect_of_isSimpleGroup [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    Group.IsPerfect G := by
  refine ⟨(Subgroup.Normal.eq_bot_or_eq_top inferInstance).resolve_left fun hb => ?_⟩
  rw [commutator_def, commutator_top_right_eq_bot_iff_le_center, top_le_iff] at hb
  exact h (center_eq_top_iff.mp hb)

/-- **The recipe returns a nonabelian simple group unchanged.**

So the construction is the identity on every entry of the classification list, and cannot turn one
entry into another. -/
def mulEquivOfIsSimpleGroup [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    DerivedCentralQuotient G ≃* G :=
  letI := isPerfect_of_isSimpleGroup h
  mulEquivOfCenterEqBot (center_eq_bot_of_isSimpleGroup h)

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

end DerivedCentralQuotient

/-! ## Fixed points of an endomorphism -/

/-- The subgroup of points fixed by an endomorphism of a group, `F.eqLocus (MonoidHom.id G)`. -/
abbrev fixedSubgroup (F : G →* G) : Subgroup G := F.eqLocus (MonoidHom.id G)

@[simp]
theorem mem_fixedSubgroup {F : G →* G} {x : G} : x ∈ fixedSubgroup F ↔ F x = x := Iff.rfl

theorem fixedSubgroup_id : fixedSubgroup (MonoidHom.id G) = ⊤ :=
  MonoidHom.eqLocus_same _

/-- Only the identity fixes every point. -/
theorem fixedSubgroup_eq_top_iff {F : G →* G} : fixedSubgroup F = ⊤ ↔ F = MonoidHom.id G := by
  constructor
  · refine fun h => MonoidHom.ext fun x => ?_
    exact mem_fixedSubgroup.mp (h ▸ mem_top x)
  · rintro rfl
    exact fixedSubgroup_id

/-- A point fixed by an endomorphism is fixed by each of its powers.

The Suzuki--Ree Steinberg maps are odd powers of a half-Frobenius whose square is a Frobenius, so
this is what places their fixed groups inside the fixed group of the corresponding untwisted
Frobenius. -/
theorem fixedSubgroup_le_fixedSubgroup_pow (F : Monoid.End G) (n : ℕ) :
    fixedSubgroup (F : G →* G) ≤ fixedSubgroup ((F ^ n : Monoid.End G) : G →* G) := by
  intro x hx
  -- `fixedSubgroup` takes a bundled `G →* G`, so the hypothesis and the goal apply their
  -- endomorphism through `MonoidHom.instFunLike`, whereas `Monoid.End.coe_pow` — the lemma turning
  -- a power of an endomorphism into an iterate — is stated through `Monoid.End.instFunLike`. The
  -- two instances are definitionally but not syntactically equal, so neither `rw` nor `simp` can
  -- bridge them; the `change` and the `show` restate the goal and the hypothesis on the
  -- `Monoid.End` side, where `simp` can apply `Monoid.End.coe_pow`.
  change (F ^ n) x = x
  simpa using Function.iterate_fixed (show F x = x from hx) n

/-- An isomorphism intertwining two endomorphisms carries fixed points onto fixed points. -/
theorem map_fixedSubgroup (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) :
    (fixedSubgroup F).map (e : G →* G') = fixedSubgroup F' := by
  ext y
  simp only [mem_map, mem_fixedSubgroup, MonoidHom.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [h x, hx]
  · refine fun hy => ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
    rw [← h (e.symm y), e.apply_symm_apply, hy]

/-- The isomorphism of fixed subgroups induced by an intertwining isomorphism.

This is exposed because `fixedSubgroupCongr_coe`, its value on elements, holds by definitional
unfolding, and a theorem exported from this module may only unfold exposed definitions. -/
@[expose]
def fixedSubgroupCongr (e : G ≃* G') {F : G →* G} {F' : G' →* G'} (h : ∀ x, F' (e x) = e (F x)) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup F') :=
  (e.subgroupMap (fixedSubgroup F)).trans (MulEquiv.subgroupCongr (map_fixedSubgroup e h))

@[simp]
theorem fixedSubgroupCongr_coe (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) (x : ↥(fixedSubgroup F)) :
    ((fixedSubgroupCongr e h x : ↥(fixedSubgroup F')) : G') = e (x : G) :=
  rfl

/-- The candidate simple group attached to an endomorphism `F` of a group: the derived subgroup of
the fixed points of `F`, modulo the centre of that derived subgroup.

For a Steinberg endomorphism of a pinned algebraic group over an algebraically closed field of
positive characteristic this is the corresponding finite group of Lie type; nothing of the sort is
asserted here. -/
abbrev FixedPointCandidate (F : G →* G) : Type _ :=
  DerivedCentralQuotient ↥(fixedSubgroup F)

/-- **The candidate attached to an endomorphism only depends on the endomorphism up to intertwining
isomorphism.** -/
def fixedPointCandidateCongr (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) : FixedPointCandidate F ≃* FixedPointCandidate F' :=
  DerivedCentralQuotient.congr (fixedSubgroupCongr e h)

/-- If the fixed points of `F` already form a nonabelian simple group, the recipe returns them. -/
def fixedPointCandidateMulEquiv (F : G →* G) [IsSimpleGroup ↥(fixedSubgroup F)]
    (h : ¬ IsMulCommutative ↥(fixedSubgroup F)) :
    FixedPointCandidate F ≃* ↥(fixedSubgroup F) :=
  DerivedCentralQuotient.mulEquivOfIsSimpleGroup h

end TauCeti
