/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Logic.Small.Basic

/-!
# Universe transport for a classification of the finite simple groups

Fix a family `Model : ι → Type v` of groups. A statement of the form

```text
∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i)
```

reads as "the family classifies the finite simple groups in `Type u`". This file proves that the
statement does not depend on `u`: it holds in every universe as soon as it holds in `Type 0`, and
conversely.

Both directions come from replacing the group by an isomorphic copy in the universe one wants.
Downwards, Mathlib's finite-group transport supplies a group in `Type 0` isomorphic to `G`;
upwards, `ULift` moves a group in `Type 0` into `Type u`. Since the statement mentions the group
only through `G ≃* Model i`, either replacement leaves it unchanged.

The downward direction is the one a consumer needs, because a classification is stated once, with a
family of concrete carriers in `Type`, and is then applied to a group living wherever it happens to
live. Finiteness supplies the smallness used by this argument. Without some smallness hypothesis,
arbitrary groups cannot always be moved down:
`TauCeti.exists_group_not_mulEquiv_type_zero` exhibits a group in `Type 1` isomorphic to no group in
`Type 0` at all.

Nothing here asserts that any such classification is true; the file is about the shape of the
statement, not its content.

## Main results

* `TauCeti.exists_nonempty_mulEquiv_of_forall_type_zero`: **the universe transport**, from `Type 0`
  to `Type u`.
* `TauCeti.forall_exists_nonempty_mulEquiv_iff` and
  `TauCeti.forall_exists_nonempty_mulEquiv_congr`: the classification statement is the same in every
  universe.
* `TauCeti.exists_group_not_mulEquiv_type_zero`: arbitrary groups cannot always be moved to
  `Type 0`.

## Roadmap

This is the universe-transport half of milestone A0 of `TauCetiRoadmap/CFSGStatement/README.md`,
whose target `classificationStatement_of_zero` reads `ClassificationStatement.{0} →
ClassificationStatement.{u}`, on the grounds that "`CFSGIndex.Group` lands in `Type`, so
`ClassificationStatement.{0}` is the substantive instance and every larger universe follows from it,
`Finite G` supplying the transport". The results below are stated for an arbitrary family of
carriers rather than for `CFSGIndex.Group`, which milestones L0 to L3 have still to construct; once
that carrier exists, `classificationStatement_of_zero` is
`TauCeti.exists_nonempty_mulEquiv_of_forall_type_zero` at `Model := CFSGIndex.Group`.
-/

public section

namespace TauCeti

universe u u' v w

/-! ## Groups in a prescribed universe -/

/-- The `ULift` copy of a simple group is simple, so a simple group has a simple model in every
larger universe. -/
instance instIsSimpleGroupULift {G : Type u} [Group G] [IsSimpleGroup G] :
    IsSimpleGroup (ULift.{v} G) :=
  (MulEquiv.ulift : ULift.{v} G ≃* G).isSimpleGroup

/-! ## Transporting a classification statement -/

section Family

-- Only the multiplications of the models are ever used: a `MulEquiv` out of a group already forces
-- its target to be a group, so asking for `Group (Model i)` would be a redundant hypothesis.
variable {ι : Sort w} {Model : ι → Type v} [∀ i, Mul (Model i)]

/-- Being isomorphic to a member of a fixed family of groups depends only on the isomorphism class
of the group, and in particular not on the universe it lives in. -/
theorem exists_nonempty_mulEquiv_congr {G : Type u} {H : Type u'} [Group G] [Group H] (e : G ≃* H)
    (h : ∃ i, Nonempty (H ≃* Model i)) : ∃ i, Nonempty (G ≃* Model i) :=
  h.imp fun _ hi => hi.map e.trans

/-- A group is isomorphic to a member of the family exactly when its `ULift` copy in a larger
universe is. -/
theorem exists_nonempty_mulEquiv_ulift_iff {G : Type u} [Group G] :
    (∃ i, Nonempty (ULift.{u'} G ≃* Model i)) ↔ ∃ i, Nonempty (G ≃* Model i) :=
  ⟨exists_nonempty_mulEquiv_congr (MulEquiv.ulift : ULift.{u'} G ≃* G).symm,
    exists_nonempty_mulEquiv_congr (MulEquiv.ulift : ULift.{u'} G ≃* G)⟩

/-- **The universe transport.** A family of groups that classifies the finite simple groups in
`Type 0` classifies the finite simple groups in every universe.

Mathlib's finite-group transport supplies a finite model `H : Type` and an isomorphism `G ≃* H`.
Simplicity is transported across this isomorphism, which is then composed with the one the
hypothesis supplies. -/
theorem exists_nonempty_mulEquiv_of_forall_type_zero
    (h : ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* Model i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : ∃ i, Nonempty (G ≃* Model i) := by
  obtain ⟨H, _, fintypeH, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, 0} G
  let _ : Finite H := @Finite.of_fintype H fintypeH
  let _ : IsSimpleGroup H := e.symm.isSimpleGroup
  exact exists_nonempty_mulEquiv_congr e (h H)

/-- The reverse transport: a family that classifies the finite simple groups in `Type u` classifies
those in `Type 0`, by lifting a group in `Type 0` into `Type u`. -/
theorem forall_type_zero_of_forall_exists_nonempty_mulEquiv
    (h : ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i))
    (H : Type) [Group H] [Finite H] [IsSimpleGroup H] : ∃ i, Nonempty (H ≃* Model i) :=
  exists_nonempty_mulEquiv_ulift_iff.mp (h (ULift.{u} H))

/-- **A classification of the finite simple groups says the same thing in every universe.**

So a development that assumes the statement in the universe it needs loses nothing by proving it in
`Type 0`, and a development that has it in `Type 0` may apply it anywhere. -/
theorem forall_exists_nonempty_mulEquiv_iff :
    (∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i)) ↔
      ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* Model i) := by
  refine ⟨forall_type_zero_of_forall_exists_nonempty_mulEquiv, fun h G _ _ _ => ?_⟩
  exact exists_nonempty_mulEquiv_of_forall_type_zero h G

/-- Comparing two arbitrary universes, rather than each against `Type 0`. -/
theorem forall_exists_nonempty_mulEquiv_congr :
    (∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i)) ↔
      ∀ (G : Type u') [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i) :=
  forall_exists_nonempty_mulEquiv_iff.trans forall_exists_nonempty_mulEquiv_iff.symm

end Family

/-! ## Why the downward proof uses finiteness -/

/-- **Arbitrary groups cannot always be moved to `Type 0`.**

There is a group in `Type 1` isomorphic to no group in `Type 0` whatsoever, namely the free group on
`Type 0`: an isomorphism to a group in `Type 0` would make it small, hence would make `Type 0`
small, which it is not. Thus the proof above needs a source of smallness, supplied there by
`Finite G`. This example does not assert that universe transport for simple groups fails without
the finiteness hypothesis. -/
theorem exists_group_not_mulEquiv_type_zero :
    ∃ (G : Type 1) (_ : Group G), ∀ (H : Type) [Group H], IsEmpty (G ≃* H) := by
  refine ⟨FreeGroup (Type 0), inferInstance, fun H _ => ⟨fun e => ?_⟩⟩
  have : Small.{0} (FreeGroup (Type 0)) := Small.mk' e.toEquiv
  exact not_small_type.{0, 0} (small_of_injective FreeGroup.of_injective)

end TauCeti
