/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Small.Basic

/-!
# Universe transport for a classification of the finite simple groups

Fix a family `Model : ι → Type v` of types carrying a multiplication. A statement of the form

```text
∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i)
```

reads as "the family classifies the finite simple groups in `Type u`". This file proves that the
statement does not depend on `u`: it holds in every universe as soon as it holds in any one of
them, and in particular as soon as it holds in `Type 0`.

The transport comes from replacing the group by an isomorphic copy in the universe one wants:
Mathlib's finite-group transport supplies, for a finite group `G : Type u` and any target universe
`u'`, a finite group in `Type u'` isomorphic to `G`. Since the statement mentions the group only
through `G ≃* Model i`, the replacement leaves it unchanged, and the same lemma serves in both
directions.

The specialisation whose hypothesis lives in `Type 0` is the one a consumer needs, because a
classification is stated once, with a family of concrete carriers in `Type`, and is then applied to
a group living wherever it happens to live; that application moves the group down to `Type 0`.
Finiteness supplies the smallness used by this argument. Without some smallness hypothesis,
arbitrary groups cannot always be moved down:
`TauCeti.exists_group_not_mulEquiv_type_zero` exhibits a group in `Type 1` isomorphic to no group in
`Type 0` at all.

Nothing here asserts that any such classification is true; the file is about the shape of the
statement, not its content.

## Main results

* `TauCeti.exists_nonempty_mulEquiv_of_forall`: **the universe transport**, between arbitrary
  universes, and `TauCeti.exists_nonempty_mulEquiv_of_forall_type_zero`, its specialisation from
  `Type 0` to `Type u`.
* `TauCeti.forall_exists_nonempty_mulEquiv_congr`: the classification statement is the same in
  every universe; at `u' := 0` it compares an arbitrary universe with `Type 0`.
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

/-! ## Transporting a classification statement -/

section Family

-- Only the multiplications of the models are ever used: the statement mentions `Model i` solely
-- through `G ≃* Model i`, so a `Group (Model i)` hypothesis would be an unused one. A consumer
-- holding such an isomorphism can transport the group structure of `G` along it.
variable {ι : Sort w} {Model : ι → Type v} [∀ i, Mul (Model i)]

/-- Being isomorphic to a member of a fixed family depends only on the isomorphism class of the
multiplication, and in particular not on the universe it lives in. -/
theorem exists_nonempty_mulEquiv_of_mulEquiv {G : Type u} {H : Type u'} [Mul G] [Mul H] (e : G ≃* H)
    (h : ∃ i, Nonempty (H ≃* Model i)) : ∃ i, Nonempty (G ≃* Model i) :=
  h.imp fun _ hi => hi.map e.trans

/-- **The universe transport.** A family that classifies the finite simple groups in `Type u'`
classifies the finite simple groups in `Type u`, for any two universes.

Mathlib's finite-group transport supplies a finite model `H : Type u'` and an isomorphism `G ≃* H`.
Simplicity is transported across this isomorphism, which is then composed with the one the
hypothesis supplies. -/
theorem exists_nonempty_mulEquiv_of_forall
    (h : ∀ (H : Type u') [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* Model i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : ∃ i, Nonempty (G ≃* Model i) := by
  obtain ⟨H, _, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, u'} G
  let _ : Finite H := .of_equiv _ e.toEquiv
  let _ : IsSimpleGroup H := e.symm.isSimpleGroup
  exact exists_nonempty_mulEquiv_of_mulEquiv e (h H)

/-- A family that classifies the finite simple groups in `Type 0` classifies the finite simple
groups in every universe. This is the direction a consumer of a classification needs. -/
theorem exists_nonempty_mulEquiv_of_forall_type_zero
    (h : ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* Model i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : ∃ i, Nonempty (G ≃* Model i) :=
  exists_nonempty_mulEquiv_of_forall h G

/-- **A classification of the finite simple groups says the same thing in every universe.**

At `u' := 0` this is the comparison with `Type 0`: a development that assumes the classification in
the universe it needs loses nothing by proving it in `Type 0`, and a development that has it in
`Type 0` may apply it anywhere. -/
theorem forall_exists_nonempty_mulEquiv_congr :
    (∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i)) ↔
      ∀ (G : Type u') [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* Model i) :=
  ⟨fun h G _ _ _ => exists_nonempty_mulEquiv_of_forall h G,
    fun h G _ _ _ => exists_nonempty_mulEquiv_of_forall h G⟩

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
