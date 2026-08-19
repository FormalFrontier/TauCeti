/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Group.ULift
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Small models of finite groups, and universe descent for classification statements

A finite group `G : Type u` is equivalent, as a type, to `Fin (Nat.card G)`, which lives in
`Type`. Transporting the multiplication along that equivalence produces a group isomorphic to `G`
whose carrier can be placed in any universe at all.

The consequence this file is written for concerns statements of the shape

```text
∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* F i)
```

for a family `F : ι → Type v` of groups: a list of groups that catches every finite simple group
in one universe catches every finite simple group in every universe, so the proposition does not
depend on the universe it quantifies over. The universe of the family plays no part in this and is
left unrelated to both.

Nothing here is specific to any particular family, and no finiteness or simplicity is asserted of
the members of `F`; the family is arbitrary data.

## Main definitions

* `TauCeti.FinModel` and `TauCeti.finModelEquiv`: the carrier `ULift (Fin (Nat.card G))` of the
  small model of a finite type, and the numbering identifying it with the type.
* `TauCeti.finModelGroup` and `TauCeti.finModelMulEquiv`: the group structure the numbering
  transports onto the small model, and the resulting isomorphism.

## Main results

* `TauCeti.card_finModel`: the small model has the same cardinality as the type it models.
* `TauCeti.exists_group_mulEquiv`: every finite group is isomorphic to a group carried by a type in
  any prescribed universe.
* `TauCeti.exists_mulEquiv_of_forall_finite` and
  `TauCeti.exists_mulEquiv_of_forall_finite_isSimpleGroup`: a family that catches every finite
  group, respectively every finite simple group, in one universe catches those in every universe.
* `TauCeti.forall_finite_isSimpleGroup_exists_mulEquiv_iff`: the resulting universe independence.

## References

Milestone A0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for `classificationStatement_of_zero`,
that `ClassificationStatement.{0}` implies `ClassificationStatement.{u}`, and prescribes the proof
used here: "A finite `G : Type u` is equivalent to `Fin (Nat.card G)`, and its group and simplicity
structure transport along that equivalence." The index family `CFSGIndex.Group` is not yet
available, since it waits on milestone L3, so the transport is proved here for an arbitrary family
of groups, which is all the argument uses; A0 obtains its named target by taking the family to be
`CFSGIndex.Group`.
-/

public section

namespace TauCeti

universe u u₂ v w

section FinModel

variable (G : Type u) [Finite G]

/-- The carrier of the small model of a finite type in a prescribed universe: the elements of `G`
numbered by its own cardinality, lifted out of `Type`.

It is a plain definition rather than an abbreviation so that instance search does not see through
it to the integers modulo `Nat.card G`, whose group structure has nothing to do with the one
transported below. -/
def FinModel : Type v := ULift (Fin (Nat.card G))

/-- The numbering of a finite type by its own cardinality, as an equivalence
`FinModel G ≃ G`.

This is the only choice the small model makes: the group structure and the isomorphism below are
transported along it, and no group is selected from an existence theorem. -/
noncomputable def finModelEquiv : FinModel.{u, v} G ≃ G :=
  Equiv.ulift.trans (Finite.equivFin G).symm

instance : Finite (FinModel.{u, v} G) :=
  .of_equiv G (finModelEquiv G).symm

/-- The small model has the same cardinality as the type it models. -/
@[simp]
theorem card_finModel : Nat.card (FinModel.{u, v} G) = Nat.card G :=
  Nat.card_congr (finModelEquiv G)

variable [Group G]

/-- The group structure that `TauCeti.finModelEquiv` transports from a finite group onto its small
model.

This is deliberately not an instance: the modelled group cannot be recovered from the carrier, since
`Nat.card G` determines `G` neither mathematically nor by unification. -/
noncomputable abbrev finModelGroup : Group (FinModel.{u, v} G) :=
  (finModelEquiv G).group

/-- The small model of a finite group is isomorphic to it. -/
@[expose] noncomputable def finModelMulEquiv :
    let _ := finModelGroup.{u, v} G
    FinModel.{u, v} G ≃* G := by
  intros
  exact Equiv.mulEquiv (finModelEquiv G)

/-- The isomorphism with the small model is the chosen numbering, with no further bookkeeping. -/
@[simp]
theorem finModelMulEquiv_apply (x : FinModel.{u, v} G) :
    letI := finModelGroup.{u, v} G
    finModelMulEquiv G x = finModelEquiv G x :=
  rfl

/-- Every finite group is isomorphic to a group carried by a type in any prescribed universe.

The carrier is the explicit small model `ULift (Fin (Nat.card G))`, not a type extracted from a
smallness argument. -/
theorem exists_group_mulEquiv : ∃ (H : Type v) (_ : Group H), Nonempty (G ≃* H) := by
  let _ := finModelGroup.{u, v} G
  exact ⟨FinModel.{u, v} G, inferInstance, ⟨(finModelMulEquiv G).symm⟩⟩

end FinModel

section Descent

variable {ι : Sort w} {F : ι → Type v} [∀ i, Group (F i)]

/-- **Universe descent.** A family of groups that catches every finite group in `Type u₂`, up to
isomorphism, catches every finite group in `Type u`.

The given group is replaced by a small model of it in `Type u₂`, to which the hypothesis applies. -/
theorem exists_mulEquiv_of_forall_finite
    (h : ∀ (H : Type u₂) [Group H] [Finite H], ∃ i, Nonempty (H ≃* F i))
    (G : Type u) [Group G] [Finite G] : ∃ i, Nonempty (G ≃* F i) := by
  obtain ⟨H, _, ⟨e⟩⟩ : ∃ (H : Type u₂) (_ : Group H), Nonempty (G ≃* H) :=
    exists_group_mulEquiv G
  have : Finite H := .of_equiv G e.toEquiv
  obtain ⟨i, ⟨f⟩⟩ := h H
  exact ⟨i, ⟨e.trans f⟩⟩

/-- **Universe descent for a classification statement.** A family of groups that catches every
finite simple group in `Type u₂`, up to isomorphism, catches every finite simple group in `Type u`.

This is not a consequence of `TauCeti.exists_mulEquiv_of_forall_finite`, whose hypothesis is about
all finite groups and is therefore strictly stronger: simplicity has to be carried across the
isomorphism with the small model instead. -/
theorem exists_mulEquiv_of_forall_finite_isSimpleGroup
    (h : ∀ (H : Type u₂) [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* F i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : ∃ i, Nonempty (G ≃* F i) := by
  obtain ⟨H, _, ⟨e⟩⟩ : ∃ (H : Type u₂) (_ : Group H), Nonempty (G ≃* H) :=
    exists_group_mulEquiv G
  have : Finite H := .of_equiv G e.toEquiv
  have : IsSimpleGroup H := e.symm.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := h H
  exact ⟨i, ⟨e.trans f⟩⟩

/-- **Universe independence.** Whether a family of groups catches every finite simple group up to
isomorphism does not depend on the universe the statement quantifies over.

Both directions are `TauCeti.exists_mulEquiv_of_forall_finite_isSimpleGroup`, which relates two
unrelated universes rather than descending along an inclusion. -/
theorem forall_finite_isSimpleGroup_exists_mulEquiv_iff :
    (∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* F i)) ↔
      ∀ (G : Type u₂) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* F i) :=
  ⟨fun h _ _ _ _ => exists_mulEquiv_of_forall_finite_isSimpleGroup h _,
    fun h _ _ _ _ => exists_mulEquiv_of_forall_finite_isSimpleGroup h _⟩

end Descent

end TauCeti
