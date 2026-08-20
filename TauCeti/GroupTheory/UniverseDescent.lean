/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Universe descent for classification statements

Mathlib's `Finite.exists_type_univ_nonempty_mulEquiv` gives every finite group an isomorphic model
in any prescribed universe. This permits classification statements about finite groups in one
universe to be applied in every universe.

The consequence this file is written for concerns statements of the shape

```text
∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G], ∃ i, Nonempty (G ≃* F i)
```

for a family `F : ι → Type v` carrying multiplications: a family that catches every finite simple
group in one universe catches every finite simple group in every universe, so the proposition does
not depend on the universe it quantifies over. The universe of the family plays no part in this and
is left unrelated to both.

Nothing here is specific to any particular family, and no finiteness or simplicity is asserted of
the members of `F`, which carry only the multiplication that `≃*` needs; the family is arbitrary
data.

## Main results

* `TauCeti.exists_mulEquiv_of_forall_finite` and
  `TauCeti.exists_mulEquiv_of_forall_finite_isSimpleGroup`: a family that catches every finite
  group, respectively every finite simple group, in one universe catches those in every universe.
* `TauCeti.forall_finite_exists_mulEquiv_iff` and
  `TauCeti.forall_finite_isSimpleGroup_exists_mulEquiv_iff`: the resulting universe independence.

## References

Milestone A0 of `TauCetiRoadmap/CFSGStatement/README.md` asks for `classificationStatement_of_zero`,
that `ClassificationStatement.{0}` implies `ClassificationStatement.{u}`, and prescribes the proof
used here: "A finite `G : Type u` is equivalent to `Fin (Nat.card G)`, and its group and simplicity
structure transport along that equivalence." The index family `CFSGIndex.Group` is not yet
available, since it waits on milestone L3, so the transport is proved here for an arbitrary family,
which is all the argument uses; A0 obtains its named target by taking the family to be
`CFSGIndex.Group`.
-/

public section

namespace TauCeti

universe u u₂ v w

section Descent

variable {ι : Sort w} {F : ι → Type v} [∀ i, Mul (F i)]

/-- **Universe descent.** A family that catches every finite group in `Type u₂`, up to
isomorphism, catches every finite group in `Type u`.

The given group is replaced by a small model of it in `Type u₂`, to which the hypothesis applies. -/
theorem exists_mulEquiv_of_forall_finite
    (h : ∀ (H : Type u₂) [Group H] [Finite H], ∃ i, Nonempty (H ≃* F i))
    (G : Type u) [Group G] [Finite G] : ∃ i, Nonempty (G ≃* F i) := by
  obtain ⟨H, groupH, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, u₂} G
  let _ := groupH
  have : Finite H := .of_equiv G e.toEquiv
  obtain ⟨i, ⟨f⟩⟩ := h H
  exact ⟨i, ⟨e.trans f⟩⟩

/-- **Universe independence.** Whether a family catches every finite group up to isomorphism does
not depend on the universe the statement quantifies over.

Both directions are `TauCeti.exists_mulEquiv_of_forall_finite`, which relates two unrelated
universes rather than descending along an inclusion. -/
theorem forall_finite_exists_mulEquiv_iff :
    (∀ (G : Type u) [Group G] [Finite G], ∃ i, Nonempty (G ≃* F i)) ↔
      ∀ (G : Type u₂) [Group G] [Finite G], ∃ i, Nonempty (G ≃* F i) :=
  ⟨fun h _ _ _ => exists_mulEquiv_of_forall_finite h _,
    fun h _ _ _ => exists_mulEquiv_of_forall_finite h _⟩

/-- **Universe descent for a classification statement.** A family that catches every finite simple
group in `Type u₂`, up to isomorphism, catches every finite simple group in `Type u`.

This is not a consequence of `TauCeti.exists_mulEquiv_of_forall_finite`, whose hypothesis is about
all finite groups and is therefore strictly stronger: simplicity has to be carried across the
isomorphism with the small model instead. -/
theorem exists_mulEquiv_of_forall_finite_isSimpleGroup
    (h : ∀ (H : Type u₂) [Group H] [Finite H] [IsSimpleGroup H], ∃ i, Nonempty (H ≃* F i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] : ∃ i, Nonempty (G ≃* F i) := by
  obtain ⟨H, groupH, _, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u, u₂} G
  let _ := groupH
  have : Finite H := .of_equiv G e.toEquiv
  have : IsSimpleGroup H := e.symm.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := h H
  exact ⟨i, ⟨e.trans f⟩⟩

/-- **Universe independence.** Whether a family catches every finite simple group up to
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
