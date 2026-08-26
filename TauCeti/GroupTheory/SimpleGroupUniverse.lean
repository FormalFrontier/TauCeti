/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Universe lowering for classifications of finite simple groups

Suppose a family `C` contains, up to isomorphism, every finite simple group whose carrier lies in
`Type`. Then it contains every finite simple group in an arbitrary universe.

The reason is specific to finite groups. Mathlib's `Shrink.{0} G` transports the group structure
of a finite group `G : Type u` to a carrier in `Type`, and `Shrink.mulEquiv` identifies the two
groups. Finiteness and simplicity transport to the shrunk carrier, so the small-universe
classification applies there; composing its isomorphism with `Shrink.mulEquiv.symm` returns an
isomorphism from the original group.

The candidate groups are not assumed finite or simple. A classification statement needs only say
that each finite simple group is isomorphic to some candidate; structural properties of the
candidates may be established separately.

## Main result

* `TauCeti.exists_mulEquiv_of_forall_finite_isSimpleGroup_zero`: a classification of groups in
  universe zero by a fixed family holds in every universe.

## Roadmap

This is the universe-transport argument required by milestone A0 of
`TauCetiRoadmap/CFSGStatement/README.md`. Once `CFSGIndex.Group` is assembled, its named theorem
`classificationStatement_of_zero` is the direct specialization to the family
`CFSGIndex.Group`.
-/

public section

namespace TauCeti

universe u v w

/-- **A classification of finite simple groups in universe zero holds in every universe.**

If every finite simple group with carrier in `Type` is isomorphic to a member of a fixed family
`C`, then the same conclusion holds for a finite simple group in any universe. No finiteness or
simplicity assumption is made on the candidate groups themselves. -/
theorem exists_mulEquiv_of_forall_finite_isSimpleGroup_zero
    {ι : Type w} (C : ι → Type v) [∀ i, Group (C i)]
    (hC : ∀ (H : Type) [Group H] [Finite H] [IsSimpleGroup H],
      ∃ i, Nonempty (H ≃* C i))
    (G : Type u) [Group G] [Finite G] [IsSimpleGroup G] :
    ∃ i, Nonempty (G ≃* C i) := by
  let e : Shrink.{0} G ≃* G := Shrink.mulEquiv
  let _ : IsSimpleGroup (Shrink.{0} G) := e.isSimpleGroup
  obtain ⟨i, f⟩ := hC (Shrink.{0} G)
  exact ⟨i, f.map (e.symm.trans ·)⟩

end TauCeti
