/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.OfQuotient

/-!
# The additive fixed points of a subgroup

Mathlib's `Mathlib/GroupTheory/GroupAction/SubMulAction.lean` and
`Mathlib/GroupTheory/GroupAction/OfQuotient.lean` put a `MulAction G (fixedPoints H α)` and a
`MulAction (G ⧸ H) (fixedPoints H α)` on the fixed points of a normal subgroup `H`, and refine the
latter to a `MulDistribMulAction` on `FixedPoints.subgroup H α`. This file is the additive
counterpart of that refinement: for a distributive action on an additive monoid it upgrades both of
Mathlib's `MulAction`s to `DistribMulAction`s on `FixedPoints.addSubmonoid H M`, records the
coercion lemmas that characterise the two actions on the `AddSubgroup` carrier, and computes the
fixed points of `⊥` and `⊤` together with their monotonicity in the subgroup.

Nothing here is specific to a topology or to cohomology; the continuous-cohomology use is in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Invariants.lean`.

## Main results

* `TauCeti.fixedPoints_bot` and `TauCeti.fixedPoints_top`: the fixed points of the trivial subgroup
  are everything and those of `⊤` are those of the whole group, with their `AddSubgroup` corollaries
  `TauCeti.fixedPoints_addSubgroup_bot` and `TauCeti.fixedPoints_addSubgroup_top`.
* `TauCeti.fixedPoints_addSubgroup_antitone`: the invariants grow as the subgroup shrinks.
* `TauCeti.distribMulActionFixedPointsAddSubmonoid` and
  `TauCeti.distribMulActionQuotientFixedPointsAddSubmonoid`: the distributive `G`- and
  `G ⧸ H`-actions on the fixed points of a normal `H`, with their `AddSubgroup` forms and the
  coercion lemmas `TauCeti.coe_smul_fixedPoints_addSubgroup` and
  `TauCeti.mk_smul_fixedPoints_addSubgroup`.
-/

public section

open MulAction

namespace TauCeti

section FixedPoints

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

/-- The trivial subgroup fixes every point. -/
@[simp]
theorem fixedPoints_bot : fixedPoints (⊥ : Subgroup G) α = Set.univ := by
  ext a
  simp

/-- The points fixed by the subgroup `⊤` are the points fixed by the whole group. -/
@[simp]
theorem fixedPoints_top : fixedPoints (⊤ : Subgroup G) α = fixedPoints G α := by
  ext a
  simp [mem_fixedPoints, Subgroup.smul_def]

end FixedPoints

section AddMonoid

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
variable {H : Subgroup G} [H.Normal]

/-- `M ^ H` is stable under the `G`-action for normal `H`, and the action is distributive: this
adds `smul_zero` and `smul_add` to Mathlib's `MulAction G (fixedPoints H M)`, which has no
multiplicative analogue upstream. -/
instance distribMulActionFixedPointsAddSubmonoid :
    DistribMulAction G (FixedPoints.addSubmonoid H M) where
  __ := (inferInstance : MulAction G (fixedPoints H M))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g a b := Subtype.ext (smul_add g (a : M) (b : M))

/-- `H` acts trivially on `M ^ H`, so the distributive `G`-action descends to `G ⧸ H`: this is the
additive counterpart of Mathlib's `MulDistribMulAction (G ⧸ H) (FixedPoints.submonoid H α)`. -/
instance distribMulActionQuotientFixedPointsAddSubmonoid :
    DistribMulAction (G ⧸ H) (FixedPoints.addSubmonoid H M) where
  __ := (inferInstance : MulAction (G ⧸ H) (fixedPoints H M))
  smul_zero q := q.induction_on fun g ↦ Subtype.ext (smul_zero g)
  smul_add q a b := q.induction_on fun g ↦ Subtype.ext (smul_add g (a : M) (b : M))

end AddMonoid

section AddGroup

variable {G : Type*} [Group G] (M : Type*) [AddGroup M] [DistribMulAction G M]

variable (G) in
/-- The trivial subgroup fixes everything. -/
@[simp]
theorem fixedPoints_addSubgroup_bot : FixedPoints.addSubgroup (⊥ : Subgroup G) M = ⊤ :=
  SetLike.coe_injective <| by rw [AddSubgroup.coe_top]; exact fixedPoints_bot G M

variable (G) in
/-- The invariants of the whole group, reached through the subgroup `⊤`. -/
@[simp]
theorem fixedPoints_addSubgroup_top :
    FixedPoints.addSubgroup (⊤ : Subgroup G) M = FixedPoints.addSubgroup G M :=
  SetLike.coe_injective <| fixedPoints_top G M

/-- The invariants grow as the subgroup shrinks. This is Mathlib's `fixedPoints_subgroup_antitone`
transported across the `SetLike` carrier of `FixedPoints.addSubgroup`, whose underlying set is
`MulAction.fixedPoints` by definition. -/
theorem fixedPoints_addSubgroup_antitone :
    Antitone fun H : Subgroup G ↦ FixedPoints.addSubgroup H M :=
  fun _ _ h ↦ fixedPoints_subgroup_antitone G M h

variable {M}
variable {H : Subgroup G} [H.Normal]

/-- The distributive `G`-action on the invariants of a normal subgroup, on the `AddSubgroup`
carrier. -/
instance distribMulActionFixedPointsAddSubgroup :
    DistribMulAction G (FixedPoints.addSubgroup H M) :=
  inferInstanceAs <| DistribMulAction G (FixedPoints.addSubmonoid H M)

/-- The distributive `G ⧸ H`-action on the invariants of a normal subgroup `H`, on the
`AddSubgroup` carrier. -/
instance distribMulActionQuotientFixedPointsAddSubgroup :
    DistribMulAction (G ⧸ H) (FixedPoints.addSubgroup H M) :=
  inferInstanceAs <| DistribMulAction (G ⧸ H) (FixedPoints.addSubmonoid H M)

/-- The `G`-action on `M ^ H` is the one on `M`. Mathlib's `coe_smul_fixedPoints_of_normal` is
stated for the carrier `↥(fixedPoints H M)` and so does not fire on `FixedPoints.addSubgroup`. -/
@[simp]
theorem coe_smul_fixedPoints_addSubgroup (g : G) (m : FixedPoints.addSubgroup H M) :
    ((g • m : FixedPoints.addSubgroup H M) : M) = g • (m : M) :=
  rfl

/-- The `G ⧸ H`-action on `M ^ H` is the `G`-action through the quotient map. Mathlib's
`coe_quotient_smul_fixedPoints` is stated for the carrier `↥(fixedPoints H M)` and so does not fire
on `FixedPoints.addSubgroup`. -/
@[simp]
theorem mk_smul_fixedPoints_addSubgroup (g : G) (m : FixedPoints.addSubgroup H M) :
    (g : G ⧸ H) • m = g • m :=
  rfl

end AddGroup

end TauCeti
