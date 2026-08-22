/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Submonoid
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.GroupAction.OfQuotient

/-!
# The additive fixed points of a subgroup

Mathlib's `Mathlib/GroupTheory/GroupAction/SubMulAction.lean` and
`Mathlib/GroupTheory/GroupAction/OfQuotient.lean` put a `MulAction G (fixedPoints H α)` and a
`MulAction (G ⧸ H) (fixedPoints H α)` on the fixed points of a normal subgroup `H`, and refine the
latter to a `MulDistribMulAction` on `FixedPoints.subgroup H α`. This file is the additive
counterpart of that refinement: for a distributive action on an additive monoid it upgrades both of
Mathlib's `MulAction`s to `DistribMulAction`s on `FixedPoints.addSubmonoid H M`, records the
coercion lemmas that characterise the two actions on the `AddSubgroup` carrier, computes the fixed
points of `⊥` and `⊤`, and supplies the inclusion and map API for additive fixed points.

Nothing here is specific to a topology or to cohomology; the continuous-cohomology use is in
`TauCeti/RepresentationTheory/Homological/ContCohomology/Invariants.lean`.

## Main results

* `TauCeti.fixedPoints_bot` and `TauCeti.fixedPoints_top`: the fixed points of the trivial subgroup
  are everything and those of `⊤` are those of the whole group, with their `AddSubgroup`
  corollaries and the trivial-action and subsingleton-coefficient edge cases.
* `TauCeti.distribMulActionFixedPointsAddSubmonoid` and
  `TauCeti.distribMulActionQuotientFixedPointsAddSubmonoid`: the distributive `G`- and
  `G ⧸ H`-actions on the fixed points of a normal `H`, with their `AddSubgroup` forms and the
  coercion lemmas `TauCeti.coe_smul_fixedPoints_addSubgroup` and
  `TauCeti.coe_quotient_smul_fixedPoints_addSubgroup`.
* `TauCeti.fixedPointsInclusion`, `TauCeti.fixedPointsDistribMulActionInclusion`, and
  `TauCeti.fixedPointsDistribMulActionSubtype`: the additive and equivariant inclusions between
  fixed points and into the ambient additive monoid, with their functoriality laws.
* `TauCeti.fixedPointsMap` and `TauCeti.fixedPointsQuotientMap`: functoriality of fixed points in
  the additive monoid, additively and as a quotient-equivariant map.
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

/-- The `G`-action on the fixed-point additive submonoid is the one on `M`. -/
@[simp]
theorem coe_smul_fixedPoints_addSubmonoid (g : G) (m : FixedPoints.addSubmonoid H M) :
    ((g • m : FixedPoints.addSubmonoid H M) : M) = g • (m : M) :=
  rfl

/-- The `G ⧸ H`-action on the fixed-point additive submonoid is induced by the `G`-action. -/
@[simp]
theorem coe_quotient_smul_fixedPoints_addSubmonoid (g : G)
    (m : FixedPoints.addSubmonoid H M) : (g : G ⧸ H) • m = g • m :=
  rfl

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

/-- If the `G`-action on `M` is trivial, every element is fixed by every subgroup. -/
@[simp]
theorem fixedPoints_addSubgroup_eq_top_of_smul_eq (H : Subgroup G)
    (h : ∀ (g : G) (m : M), g • m = m) : FixedPoints.addSubgroup H M = ⊤ := by
  ext m
  simp [h]

/-- The fixed-point subgroup of a subsingleton additive group is zero. -/
@[simp]
theorem fixedPoints_addSubgroup_eq_bot_of_subsingleton [Subsingleton M] (H : Subgroup G) :
    FixedPoints.addSubgroup H M = ⊥ :=
  Subsingleton.elim _ _

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
theorem coe_quotient_smul_fixedPoints_addSubgroup (g : G)
    (m : FixedPoints.addSubgroup H M) :
    (g : G ⧸ H) • m = g • m :=
  rfl

end AddGroup

section Functoriality

variable {G : Type*} [Group G] {M : Type*} [AddMonoid M] [DistribMulAction G M]
variable {H K : Subgroup G}

/-- For `K ≤ H`, the fixed points of `H` include into the fixed points of `K`. This is stated on
additive submonoids so that it applies before additive inverses are available. -/
def fixedPointsInclusion (h : K ≤ H) :
    FixedPoints.addSubmonoid H M →+ FixedPoints.addSubmonoid K M :=
  AddSubmonoid.inclusion (fixedPoints_subgroup_antitone G M h)

/-- The fixed-point inclusion does not move an element of `M`. -/
@[simp]
theorem coe_fixedPointsInclusion (h : K ≤ H) (m : FixedPoints.addSubmonoid H M) :
    (fixedPointsInclusion h m : M) = (m : M) :=
  AddSubmonoid.coe_inclusion _ m

/-- The fixed-point inclusions are injective. -/
theorem fixedPointsInclusion_injective (h : K ≤ H) :
    Function.Injective (fixedPointsInclusion (M := M) h) :=
  AddSubmonoid.inclusion_injective _

/-- The fixed-point inclusion is `G`-equivariant. -/
@[simp]
theorem fixedPointsInclusion_smul [H.Normal] [K.Normal] (h : K ≤ H) (g : G)
    (m : FixedPoints.addSubmonoid H M) :
    fixedPointsInclusion h (g • m) = g • fixedPointsInclusion h m :=
  Subtype.ext <| by simp

/-- For normal `H` and `K`, fixed-point inclusion is a `G`-equivariant additive map. -/
def fixedPointsDistribMulActionInclusion [H.Normal] [K.Normal] (h : K ≤ H) :
    FixedPoints.addSubmonoid H M →+[G] FixedPoints.addSubmonoid K M where
  toAddMonoidHom := fixedPointsInclusion h
  map_smul' := fixedPointsInclusion_smul h

/-- The `G`-equivariant inclusion of the fixed points of a normal subgroup into `M`. -/
def fixedPointsDistribMulActionSubtype (H : Subgroup G) [H.Normal] :
    FixedPoints.addSubmonoid H M →+[G] M where
  toAddMonoidHom := AddSubmonoid.subtype _
  map_smul' _ _ := rfl

/-- The equivariant fixed-point inclusion does not move an element of `M`. -/
@[simp]
theorem coe_fixedPointsDistribMulActionInclusion [H.Normal] [K.Normal] (h : K ≤ H)
    (m : FixedPoints.addSubmonoid H M) :
    (fixedPointsDistribMulActionInclusion h m : M) = (m : M) :=
  coe_fixedPointsInclusion h m

/-- The equivariant fixed-point subtype map does not move an element of `M`. -/
@[simp]
theorem fixedPointsDistribMulActionSubtype_apply (H : Subgroup G) [H.Normal]
    (m : FixedPoints.addSubmonoid H M) : fixedPointsDistribMulActionSubtype H m = (m : M) :=
  congrFun (AddSubmonoid.coe_subtype (FixedPoints.addSubmonoid H M)) m

/-- The fixed-point inclusion is equivariant along Mathlib's canonical quotient homomorphism
`G ⧸ K →* G ⧸ H`. -/
@[simp]
theorem fixedPointsInclusion_quotientGroupMap_smul [H.Normal] [K.Normal] (h : K ≤ H) (q : G ⧸ K)
    (m : FixedPoints.addSubmonoid H M) :
    fixedPointsInclusion h
        ((QuotientGroup.map K H (MonoidHom.id G) (h.trans_eq (Subgroup.comap_id H).symm) q) • m) =
      q • fixedPointsInclusion h m := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

variable (M) in
/-- The fixed-point inclusions are functorial in the subgroup: the identity inclusion is the
identity. -/
@[simp]
theorem fixedPointsInclusion_self (H : Subgroup G) :
    fixedPointsInclusion (M := M) (le_refl H) = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun m ↦ Subtype.ext (coe_fixedPointsInclusion _ m)

/-- The fixed-point inclusions are functorial in the subgroup: they compose. -/
@[simp]
theorem fixedPointsInclusion_comp_fixedPointsInclusion {L : Subgroup G} (h : K ≤ H) (h' : L ≤ K) :
    (fixedPointsInclusion (M := M) h').comp (fixedPointsInclusion h) =
      fixedPointsInclusion (h'.trans h) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

section Map

variable {N : Type*} [AddMonoid N] [DistribMulAction G N]

/-- A `G`-equivariant additive map restricts to the fixed points of any subgroup. -/
def fixedPointsMap (f : M →+[G] N) (H : Subgroup G) :
    FixedPoints.addSubmonoid H M →+ FixedPoints.addSubmonoid H N where
  toFun m := ⟨f (m : M), f.toMulActionHom.map_mem_fixedPoints (H := H.toSubmonoid) m.2⟩
  map_zero' := Subtype.ext (map_zero f)
  map_add' a b := Subtype.ext (map_add f (a : M) (b : M))

/-- The restricted map is the original map on underlying elements. -/
@[simp]
theorem coe_fixedPointsMap (f : M →+[G] N) (H : Subgroup G)
    (m : FixedPoints.addSubmonoid H M) :
    (fixedPointsMap f H m : N) = f (m : M) := by
  rfl

/-- Restriction to fixed points preserves the identity map. -/
@[simp]
theorem fixedPointsMap_id (H : Subgroup G) :
    fixedPointsMap (DistribMulActionHom.id G : M →+[G] M) H = AddMonoidHom.id _ :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to fixed points preserves composition. -/
@[simp]
theorem fixedPointsMap_comp_fixedPointsMap {P : Type*} [AddMonoid P] [DistribMulAction G P]
    (f : M →+[G] N) (f' : N →+[G] P) (H : Subgroup G) :
    (fixedPointsMap f' H).comp (fixedPointsMap f H) = fixedPointsMap (f'.comp f) H :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to the fixed points is equivariant for the `G`-actions of a normal subgroup. -/
@[simp]
theorem fixedPointsMap_smul (f : M →+[G] N) (H : Subgroup G) [H.Normal] (g : G)
    (m : FixedPoints.addSubmonoid H M) :
    fixedPointsMap f H (g • m) = g • fixedPointsMap f H m :=
  Subtype.ext <| by simp

/-- Restriction to the fixed points is equivariant for the `G ⧸ H`-actions. -/
@[simp]
theorem fixedPointsMap_quotient_smul (f : M →+[G] N) (H : Subgroup G) [H.Normal] (q : G ⧸ H)
    (m : FixedPoints.addSubmonoid H M) :
    fixedPointsMap f H (q • m) = q • fixedPointsMap f H m := by
  induction q using QuotientGroup.induction_on with
  | H g => simp

/-- For normal `H`, restriction to the fixed points is a `G ⧸ H`-equivariant additive map. -/
def fixedPointsQuotientMap (f : M →+[G] N) (H : Subgroup G) [H.Normal] :
    FixedPoints.addSubmonoid H M →+[G ⧸ H] FixedPoints.addSubmonoid H N where
  toAddMonoidHom := fixedPointsMap f H
  map_smul' := fixedPointsMap_quotient_smul f H

/-- The quotient-equivariant map is the original map on underlying elements. -/
@[simp]
theorem coe_fixedPointsQuotientMap (f : M →+[G] N) (H : Subgroup G) [H.Normal]
    (m : FixedPoints.addSubmonoid H M) :
    (fixedPointsQuotientMap f H m : N) = f (m : M) := by
  rfl

/-- Quotient-equivariant restriction to fixed points preserves the identity map. -/
@[simp]
theorem fixedPointsQuotientMap_id (H : Subgroup G) [H.Normal] :
    fixedPointsQuotientMap (DistribMulActionHom.id G : M →+[G] M) H =
      DistribMulActionHom.id (G ⧸ H) :=
  DistribMulActionHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Quotient-equivariant restriction to fixed points preserves composition. -/
@[simp]
theorem fixedPointsQuotientMap_comp_fixedPointsQuotientMap {P : Type*} [AddMonoid P]
    [DistribMulAction G P] (f : M →+[G] N) (f' : N →+[G] P) (H : Subgroup G) [H.Normal] :
    (fixedPointsQuotientMap f' H).comp (fixedPointsQuotientMap f H) =
      fixedPointsQuotientMap (f'.comp f) H :=
  DistribMulActionHom.ext fun _ ↦ Subtype.ext <| by simp

/-- Restriction to the fixed points commutes with the fixed-point inclusions. -/
@[simp]
theorem fixedPointsMap_comp_fixedPointsInclusion (f : M →+[G] N) (h : K ≤ H) :
    (fixedPointsMap f K).comp (fixedPointsInclusion h) =
      (fixedPointsInclusion h).comp (fixedPointsMap f H) :=
  AddMonoidHom.ext fun _ ↦ Subtype.ext <| by simp

end Map

end Functoriality

end TauCeti
