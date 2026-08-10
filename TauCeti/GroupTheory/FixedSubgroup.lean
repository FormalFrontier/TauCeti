/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The fixed points of an endomorphism

Let `F` be an endomorphism of a group `G`. This file studies the subgroup

```text
fixedSubgroup F = F.eqLocus (MonoidHom.id G)
```

of points of `G` fixed by `F`: when it is everything, how it grows along the powers of `F`, and how
it transports along an isomorphism intertwining two endomorphisms.

Nothing here is specific to any particular endomorphism: the material needs only a group and an
endomorphism of it, so it is available before any ambient group has been constructed.

## Main definitions

* `TauCeti.fixedSubgroup`: the subgroup of points fixed by an endomorphism.
* `TauCeti.fixedSubgroupCongr`: transport along an isomorphism intertwining two endomorphisms.

## Main results

* `TauCeti.fixedSubgroup_eq_top_iff`: only the identity fixes every point.
* `TauCeti.fixedSubgroup_le_fixedSubgroup_pow`: a point fixed by an endomorphism is fixed by each of
  its powers.
* `TauCeti.map_fixedSubgroup`: an isomorphism intertwining two endomorphisms carries fixed points
  onto fixed points; `TauCeti.fixedSubgroupCongr_refl`, `TauCeti.fixedSubgroupCongr_symm` and
  `TauCeti.fixedSubgroupCongr_trans` are the coherence laws of the resulting transport.

## References

The fixed subgroup in the form `F.eqLocus (MonoidHom.id G)` is what milestone L3 of
`TauCetiRoadmap/CFSGStatement/README.md` prescribes for the fixed points of a Steinberg
endomorphism. The construction is standard; see R. W. Carter, *Simple Groups of Lie Type*.
-/

public section

namespace TauCeti

open Subgroup

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

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

/-! ## Transport along an intertwining isomorphism -/

/-- An isomorphism carrying `F` to `F'` has an inverse carrying `F'` back to `F`. -/
theorem symm_intertwines (e : G ≃* G') {F : G →* G} {F' : G' →* G'} (h : ∀ x, F' (e x) = e (F x))
    (y : G') : F (e.symm y) = e.symm (F' y) := by
  rw [eq_comm, MulEquiv.symm_apply_eq, ← h (e.symm y), MulEquiv.apply_symm_apply]

/-- Isomorphisms carrying `F` to `F'` and `F'` to `F''` compose to one carrying `F` to `F''`. -/
theorem trans_intertwines (e : G ≃* G') (e' : G' ≃* G'') {F : G →* G} {F' : G' →* G'}
    {F'' : G'' →* G''} (h : ∀ x, F' (e x) = e (F x)) (h' : ∀ y, F'' (e' y) = e' (F' y)) (x : G) :
    F'' ((e.trans e') x) = (e.trans e') (F x) := by
  simp only [MulEquiv.trans_apply, h', h]

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

/-- The isomorphism of fixed subgroups induced by an intertwining isomorphism. -/
def fixedSubgroupCongr (e : G ≃* G') {F : G →* G} {F' : G' →* G'} (h : ∀ x, F' (e x) = e (F x)) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup F') :=
  (e.subgroupMap (fixedSubgroup F)).trans (MulEquiv.subgroupCongr (map_fixedSubgroup e h))

@[simp]
theorem fixedSubgroupCongr_coe (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) (x : ↥(fixedSubgroup F)) :
    ((fixedSubgroupCongr e h x : ↥(fixedSubgroup F')) : G') = e (x : G) := by
  simp only [fixedSubgroupCongr, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

@[simp]
theorem fixedSubgroupCongr_refl {F : G →* G}
    (h : ∀ x, F (MulEquiv.refl G x) = MulEquiv.refl G (F x)) :
    fixedSubgroupCongr (MulEquiv.refl G) h = MulEquiv.refl ↥(fixedSubgroup F) :=
  MulEquiv.ext fun x =>
    Subtype.ext (by simp only [fixedSubgroupCongr_coe, MulEquiv.refl_apply])

@[simp]
theorem fixedSubgroupCongr_symm (e : G ≃* G') {F : G →* G} {F' : G' →* G'}
    (h : ∀ x, F' (e x) = e (F x)) :
    (fixedSubgroupCongr e h).symm = fixedSubgroupCongr e.symm (symm_intertwines e h) :=
  MulEquiv.ext fun y =>
    (fixedSubgroupCongr e h).symm_apply_eq.mpr
      (Subtype.ext (by simp only [fixedSubgroupCongr_coe, MulEquiv.apply_symm_apply]))

@[simp]
theorem fixedSubgroupCongr_trans (e : G ≃* G') (e' : G' ≃* G'') {F : G →* G} {F' : G' →* G'}
    {F'' : G'' →* G''} (h : ∀ x, F' (e x) = e (F x)) (h' : ∀ y, F'' (e' y) = e' (F' y)) :
    (fixedSubgroupCongr e h).trans (fixedSubgroupCongr e' h') =
      fixedSubgroupCongr (e.trans e') (trans_intertwines e e' h h') :=
  MulEquiv.ext fun x =>
    Subtype.ext (by simp only [MulEquiv.trans_apply, fixedSubgroupCongr_coe])

end TauCeti
