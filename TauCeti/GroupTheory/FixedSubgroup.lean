/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The fixed points of an endomorphism

Let `F` be an endomorphism of a group `G`. This file studies the subgroup

```text
fixedSubgroup F = F.eqLocus (MonoidHom.id G)
```

of points of `G` fixed by `F`: when it is everything, how it grows along the powers of `F`, and how
it transports along an isomorphism of the ambient group.

An isomorphism `ψ : G ≃* G'` *intertwines* `F` with an endomorphism `F'` of `G'` when
`ψ ∘ F = F' ∘ ψ`. Such a `ψ` carries `fixedSubgroup F` onto `fixedSubgroup F'`, so the pair
`(G, F)` determines its fixed subgroup up to isomorphism and not merely up to inclusion. The
one-sided statement for a homomorphism is `TauCeti.map_fixedSubgroup_le`; the two-sided statements
are `TauCeti.map_fixedSubgroup_eq` and `TauCeti.fixedSubgroupCongr`.

Nothing here is specific to any particular endomorphism: the material needs only a group and an
endomorphism of it, so it is available before any ambient group has been constructed.

## Main definitions and results

* `TauCeti.fixedSubgroup`: the subgroup of points fixed by an endomorphism.
* `TauCeti.fixedSubgroup_eq_top_iff`: only the identity fixes every point.
* `TauCeti.fixedSubgroup_le_fixedSubgroup_pow`: a point fixed by an endomorphism is fixed by each of
  its powers.
* `TauCeti.map_fixedSubgroup_le`: a homomorphism intertwining two endomorphisms carries the points
  fixed by the one to the points fixed by the other.
* `TauCeti.map_fixedSubgroup_eq`: an isomorphism intertwining them carries the one *onto* the other.
* `TauCeti.fixedSubgroupCongr`: the resulting isomorphism of fixed subgroups.

## References

The fixed subgroup in the form `F.eqLocus (MonoidHom.id G)` is what milestone L3 of
`TauCetiRoadmap/CFSGStatement/README.md` prescribes for the fixed points of a Steinberg
endomorphism. The construction is standard; see R. W. Carter, *Simple Groups of Lie Type*.
-/

public section

namespace TauCeti

open Subgroup

variable {G : Type*} [Group G]

/-- The subgroup of points fixed by an endomorphism of a group, `F.eqLocus (MonoidHom.id G)`. -/
abbrev fixedSubgroup (F : G →* G) : Subgroup G := F.eqLocus (MonoidHom.id G)

@[simp]
theorem mem_fixedSubgroup {F : G →* G} {x : G} : x ∈ fixedSubgroup F ↔ F x = x := Iff.rfl

/-- Only the identity fixes every point. -/
theorem fixedSubgroup_eq_top_iff {F : G →* G} : fixedSubgroup F = ⊤ ↔ F = MonoidHom.id G := by
  constructor
  · refine fun h => MonoidHom.ext fun x => ?_
    exact mem_fixedSubgroup.mp (h ▸ mem_top x)
  · rintro rfl
    exact MonoidHom.eqLocus_same _

private theorem mem_fixedSubgroup_end_pow_iff (F : Monoid.End G) (n : ℕ) (x : G) :
    x ∈ fixedSubgroup ((F ^ n : Monoid.End G) : G →* G) ↔ F^[n] x = x := Iff.rfl

private theorem mem_fixedSubgroup_pow_of_mem (F : Monoid.End G) (n : ℕ) (x : G)
    (hx : x ∈ fixedSubgroup (F : G →* G)) :
    x ∈ fixedSubgroup ((F ^ n : Monoid.End G) : G →* G) :=
  (mem_fixedSubgroup_end_pow_iff F n x).mpr
    (Function.iterate_fixed ((mem_fixedSubgroup (F := (F : G →* G))).mp hx) n)

/-- A point fixed by an endomorphism is fixed by each of its powers.

The Suzuki--Ree Steinberg maps are odd powers of a half-Frobenius whose square is a Frobenius, so
this is what places their fixed groups inside the fixed group of the corresponding untwisted
Frobenius. -/
theorem fixedSubgroup_le_fixedSubgroup_pow (F : Monoid.End G) (n : ℕ) :
    fixedSubgroup (F : G →* G) ≤ fixedSubgroup ((F ^ n : Monoid.End G) : G →* G) :=
  mem_fixedSubgroup_pow_of_mem F n

variable {G' : Type*} [Group G']

/-- A homomorphism intertwining two endomorphisms carries the points fixed by the one to the points
fixed by the other. -/
theorem map_fixedSubgroup_le {F : G →* G} {F' : G' →* G'} (ψ : G →* G')
    (hψ : ψ.comp F = F'.comp ψ) : (fixedSubgroup F).map ψ ≤ fixedSubgroup F' := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixedSubgroup, ← MonoidHom.comp_apply, ← hψ, MonoidHom.comp_apply,
    mem_fixedSubgroup.mp hx]

/-! ### Transport along an isomorphism of the ambient group -/

variable {F : G →* G} {F' : G' →* G'}

/-- An isomorphism intertwining two endomorphisms has an inverse intertwining them the other way.

The equation is not symmetric in `ψ` and `ψ.symm`, so this is what makes the transport of the fixed
subgroup two-sided. -/
theorem _root_.MulEquiv.symm_comp_eq_comp_symm (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (ψ.symm : G' →* G).comp F' = F.comp (ψ.symm : G' →* G) := by
  ext y
  apply ψ.injective
  simpa using (DFunLike.congr_fun hψ (ψ.symm y)).symm

variable {G'' : Type*} [Group G''] {F'' : G'' →* G''}

/-- Intertwining relations compose. -/
theorem _root_.MulEquiv.trans_comp_eq_comp_trans {ψ : G ≃* G'} {χ : G' ≃* G''}
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G'))
    (hχ : (χ : G' →* G'').comp F' = F''.comp (χ : G' →* G'')) :
    ((ψ.trans χ : G ≃* G'') : G →* G'').comp F = F''.comp ((ψ.trans χ : G ≃* G'') : G →* G'') := by
  ext x
  have h₁ : ψ (F x) = F' (ψ x) := DFunLike.congr_fun hψ x
  have h₂ : χ (F' (ψ x)) = F'' (χ (ψ x)) := DFunLike.congr_fun hχ (ψ x)
  change χ (ψ (F x)) = F'' (χ (ψ x))
  rw [h₁, h₂]

/-- An isomorphism intertwining two endomorphisms carries the points fixed by the one *onto* the
points fixed by the other. -/
theorem map_fixedSubgroup_eq (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (fixedSubgroup F).map (ψ : G →* G') = fixedSubgroup F' :=
  le_antisymm (map_fixedSubgroup_le _ hψ) fun y hy =>
    ⟨ψ.symm y,
      map_fixedSubgroup_le (ψ.symm : G' →* G) (MulEquiv.symm_comp_eq_comp_symm ψ hψ) ⟨y, hy, rfl⟩,
      ψ.apply_symm_apply y⟩

/-- The isomorphism of fixed subgroups induced by an isomorphism intertwining the two
endomorphisms. -/
def fixedSubgroupCongr (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup F') :=
  (ψ.subgroupMap (fixedSubgroup F)).trans (MulEquiv.subgroupCongr (map_fixedSubgroup_eq ψ hψ))

@[simp]
theorem coe_fixedSubgroupCongr_apply (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (x : ↥(fixedSubgroup F)) :
    (fixedSubgroupCongr ψ hψ x : G') = ψ (x : G) := by
  simp only [fixedSubgroupCongr, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

@[simp]
theorem coe_fixedSubgroupCongr_symm_apply (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (y : ↥(fixedSubgroup F')) :
    ((fixedSubgroupCongr ψ hψ).symm y : G) = ψ.symm (y : G') := by
  simp only [fixedSubgroupCongr, MulEquiv.symm_trans_apply, MulEquiv.subgroupCongr_symm_apply,
    MulEquiv.subgroupMap_symm_apply]

@[simp]
theorem fixedSubgroupCongr_refl
    (hψ : (MulEquiv.refl G : G →* G).comp F = F.comp (MulEquiv.refl G : G →* G)) :
    fixedSubgroupCongr (MulEquiv.refl G) hψ = MulEquiv.refl ↥(fixedSubgroup F) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

theorem fixedSubgroupCongr_trans (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (χ : G' ≃* G'')
    (hχ : (χ : G' →* G'').comp F' = F''.comp (χ : G' →* G'')) :
    (fixedSubgroupCongr ψ hψ).trans (fixedSubgroupCongr χ hχ) =
      fixedSubgroupCongr (ψ.trans χ) (MulEquiv.trans_comp_eq_comp_trans hψ hχ) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

theorem fixedSubgroupCongr_symm (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (fixedSubgroupCongr ψ hψ).symm =
      fixedSubgroupCongr ψ.symm (MulEquiv.symm_comp_eq_comp_symm ψ hψ) :=
  MulEquiv.ext fun _ => Subtype.ext (by simp)

/-! ### Transporting the endomorphism as well

A consumer usually has an isomorphism `ψ : G ≃* G'` and an endomorphism of `G`, and no candidate
`F'` in hand. Conjugating `F` by `ψ` supplies one, and it is the only choice: `ψ` intertwines `F`
with `F'` exactly when `F'` is that conjugate. -/

/-- The endomorphism of `G'` obtained by conjugating an endomorphism of `G` by an isomorphism. -/
def _root_.MulEquiv.endCongr (ψ : G ≃* G') : (G →* G) ≃ (G' →* G') :=
  (MulEquiv.monoidHomCongrLeftEquiv (N := G) ψ).trans (MulEquiv.monoidHomCongrRightEquiv ψ)

@[simp]
theorem _root_.MulEquiv.endCongr_apply (ψ : G ≃* G') (F : G →* G) (y : G') :
    MulEquiv.endCongr ψ F y = ψ (F (ψ.symm y)) := by
  simp only [MulEquiv.endCongr, Equiv.trans_apply, MulEquiv.monoidHomCongrLeftEquiv_apply,
    MulEquiv.monoidHomCongrRightEquiv_apply, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom]

/-- An isomorphism intertwines an endomorphism with its own conjugate. -/
theorem _root_.MulEquiv.comp_eq_endCongr_comp (ψ : G ≃* G') (F : G →* G) :
    (ψ : G →* G').comp F = (MulEquiv.endCongr ψ F).comp (ψ : G →* G') := by
  ext x
  simp

/-- An isomorphism intertwines `F` with `F'` exactly when `F'` is the conjugate of `F`, so no
generality is lost by conjugating. -/
theorem _root_.MulEquiv.comp_eq_comp_iff_eq_endCongr (ψ : G ≃* G') :
    (ψ : G →* G').comp F = F'.comp (ψ : G →* G') ↔ MulEquiv.endCongr ψ F = F' := by
  refine ⟨fun h => MonoidHom.ext fun y => ?_, fun h => h ▸ MulEquiv.comp_eq_endCongr_comp ψ F⟩
  simpa using DFunLike.congr_fun h (ψ.symm y)

/-- The isomorphism of fixed subgroups induced by an isomorphism of the ambient group, with the
endomorphism carried along by conjugation. -/
def fixedSubgroupCongrEnd (ψ : G ≃* G') (F : G →* G) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup (MulEquiv.endCongr ψ F)) :=
  fixedSubgroupCongr ψ (MulEquiv.comp_eq_endCongr_comp ψ F)

@[simp]
theorem coe_fixedSubgroupCongrEnd_apply (ψ : G ≃* G') (F : G →* G) (x : ↥(fixedSubgroup F)) :
    (fixedSubgroupCongrEnd ψ F x : G') = ψ (x : G) :=
  coe_fixedSubgroupCongr_apply _ _ x

end TauCeti
