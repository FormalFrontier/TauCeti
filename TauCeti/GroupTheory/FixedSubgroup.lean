/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End
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
* `TauCeti.fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_comp`: a point fixed by each of two
  endomorphisms is fixed by their composite.
* `TauCeti.fixedSubgroup_comp_le_fixedSubgroup_pow_of_commute_of_pow_eq_one`: fixed points of a
  composite of commuting endomorphisms lie in the fixed points of a power of one factor when the
  other factor has finite order.
* `TauCeti.map_fixedSubgroup_le`: a homomorphism intertwining two endomorphisms carries the points
  fixed by the one to the points fixed by the other.
* `TauCeti.map_fixedSubgroup_eq`: an isomorphism intertwining them carries the one *onto* the other.
* `TauCeti.fixedSubgroupCongr`: the resulting isomorphism of fixed subgroups.
* `TauCeti.symm_comp_eq_comp_symm_of_comp_eq_comp` and
  `TauCeti.trans_comp_eq_comp_trans_of_comp_eq_comp`: intertwining relations invert and compose,
  which is what makes that isomorphism symmetric and transitive.

## References

The fixed subgroup in the form `F.eqLocus (MonoidHom.id G)` is what milestone L3 of
`TauCetiRoadmap/CFSGStatement/README.md` prescribes for the fixed points of a Steinberg
endomorphism. The construction is standard; see R. W. Carter, *Simple Groups of Lie Type*.
-/

public section

namespace TauCeti

open _root_.Subgroup

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

/-- A point fixed by each of two endomorphisms is fixed by their composite.

The converse fails in general: a Steinberg endomorphism is a composite of a Frobenius with a
diagram automorphism, and its fixed points are not in general fixed by either factor. -/
theorem fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_comp (F F' : G →* G) :
    fixedSubgroup F ⊓ fixedSubgroup F' ≤ fixedSubgroup (F'.comp F) := by
  intro x hx
  obtain ⟨hF, hF'⟩ := Subgroup.mem_inf.mp hx
  rw [mem_fixedSubgroup] at hF hF' ⊢
  rw [MonoidHom.comp_apply, hF, hF']

/-- Suppose that two endomorphisms commute and that `F' ^ d = 1`. Every point fixed by
`F'.comp F` is then fixed by `F ^ d`.

This is the fixed-subgroup consequence of `Function.Commute.comp_iterate`. -/
theorem fixedSubgroup_comp_le_fixedSubgroup_pow_of_commute_of_pow_eq_one
    (F : Monoid.End G) (F' : MulAut G) (hcomm : Function.Commute F' F)
    {d : ℕ} (hpow : F' ^ d = 1) :
    fixedSubgroup (F'.toMonoidHom.comp F : G →* G) ≤
      fixedSubgroup ((F ^ d : Monoid.End G) : G →* G) := by
  intro x hx
  rw [mem_fixedSubgroup] at hx
  rw [mem_fixedSubgroup_end_pow_iff]
  have hfixed := Function.iterate_fixed hx d
  have hcomp : (⇑(F'.toMonoidHom.comp F : Monoid.End G)) = (⇑F') ∘ (⇑F) := rfl
  rw [hcomp, hcomm.comp_iterate] at hfixed
  have hpow' (y : G) : F'^[d] y = y := by
    rw [← congrFun (hom_coe_pow (fun f : MulAut G => (f : G → G))
      (MulAut.coe_one _) (MulAut.coe_mul _) F' d) y, hpow, MulAut.one_apply]
  simpa only [hpow', Function.comp_apply] using hfixed

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
theorem symm_comp_eq_comp_symm_of_comp_eq_comp (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (ψ.symm : G' →* G).comp F' = F.comp (ψ.symm : G' →* G) :=
  have h : Function.Semiconj ψ F F' := fun x => DFunLike.congr_fun hψ x
  MonoidHom.ext (h.inverse_left ψ.symm_apply_apply ψ.apply_symm_apply)

variable {G'' : Type*} [Group G''] {F'' : G'' →* G''}

/-- Intertwining relations compose. -/
theorem trans_comp_eq_comp_trans_of_comp_eq_comp {ψ : G ≃* G'} {χ : G' ≃* G''}
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G'))
    (hχ : (χ : G' →* G'').comp F' = F''.comp (χ : G' →* G'')) :
    ((ψ.trans χ : G ≃* G'') : G →* G'').comp F = F''.comp ((ψ.trans χ : G ≃* G'') : G →* G'') :=
  have h₁ : Function.Semiconj ψ F F' := fun x => DFunLike.congr_fun hψ x
  have h₂ : Function.Semiconj χ F' F'' := fun x => DFunLike.congr_fun hχ x
  MonoidHom.ext (h₁.trans h₂)

/-- An isomorphism intertwining two endomorphisms carries the points fixed by the one *onto* the
points fixed by the other. -/
theorem map_fixedSubgroup_eq (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (fixedSubgroup F).map (ψ : G →* G') = fixedSubgroup F' :=
  le_antisymm (map_fixedSubgroup_le _ hψ) fun y hy =>
    ⟨ψ.symm y,
      map_fixedSubgroup_le (ψ.symm : G' →* G) (symm_comp_eq_comp_symm_of_comp_eq_comp ψ hψ)
        ⟨y, hy, rfl⟩,
      ψ.apply_symm_apply y⟩

/-- The isomorphism of fixed subgroups induced by an isomorphism intertwining the two
endomorphisms. -/
def fixedSubgroupCongr (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    ↥(fixedSubgroup F) ≃* ↥(fixedSubgroup F') :=
  Subgroup.congrOfMapEq ψ (map_fixedSubgroup_eq ψ hψ)

@[simp]
theorem coe_fixedSubgroupCongr_apply (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (x : ↥(fixedSubgroup F)) :
    (fixedSubgroupCongr ψ hψ x : G') = ψ (x : G) :=
  Subgroup.coe_congrOfMapEq_apply ψ _ x

@[simp]
theorem coe_fixedSubgroupCongr_symm_apply (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (y : ↥(fixedSubgroup F')) :
    ((fixedSubgroupCongr ψ hψ).symm y : G) = ψ.symm (y : G') :=
  Subgroup.coe_congrOfMapEq_symm_apply ψ _ y

@[simp]
theorem fixedSubgroupCongr_refl
    (hψ : (MulEquiv.refl G : G →* G).comp F = F.comp (MulEquiv.refl G : G →* G)) :
    fixedSubgroupCongr (MulEquiv.refl G) hψ = MulEquiv.refl ↥(fixedSubgroup F) :=
  Subgroup.congrOfMapEq_refl _

@[simp]
theorem fixedSubgroupCongr_trans (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) (χ : G' ≃* G'')
    (hχ : (χ : G' →* G'').comp F' = F''.comp (χ : G' →* G'')) :
    (fixedSubgroupCongr ψ hψ).trans (fixedSubgroupCongr χ hχ) =
      fixedSubgroupCongr (ψ.trans χ) (trans_comp_eq_comp_trans_of_comp_eq_comp hψ hχ) :=
  Subgroup.congrOfMapEq_trans _ _ _ _

-- Not `@[simp]`, for the reason given at `TauCeti.Subgroup.congrOfMapEq_symm`.
theorem fixedSubgroupCongr_symm (ψ : G ≃* G')
    (hψ : (ψ : G →* G').comp F = F'.comp (ψ : G →* G')) :
    (fixedSubgroupCongr ψ hψ).symm =
      fixedSubgroupCongr ψ.symm (symm_comp_eq_comp_symm_of_comp_eq_comp ψ hψ) :=
  Subgroup.congrOfMapEq_symm _ _

end TauCeti
