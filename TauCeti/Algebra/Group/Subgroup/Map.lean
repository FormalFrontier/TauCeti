/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Maps of subgroups

Mathlib's `MonoidHom.subgroupComap` sends the preimage `K.comap f` of a subgroup `K` to `K`.
Mathlib records that this map is surjective when `f` is
(`MonoidHom.subgroupComap_surjective_of_surjective`); this file records the companion fact for
injectivity. It also records how surjective homomorphisms act on centres.

## Main results

* `TauCeti.MonoidHom.subgroupComap_injective_of_injective`: `f.subgroupComap K` is injective when
  `f` is.
* `TauCeti.Subgroup.map_center_le`: a surjective homomorphism carries central elements to central
  elements.
* `TauCeti.MonoidHom.center_le_ker`: the centre lies in the kernel of a surjection onto a
  centreless group.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [Group H]

/-- The comparison map from the preimage of a subgroup to that subgroup is injective as soon as the
underlying homomorphism is. Companion to Mathlib's
`MonoidHom.subgroupComap_surjective_of_surjective`. -/
theorem MonoidHom.subgroupComap_injective_of_injective {f : H →* G} (hf : Function.Injective f)
    (K : Subgroup G) : Function.Injective (f.subgroupComap K) :=
  fun _ _ hxy => Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A surjective homomorphism carries central elements to central elements. -/
theorem Subgroup.map_center_le (f : G →* H) (hf : Function.Surjective f) :
    (Subgroup.center G).map f ≤ Subgroup.center H := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨z, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]

/-- An isomorphism of groups carries the centre onto the centre. -/
theorem Subgroup.map_center_eq_center (e : G ≃* H) :
    (Subgroup.center G).map (e : G →* H) = Subgroup.center H := by
  apply le_antisymm (Subgroup.map_center_le _ e.surjective)
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  exact Subgroup.map_center_le (e.symm : H →* G) e.symm.surjective ⟨y, hy, rfl⟩

/-- The centre of a group lies in the kernel of every surjection onto a centreless group. -/
theorem MonoidHom.center_le_ker (f : G →* H) (hf : Function.Surjective f)
    (hH : Subgroup.center H = ⊥) : Subgroup.center G ≤ f.ker := by
  intro x hx
  have hfx := Subgroup.map_center_le f hf ⟨x, hx, rfl⟩
  rw [hH, Subgroup.mem_bot] at hfx
  exact hfx

end TauCeti
