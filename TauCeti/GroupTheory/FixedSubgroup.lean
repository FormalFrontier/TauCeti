/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The fixed points of an endomorphism

Let `F` be an endomorphism of a group `G`. This file studies the subgroup

```text
fixedSubgroup F = F.eqLocus (MonoidHom.id G)
```

of points of `G` fixed by `F`: when it is everything and how it grows along the powers of `F`.

Nothing here is specific to any particular endomorphism: the material needs only a group and an
endomorphism of it, so it is available before any ambient group has been constructed.

## Main definitions and results

* `TauCeti.fixedSubgroup`: the subgroup of points fixed by an endomorphism.
* `TauCeti.fixedSubgroup_eq_top_iff`: only the identity fixes every point.
* `TauCeti.fixedSubgroup_le_fixedSubgroup_pow`: a point fixed by an endomorphism is fixed by each of
  its powers.
* `TauCeti.fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_comp`: a point fixed by each of two
  endomorphisms is fixed by their composite.
* `TauCeti.map_fixedSubgroup_le`: a homomorphism intertwining two endomorphisms carries the points
  fixed by the one to the points fixed by the other.

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

/-- A point fixed by each of two endomorphisms is fixed by their composite.

The converse fails in general: a Steinberg endomorphism is a composite of a Frobenius with a
diagram automorphism, and its fixed points are not in general fixed by either factor. -/
theorem fixedSubgroup_inf_fixedSubgroup_le_fixedSubgroup_comp (F F' : G →* G) :
    fixedSubgroup F ⊓ fixedSubgroup F' ≤ fixedSubgroup (F'.comp F) := by
  intro x hx
  obtain ⟨hF, hF'⟩ := Subgroup.mem_inf.mp hx
  rw [mem_fixedSubgroup] at hF hF' ⊢
  rw [MonoidHom.comp_apply, hF, hF']

variable {G' : Type*} [Group G']

/-- A homomorphism intertwining two endomorphisms carries the points fixed by the one to the points
fixed by the other. -/
theorem map_fixedSubgroup_le {F : G →* G} {F' : G' →* G'} (ψ : G →* G')
    (hψ : ψ.comp F = F'.comp ψ) : (fixedSubgroup F).map ψ ≤ fixedSubgroup F' := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_fixedSubgroup, ← MonoidHom.comp_apply, ← hψ, MonoidHom.comp_apply,
    mem_fixedSubgroup.mp hx]

end TauCeti
