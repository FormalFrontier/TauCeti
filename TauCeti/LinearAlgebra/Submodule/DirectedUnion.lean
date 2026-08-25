/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Linear maps out of directed unions of submodules

This file gives the universal property of a directed union of submodules. A compatible family of
linear maps on the members of a directed family glues to a linear map on any submodule of their
supremum.

The construction `TauCeti.Submodule.iSupLift` is the linear analogue of
`Subalgebra.iSupLift`. It uses `Set.iUnionLift` and the directedness of the family to prove that the
local maps agree on overlaps.

## Main declarations

* `TauCeti.Submodule.iSupLift`: glue compatible linear maps on a directed family of submodules.
* `TauCeti.Submodule.iSupLift_inclusion` and `TauCeti.Submodule.iSupLift_of_mem`: pointwise
  evaluation rules for the glued map.
* `TauCeti.Submodule.iSupLift_mk`: the glued map agrees with each prescribed map.
* `TauCeti.Submodule.iSupLift_comp_inclusion`: restricting the glued map recovers each prescribed
  map.
* `TauCeti.Submodule.iSupLift_unique`: the restriction property characterizes the glued map.
-/

public section

namespace TauCeti

universe u v w x

namespace Submodule

variable {R : Type u} {M : Type v} {P : Type w} {ι : Type x}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

private noncomputable def iSupLiftNonempty [Nonempty ι] (K : ι → Submodule R M)
    (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₗ[R] P)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h))
    (T : Submodule R M) (hT : T ≤ iSup K) : T →ₗ[R] P := by
  let compatible :
      ∀ (i j) (x : M) (hxi : x ∈ (K i : Set M)) (hxj : x ∈ (K j : Set M)),
        f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩ := by
    intro i j m hmi hmj
    obtain ⟨k, hik, hjk⟩ := dir i j
    rw [hf i k hik, hf j k hjk]
    rfl
  let liftSup : (iSup K : Submodule R M) →ₗ[R] P :=
    { toFun :=
        Set.iUnionLift (fun i => (K i : Set M)) (fun i => f i) compatible
          ((iSup K : Submodule R M) : Set M)
          (le_of_eq (Submodule.coe_iSup_of_directed K dir))
      map_add' := by
        apply Set.iUnionLift_binary (Submodule.coe_iSup_of_directed K dir) dir _
          (fun _ => (· + ·))
        all_goals simp
      map_smul' := fun r => by
        dsimp
        apply Set.iUnionLift_unary (Submodule.coe_iSup_of_directed K dir) _
          (fun _ m => r • m)
        all_goals simp }
  exact liftSup.comp (Submodule.inclusion hT)

/-- Define a linear map on a submodule of a directed supremum by defining it compatibly on each
member of the directed family. -/
noncomputable def iSupLift (K : ι → Submodule R M) (dir : Directed (· ≤ ·) K)
    (f : ∀ i, K i →ₗ[R] P)
    (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h))
    (T : Submodule R M) (hT : T ≤ iSup K) : T →ₗ[R] P := by
  classical
  exact if hι : Nonempty ι then
      let _ := hι
      iSupLiftNonempty K dir f hf T hT
    else 0

/-- The map glued on a directed supremum agrees with a prescribed map on each member of the
family. -/
@[simp]
theorem iSupLift_mk {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : K i) (hm : (m : M) ∈ T) :
    iSupLift K dir f hf T hT ⟨m, hm⟩ = f i m := by
  let _ : Nonempty ι := ⟨i⟩
  rw [iSupLift, dite_eq_left ⟨i⟩]
  unfold iSupLiftNonempty
  dsimp
  rw [Submodule.inclusion_apply]
  rw [Set.iUnionLift_mk]

/-- The map glued on a directed supremum agrees with a prescribed map after inclusion into its
domain. -/
@[simp]
theorem iSupLift_inclusion {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : K i) (h : K i ≤ T) :
    iSupLift K dir f hf T hT (Submodule.inclusion h m) = f i m := by
  apply iSupLift_mk

/-- Evaluate the map glued on a directed supremum at an element known to lie in one member of the
family. -/
theorem iSupLift_of_mem {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : T) (hm : (m : M) ∈ K i) :
    iSupLift K dir f hf T hT m = f i ⟨m, hm⟩ := by
  exact iSupLift_mk (dir := dir) (hf := hf) (⟨(m : M), hm⟩ : K i) m.2

/-- Restricting the map glued on a directed supremum to a member of the family recovers the
prescribed map. -/
@[simp]
theorem iSupLift_comp_inclusion {K : ι → Submodule R M}
    {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (Submodule.inclusion h) = f i := by
  ext m
  exact iSupLift_mk (dir := dir) (hf := hf) m (h m.2)

/-- A linear map on a submodule of a directed supremum is determined by its values on the members
of the directed family. -/
theorem iSupLift_unique {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} (g : T →ₗ[R] P)
    (hg : ∀ (i : ι) (m : K i) (hm : (m : M) ∈ T), g ⟨m, hm⟩ = f i m) :
    g = iSupLift K dir f hf T hT := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let _ : IsEmpty ι := hι
    rw [iSup_of_empty] at hT
    have hT_eq : T = ⊥ := le_antisymm hT bot_le
    subst T
    ext m
    have hm : m = 0 := Subsingleton.elim _ _
    subst m
    simp
  let _ : Nonempty ι := hι
  ext m
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed K dir).1 (hT m.2)
  rw [hg i ⟨m, hi⟩ m.2]
  simpa only using
    (iSupLift_mk (dir := dir) (hf := hf) (m := ⟨m, hi⟩) m.2).symm

end Submodule

end TauCeti
