/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.UnionLift
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Linear maps out of directed unions of submodules

This file gives the universal property of a directed union of submodules, then specializes it to
the finite subcomodules of a comodule. A compatible family of linear maps on the finite
subcomodules glues to a linear map on the whole comodule as soon as every element lies in a finite
subcomodule.

The construction `TauCeti.Submodule.iSupLift` is the linear analogue of
`Subalgebra.iSupLift`. It uses `Set.iUnionLift` and the directedness of the family to prove that the
local maps agree on overlaps.

This is a prerequisite for the Tannakian reconstruction step in the `ReductiveGroups` roadmap:
the components of a tensor automorphism on the finite subcomodules of the regular comodule must be
assembled into one linear functional on the coordinate Hopf algebra.

## Main declarations

* `TauCeti.Submodule.iSupLift`: glue compatible linear maps on a directed family of submodules.
* `TauCeti.Subcomodule.finiteSubcomoduleLiftOfExistsMem`: glue a compatible family under an
  explicit covering hypothesis.
* `TauCeti.Subcomodule.finiteSubcomoduleLift`: glue such a family when the coefficient coalgebra
  is free.
* `TauCeti.Subcomodule.finiteSubcomoduleLift_apply`: the glued map restricts to each member of the
  family.
* `TauCeti.Subcomodule.finiteSubcomoduleLift_unique`: the restriction property characterizes the
  glued map.
-/

public section

namespace TauCeti

universe u v w x

namespace Submodule

variable {R : Type u} {M : Type v} {P : Type w} {ι : Type x}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid P] [Module R P]

/-- Define a linear map on a submodule of a directed supremum by defining it compatibly on each
member of the directed family. -/
noncomputable def iSupLift [Nonempty ι] (K : ι → Submodule R M) (dir : Directed (· ≤ ·) K)
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

/-- The map glued on a directed supremum agrees with a prescribed map on each member of the
family. -/
@[simp]
theorem iSupLift_mk [Nonempty ι] {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (m : K i) (hm : (m : M) ∈ T) :
    iSupLift K dir f hf T hT ⟨m, hm⟩ = f i m := by
  unfold iSupLift
  dsimp
  rw [Submodule.inclusion_apply]
  rw [Set.iUnionLift_mk]

/-- Restricting the map glued on a directed supremum to a member of the family recovers the
prescribed map. -/
@[simp]
theorem iSupLift_comp_inclusion [Nonempty ι] {K : ι → Submodule R M}
    {dir : Directed (· ≤ ·) K} {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} {i : ι} (h : K i ≤ T) :
    (iSupLift K dir f hf T hT).comp (Submodule.inclusion h) = f i := by
  ext m
  exact iSupLift_mk (dir := dir) (hf := hf) m (h m.2)

/-- A linear map on a submodule of a directed supremum is determined by its values on the members
of the directed family. -/
theorem iSupLift_unique [Nonempty ι] {K : ι → Submodule R M} {dir : Directed (· ≤ ·) K}
    {f : ∀ i, K i →ₗ[R] P}
    {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (Submodule.inclusion h)}
    {T : Submodule R M} {hT : T ≤ iSup K} (g : T →ₗ[R] P)
    (hg : ∀ (i : ι) (m : K i) (hm : (m : M) ∈ T), g ⟨m, hm⟩ = f i m) :
    g = iSupLift K dir f hf T hT := by
  ext m
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed K dir).1 (hT m.2)
  rw [hg i ⟨m, hi⟩ m.2]
  simpa only using
    (iSupLift_mk (dir := dir) (hf := hf) (m := ⟨m, hi⟩) m.2).symm

end Submodule

namespace Subcomodule

variable {R : Type u} {C : Type v} {M : Type w} {P : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid P] [Module R P]

private instance : Nonempty (finiteSubcomodules (R := R) (C := C) (M := M)) :=
  nonempty_finiteSubcomodules.to_subtype

private theorem finiteSubcomodule_directed_toSubmodule :
    Directed (· ≤ ·) (fun N : finiteSubcomodules (R := R) (C := C) (M := M) =>
      N.1.toSubmodule) := by
  intro N Q
  obtain ⟨K, hNK, hQK⟩ := directedOn_finiteSubcomodules.directed_val N Q
  exact ⟨K, toSubmodule_le_toSubmodule.2 hNK, toSubmodule_le_toSubmodule.2 hQK⟩

private theorem iSup_finiteSubcomodule_toSubmodule_eq_top
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    (⨆ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1.toSubmodule) = ⊤ := by
  rw [← sSup_toSubmodule, sSup_finiteSubcomodules_eq_top_of_exists_mem hM]
  rfl

/-- Glue a compatible family of linear maps on the finite subcomodules of a comodule.

Compatibility is expressed along inclusions. The hypothesis `hM` says that the finite
subcomodules cover `M`; it is supplied by `exists_finite_subcomodule_mem` whenever `C` is free as
an `R`-module. -/
noncomputable def finiteSubcomoduleLiftOfExistsMem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ)) : M →ₗ[R] P :=
  (Submodule.iSupLift
      (fun N : finiteSubcomodules (R := R) (C := C) (M := M) => N.1.toSubmodule)
      finiteSubcomodule_directed_toSubmodule f
      (fun N Q h => hf N Q (toSubmodule_le_toSubmodule.1 h)) ⊤
      (iSup_finiteSubcomodule_toSubmodule_eq_top hM).symm.le).comp
    (Submodule.topEquiv (R := R) (M := M)).symm.toLinearMap

/-- The map glued from finite subcomodules agrees with the prescribed map on each finite
subcomodule. -/
@[simp]
theorem finiteSubcomoduleLiftOfExistsMem_apply
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (N : finiteSubcomodules (R := R) (C := C) (M := M)) (m : N.1) :
    finiteSubcomoduleLiftOfExistsMem hM f hf m = f N m := by
  unfold finiteSubcomoduleLiftOfExistsMem
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [show (Submodule.topEquiv (R := R) (M := M)).symm (m : M) =
    (⟨m, Submodule.mem_top⟩ : (⊤ : Submodule R M)) from rfl]
  apply Submodule.iSupLift_mk

/-- Restricting the map glued from finite subcomodules to one finite subcomodule recovers its
prescribed map. -/
@[simp]
theorem finiteSubcomoduleLiftOfExistsMem_comp_subtype
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (N : finiteSubcomodules (R := R) (C := C) (M := M)) :
    (finiteSubcomoduleLiftOfExistsMem hM f hf).comp N.1.toSubmodule.subtype = f N := by
  ext m
  exact finiteSubcomoduleLiftOfExistsMem_apply hM f hf N m

/-- A linear map out of a comodule is determined by its restrictions to all finite
subcomodules. -/
theorem finiteSubcomoduleLiftOfExistsMem_unique
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (g : M →ₗ[R] P) (hg : ∀ (N : finiteSubcomodules (R := R) (C := C) (M := M))
      (m : N.1), g m = f N m) :
    g = finiteSubcomoduleLiftOfExistsMem hM f hf := by
  ext m
  obtain ⟨N, hNfinite, hmN⟩ := hM m
  let N' : finiteSubcomodules (R := R) (C := C) (M := M) :=
    ⟨N, mem_finiteSubcomodules.mpr hNfinite⟩
  rw [hg N' ⟨m, hmN⟩, finiteSubcomoduleLiftOfExistsMem_apply hM f hf N' ⟨m, hmN⟩]

/-- Glue a compatible family of linear maps on the finite subcomodules of a comodule whose
coefficient coalgebra is free as a module. -/
noncomputable def finiteSubcomoduleLift [Module.Free R C]
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ)) : M →ₗ[R] P :=
  finiteSubcomoduleLiftOfExistsMem exists_finite_subcomodule_mem f hf

/-- The map glued from the finite subcomodules of a comodule over a free coalgebra agrees with
the prescribed map on each finite subcomodule. -/
@[simp]
theorem finiteSubcomoduleLift_apply [Module.Free R C]
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (N : finiteSubcomodules (R := R) (C := C) (M := M)) (m : N.1) :
    finiteSubcomoduleLift f hf m = f N m :=
  finiteSubcomoduleLiftOfExistsMem_apply exists_finite_subcomodule_mem f hf N m

/-- Restricting the map glued from finite subcomodules over a free coefficient coalgebra to one
finite subcomodule recovers its prescribed map. -/
@[simp]
theorem finiteSubcomoduleLift_comp_subtype [Module.Free R C]
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (N : finiteSubcomodules (R := R) (C := C) (M := M)) :
    (finiteSubcomoduleLift f hf).comp N.1.toSubmodule.subtype = f N :=
  finiteSubcomoduleLiftOfExistsMem_comp_subtype exists_finite_subcomodule_mem f hf N

/-- A linear map out of a comodule over a free coefficient coalgebra is determined by its
restrictions to the finite subcomodules. -/
theorem finiteSubcomoduleLift_unique [Module.Free R C]
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (g : M →ₗ[R] P) (hg : ∀ (N : finiteSubcomodules (R := R) (C := C) (M := M))
      (m : N.1), g m = f N m) :
    g = finiteSubcomoduleLift f hf :=
  finiteSubcomoduleLiftOfExistsMem_unique exists_finite_subcomodule_mem f hf g hg

end Subcomodule

end TauCeti
