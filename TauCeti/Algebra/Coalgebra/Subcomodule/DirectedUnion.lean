/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Set.UnionLift
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Linear maps out of a union of finite subcomodules

This file gives the universal property of the directed union of the finite subcomodules of a
comodule. A compatible family of linear maps on the finite subcomodules glues to a linear map on
the whole comodule as soon as every element lies in a finite subcomodule.

The construction is the linear analogue of `Subalgebra.iSupLift`. It uses `Set.liftCover` for the
underlying function and the directedness of finite subcomodules to prove that the local maps agree
on overlaps.

This is a prerequisite for the Tannakian reconstruction step in the `ReductiveGroups` roadmap:
the components of a tensor automorphism on the finite subcomodules of the regular comodule must be
assembled into one linear functional on the coordinate Hopf algebra.

## Main declarations

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

namespace Subcomodule

variable {R : Type u} {C : Type v} {M : Type w} {P : Type x}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid P] [Module R P]

private theorem finiteSubcomodule_cover
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N) :
    (⋃ N : finiteSubcomodules (R := R) (C := C) (M := M), (N.1 : Set M)) =
      Set.univ :=
  iUnion_finiteSubcomodules_eq_univ_of_exists_mem hM

private theorem finiteSubcomodule_compatible
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ))
    (N Q : finiteSubcomodules (R := R) (C := C) (M := M)) (m : M)
    (hmN : m ∈ N.1) (hmQ : m ∈ Q.1) :
    f N ⟨m, hmN⟩ = f Q ⟨m, hmQ⟩ := by
  have hdir : Directed (· ≤ ·)
      (fun K : finiteSubcomodules (R := R) (C := C) (M := M) => K.1) :=
    directedOn_finiteSubcomodules.directed_val
  obtain ⟨K, hNK, hQK⟩ := hdir N Q
  have hN := LinearMap.congr_fun (hf N K hNK) (⟨m, hmN⟩ : N.1)
  have hQ := LinearMap.congr_fun (hf Q K hQK) (⟨m, hmQ⟩ : Q.1)
  calc
    f N ⟨m, hmN⟩ = f K ⟨m, hNK hmN⟩ := hN
    _ = f K ⟨m, hQK hmQ⟩ := congrArg (f K) (Subtype.ext rfl)
    _ = f Q ⟨m, hmQ⟩ := hQ.symm

/-- Glue a compatible family of linear maps on the finite subcomodules of a comodule.

Compatibility is expressed along inclusions. The hypothesis `hM` says that the finite
subcomodules cover `M`; it is supplied by `exists_finite_subcomodule_mem` whenever `C` is free as
an `R`-module. -/
noncomputable def finiteSubcomoduleLiftOfExistsMem
    (hM : ∀ m : M, ∃ N : Subcomodule R C M, Module.Finite R N.toSubmodule ∧ m ∈ N)
    (f : ∀ N : finiteSubcomodules (R := R) (C := C) (M := M), N.1 →ₗ[R] P)
    (hf : ∀ (N Q : finiteSubcomodules (R := R) (C := C) (M := M))
      (hNQ : N.1 ≤ Q.1),
        f N = (f Q).comp (Submodule.inclusion hNQ)) : M →ₗ[R] P := by
  let S := fun N : finiteSubcomodules (R := R) (C := C) (M := M) => (N.1 : Set M)
  refine
    { toFun := Set.liftCover S (fun N => f N) (finiteSubcomodule_compatible f hf)
        (finiteSubcomodule_cover hM)
      map_add' := ?_
      map_smul' := ?_ }
  · intro m n
    obtain ⟨N, hNfinite, hmnN⟩ :=
      exists_finite_subcomodule_of_setFinite_of_exists_mem hM (Set.toFinite {m, n})
    let N' : finiteSubcomodules (R := R) (C := C) (M := M) :=
      ⟨N, mem_finiteSubcomodules.mpr hNfinite⟩
    have hmN : m ∈ S N' := hmnN (Set.mem_insert m {n})
    have hnN : n ∈ S N' := hmnN (Set.mem_insert_of_mem m (Set.mem_singleton n))
    have haddN : m + n ∈ S N' := N.toSubmodule.add_mem hmN hnN
    rw [Set.liftCover_of_mem haddN, Set.liftCover_of_mem hmN, Set.liftCover_of_mem hnN]
    exact map_add (f N') ⟨m, hmN⟩ ⟨n, hnN⟩
  · intro r m
    obtain ⟨N, hNfinite, hmN⟩ := hM m
    let N' : finiteSubcomodules (R := R) (C := C) (M := M) :=
      ⟨N, mem_finiteSubcomodules.mpr hNfinite⟩
    have hmN' : m ∈ S N' := hmN
    have hsmulN : r • m ∈ S N' := N.toSubmodule.smul_mem r hmN
    rw [Set.liftCover_of_mem hsmulN, Set.liftCover_of_mem hmN']
    exact map_smul (f N') r ⟨m, hmN'⟩

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
  change Set.liftCover
    (fun Q : finiteSubcomodules (R := R) (C := C) (M := M) => (Q.1 : Set M))
    (fun Q => f Q) (finiteSubcomodule_compatible f hf) (finiteSubcomodule_cover hM)
    (m : M) = f N m
  exact Set.liftCover_coe
    (S := fun Q : finiteSubcomodules (R := R) (C := C) (M := M) => (Q.1 : Set M))
    (f := fun Q => f Q) (hf := finiteSubcomodule_compatible f hf)
    (hS := finiteSubcomodule_cover hM) m

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
