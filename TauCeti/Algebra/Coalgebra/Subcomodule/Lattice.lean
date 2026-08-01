/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Basic

/-!
# Joins of subcomodules

This file adds suprema to the lightweight `Subcomodule` structure. The supremum of a family
of subcomodules has underlying submodule the supremum of the underlying submodules; the
coaction is stable because `ρ` is linear, every element of a submodule supremum is a finite
sum of elements from the summands, and each summand coacts into the tensor product of a
submodule contained in the larger one.

This is a Layer 1 prerequisite for the reductive-groups roadmap target on finite-dimensional
subcomodules: finite sums of finite subcomodules remain finite.

## Main declarations

* `Subcomodule.instCompleteSemilatticeSup`: arbitrary suprema of subcomodules.
* `Subcomodule.iSup_toSubmodule`, `Subcomodule.mem_iSup`, `Subcomodule.mem_sSup`:
  characteristic API for arbitrary joins.
* `Subcomodule.coe_iSup_of_directed`, `Subcomodule.mem_iSup_of_directed`:
  a nonempty directed join has carrier equal to the union of the carriers.
* `Subcomodule.sup_toSubmodule`, `Subcomodule.mem_sup`: characteristic API for binary joins.
* `Subcomodule.iSup_finite`, `Subcomodule.sup_finite`, `Subcomodule.finset_sup_finite`:
  finite generation is preserved by finite joins.
* `Subcomodule.map_sup`, `Subcomodule.map_iSup`: images preserve joins.

## References

The lattice construction is adapted from `TauCeti.Algebra.Coalgebra.Subcoalgebra.Lattice`,
and the image-join lemmas follow the corresponding map API in
`TauCeti.Algebra.Coalgebra.Subcoalgebra.Map`.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

namespace Subcomodule

omit [Coalgebra R C] [Comodule R C M] in
private lemma tensor_range_mono {P Q : Submodule R M} (hPQ : P ≤ Q) :
    LinearMap.range (TensorProduct.map P.subtype (LinearMap.id : C →ₗ[R] C)) ≤
      LinearMap.range (TensorProduct.map Q.subtype (LinearMap.id : C →ₗ[R] C)) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨TensorProduct.map (Submodule.inclusion hPQ) (LinearMap.id : C →ₗ[R] C) x, ?_⟩
  induction x with
  | zero => simp
  | tmul p c => rfl
  | add x y hx hy => simp [hx, hy]

private lemma coact_mem_sup (N P : Subcomodule R C M) {m : M}
    (hm : m ∈ N.toSubmodule ⊔ P.toSubmodule) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range
        (TensorProduct.map (N.toSubmodule ⊔ P.toSubmodule).subtype
          (LinearMap.id : C →ₗ[R] C)) := by
  rcases Submodule.mem_sup.1 hm with ⟨n, hn, p, hp, rfl⟩
  rw [LinearMap.map_add]
  exact add_mem
    (tensor_range_mono
      (P := N.toSubmodule) (Q := N.toSubmodule ⊔ P.toSubmodule) le_sup_left
      (N.coact_mem hn))
    (tensor_range_mono
      (P := P.toSubmodule) (Q := N.toSubmodule ⊔ P.toSubmodule) le_sup_right
      (P.coact_mem hp))

private lemma coact_mem_sSup (S : Set (Subcomodule R C M)) {m : M}
    (hm : m ∈ ⨆ N : S, (N : Subcomodule R C M).toSubmodule) :
    Comodule.coact (R := R) (C := C) (M := M) m ∈
      LinearMap.range
        (TensorProduct.map (⨆ N : S, (N : Subcomodule R C M).toSubmodule).subtype
          (LinearMap.id : C →ₗ[R] C)) := by
  classical
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hm
  rcases hm with ⟨f, hf, rfl⟩
  rw [Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun N _ =>
    tensor_range_mono
      (P := (N : Subcomodule R C M).toSubmodule)
      (Q := ⨆ N : S, (N : Subcomodule R C M).toSubmodule)
      (le_iSup (fun N : S => (N : Subcomodule R C M).toSubmodule) N)
      (N.1.coact_mem (hf N))

/-- The join of two subcomodules has underlying submodule the join of the underlying
submodules. -/
instance instMax : Max (Subcomodule R C M) where
  max N P :=
    { carrier := N.toSubmodule ⊔ P.toSubmodule
      coact_mem' := by
        intro m hm
        exact coact_mem_sup N P hm }

/-- The supremum of a set of subcomodules has underlying submodule the supremum of the
underlying submodules. -/
instance instSupSet : SupSet (Subcomodule R C M) where
  sSup S :=
    { carrier := ⨆ N : S, (N : Subcomodule R C M).toSubmodule
      coact_mem' := by
        intro m hm
        exact coact_mem_sSup S hm }

/-- The underlying submodule of the join is the join of the underlying submodules. -/
@[simp]
theorem sup_toSubmodule (N P : Subcomodule R C M) :
    (N ⊔ P).toSubmodule = N.toSubmodule ⊔ P.toSubmodule :=
  rfl

/-- Membership in the join of two subcomodules. -/
theorem mem_sup {N P : Subcomodule R C M} {m : M} :
    m ∈ N ⊔ P ↔ ∃ n ∈ N, ∃ p ∈ P, n + p = m := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]
  rfl

/-- Subcomodules form a semilattice under the join whose carrier is the supremum of the
underlying submodules. -/
instance instSemilatticeSup : SemilatticeSup (Subcomodule R C M) :=
  SemilatticeSup.mk (fun N P => N ⊔ P)
    (fun _ _ => by
      intro m hm
      rw [← mem_toSubmodule, sup_toSubmodule]
      exact Submodule.mem_sup_left ((mem_toSubmodule).2 hm))
    (fun _ _ => by
      intro m hm
      rw [← mem_toSubmodule, sup_toSubmodule]
      exact Submodule.mem_sup_right ((mem_toSubmodule).2 hm))
    (fun _ _ _ hN hP => by
      intro m hm
      rw [mem_sup] at hm
      rcases hm with ⟨n, hn, p, hp, rfl⟩
      exact add_mem (hN hn) (hP hp))

/-- The underlying submodule of a supremum of a set of subcomodules is the supremum of the
underlying submodules indexed by that set. -/
@[simp]
theorem sSup_toSubmodule (S : Set (Subcomodule R C M)) :
    (sSup S).toSubmodule = ⨆ N : S, (N : Subcomodule R C M).toSubmodule :=
  rfl

/-- Membership in the supremum of a set of subcomodules. -/
theorem mem_sSup {S : Set (Subcomodule R C M)} {m : M} :
    m ∈ sSup S ↔
      ∃ f : S →₀ M, (∀ N : S, f N ∈ (N : Subcomodule R C M)) ∧
        f.sum (fun _ x => x) = m := by
  rw [← mem_toSubmodule, sSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp
    (fun N : S => (N : Subcomodule R C M).toSubmodule) m

/-- The underlying submodule of a supremum of subcomodules is the supremum of the
underlying submodules. -/
@[simp]
theorem iSup_toSubmodule {ι : Sort*} (N : ι → Subcomodule R C M) :
    (⨆ i, N i).toSubmodule = ⨆ i, (N i).toSubmodule := by
  rw [iSup, sSup_toSubmodule]
  ext m
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of subcomodules. -/
theorem mem_iSup {ι : Type*} {N : ι → Subcomodule R C M} {m : M} :
    m ∈ ⨆ i, N i ↔
      ∃ f : ι →₀ M, (∀ i, f i ∈ N i) ∧ f.sum (fun _ x => x) = m := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (N i).toSubmodule) m

/-- Subcomodules have arbitrary suprema, computed on underlying submodules. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Subcomodule R C M) where
  sSup := sSup
  isLUB_sSup S :=
    ⟨fun N hN m hm => by
      rw [← mem_toSubmodule, sSup_toSubmodule]
      exact Submodule.mem_iSup_of_mem ⟨N, hN⟩ ((mem_toSubmodule).2 hm),
    fun N hN m hm => by
      rw [← mem_toSubmodule, sSup_toSubmodule] at hm
      rw [← mem_toSubmodule]
      have hle : (⨆ P : S, (P : Subcomodule R C M).toSubmodule) ≤ N.toSubmodule := by
        refine iSup_le fun P : S => ?_
        exact toSubmodule_le_toSubmodule.2 (hN P.2)
      exact hle hm⟩

/-- The carrier of a nonempty directed supremum of subcomodules is the union of their carriers. -/
@[simp]
theorem coe_iSup_of_directed {iota : Type*} [Nonempty iota]
    (N : iota → Subcomodule R C M) (hN : Directed (· ≤ ·) N) :
    ((↑(⨆ i, N i) : Set M)) = ⋃ i, (N i : Set M) := by
  have hN' : Directed (· ≤ ·) (fun i ↦ (N i).toSubmodule) := fun i j ↦ by
    obtain ⟨k, hik, hjk⟩ := hN i j
    exact ⟨k, toSubmodule_le_toSubmodule.2 hik, toSubmodule_le_toSubmodule.2 hjk⟩
  ext m
  rw [SetLike.mem_coe, ← mem_toSubmodule, iSup_toSubmodule, ← SetLike.mem_coe,
    Submodule.coe_iSup_of_directed _ hN']
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_toSubmodule]

/-- An element belongs to a nonempty directed supremum of subcomodules exactly when it belongs to
one member of the family. -/
@[simp]
theorem mem_iSup_of_directed {iota : Type*} [Nonempty iota]
    (N : iota → Subcomodule R C M) (hN : Directed (· ≤ ·) N) {m : M} :
    m ∈ ⨆ i, N i ↔ ∃ i, m ∈ N i := by
  rw [← SetLike.mem_coe, coe_iSup_of_directed N hN, Set.mem_iUnion]
  simp only [SetLike.mem_coe]

/-- The carrier of the supremum of a nonempty directed set of subcomodules is the union of its
carriers. -/
@[simp]
theorem coe_sSup_of_directedOn {S : Set (Subcomodule R C M)} (hS : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) :
    ((sSup S : Subcomodule R C M) : Set M) = ⋃ N : S, (N.1 : Set M) := by
  letI : Nonempty S := hS.to_subtype
  rw [sSup_eq_iSup']
  exact coe_iSup_of_directed (fun N : S ↦ N.1) hdir.directed_val

/-- Membership in the supremum of a nonempty directed set of subcomodules reduces to membership
in one member of the set. -/
@[simp]
theorem mem_sSup_of_directedOn {S : Set (Subcomodule R C M)} (hS : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) {m : M} :
    m ∈ sSup S ↔ ∃ N ∈ S, m ∈ N := by
  letI : Nonempty S := hS.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed (fun N : S ↦ N.1) hdir.directed_val,
    SetCoe.exists, exists_prop]

/-- The join of finitely generated subcomodules is finitely generated as an `R`-module. -/
theorem sup_finite (N P : Subcomodule R C M)
    [Module.Finite R N.toSubmodule] [Module.Finite R P.toSubmodule] :
    Module.Finite R (N ⊔ P).toSubmodule := by
  rw [sup_toSubmodule, Module.Finite.iff_fg]
  exact (Module.Finite.iff_fg.mp inferInstance).sup (Module.Finite.iff_fg.mp inferInstance)

/-- The join of finitely generated subcomodules is finitely generated as an `R`-module. -/
instance instFiniteSup (N P : Subcomodule R C M)
    [Module.Finite R N.toSubmodule] [Module.Finite R P.toSubmodule] :
    Module.Finite R (N ⊔ P).toSubmodule :=
  sup_finite N P

variable {ι : Type*}

/-- The underlying submodule of a finite join of subcomodules is the finite join of the
underlying submodules. -/
@[simp]
theorem finset_sup_toSubmodule (s : Finset ι) (N : ι → Subcomodule R C M) :
    (s.sup N).toSubmodule = s.sup fun i => (N i).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bot_toSubmodule
  | insert a s _ ih =>
      rw [Finset.sup_insert, sup_toSubmodule, ih, Finset.sup_insert]

/-- Membership in a finite join of subcomodules. -/
theorem mem_finset_sup {s : Finset ι} {N : ι → Subcomodule R C M} {m : M} :
    m ∈ s.sup N ↔ ∃ μ : ∀ i, (N i).toSubmodule, (∑ i ∈ s, (μ i : M)) = m := by
  rw [← mem_toSubmodule, finset_sup_toSubmodule]
  simpa only [Finset.sup_eq_iSup] using
    (Submodule.mem_iSup_finset_iff_exists_sum (fun i => (N i).toSubmodule) m)

/-- A finite supremum of finitely generated subcomodules is finitely generated as an
`R`-module. -/
theorem iSup_finite {ι : Sort*} [Finite ι] (N : ι → Subcomodule R C M)
    (hN : ∀ i, Module.Finite R (N i).toSubmodule) :
    Module.Finite R (⨆ i, N i).toSubmodule := by
  rw [iSup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_iSup (fun i => (N i).toSubmodule)
    fun i => Module.Finite.iff_fg.mp (hN i)

/-- A finite join of finitely generated subcomodules is finitely generated as an
`R`-module. -/
theorem finset_sup_finite (s : Finset ι) (N : ι → Subcomodule R C M)
    (hN : ∀ i ∈ s, Module.Finite R (N i).toSubmodule) :
    Module.Finite R (s.sup N).toSubmodule := by
  classical
  rw [finset_sup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_finset_sup s (fun i => (N i).toSubmodule)
    fun i hi => Module.Finite.iff_fg.mp (hN i hi)

section Map

variable {M' : Type*} [AddCommMonoid M'] [Module R M'] [Comodule R C M']

/-- The image of a binary join is the binary join of the images. -/
@[simp]
theorem map_sup (f : Comodule.Hom R C M M') (N P : Subcomodule R C M) :
    (N ⊔ P).map f = N.map f ⊔ P.map f := by
  ext m
  rw [← mem_toSubmodule, map_toSubmodule, sup_toSubmodule, Submodule.map_sup,
    ← map_toSubmodule N f, ← map_toSubmodule P f, ← sup_toSubmodule, mem_toSubmodule]

/-- The image of a supremum is the supremum of the images. -/
@[simp]
theorem map_iSup {ι : Sort*} (f : Comodule.Hom R C M M') (N : ι → Subcomodule R C M) :
    (⨆ i, N i).map f = ⨆ i, (N i).map f := by
  ext m
  rw [← mem_toSubmodule, map_toSubmodule, iSup_toSubmodule, Submodule.map_iSup]
  simp_rw [← map_toSubmodule (f := f)]
  rw [← iSup_toSubmodule, mem_toSubmodule]

/-- The image of a finite join is the finite join of the images. -/
@[simp]
theorem map_finset_sup (s : Finset ι) (f : Comodule.Hom R C M M')
    (N : ι → Subcomodule R C M) :
    (s.sup N).map f = s.sup fun i => (N i).map f := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.sup_empty, Finset.sup_empty, map_bot]
  | cons i s hi ih => rw [Finset.sup_cons, Finset.sup_cons, map_sup, ih]

end Map

end Subcomodule

end TauCeti
