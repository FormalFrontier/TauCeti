/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic

/-!
# Joins of subcoalgebras

This file adds suprema to the lightweight `Subcoalgebra` structure. The supremum of a family
of subcoalgebras has underlying submodule the supremum of the underlying submodules; the
comultiplication is stable because `Δ` is linear, every element of a submodule supremum is a
finite sum of elements from the summands, and each tensor square maps into the tensor square
of the larger submodule.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on
finite-dimensional subcoalgebras: finite sums of finite subcoalgebras remain finite.

## Main declarations

* `Subcoalgebra.instCompleteSemilatticeSup`: arbitrary suprema of subcoalgebras.
* `Subcoalgebra.iSup_toSubmodule`, `Subcoalgebra.mem_iSup`, `Subcoalgebra.mem_sSup`:
  characteristic API for arbitrary joins.
* `Subcoalgebra.mem_iSup_of_directed`, `Subcoalgebra.coe_iSup_of_directed`:
  a nonempty directed supremum is the union of its members.
* `Subcoalgebra.mem_sSup_of_directedOn`, `Subcoalgebra.coe_sSup_of_directedOn`:
  the corresponding set-indexed directed-union results.
* `Subcoalgebra.sup_toSubmodule`, `Subcoalgebra.mem_sup`: characteristic API for binary joins.
* `Subcoalgebra.iSup_finite`, `Subcoalgebra.sup_finite`, `Subcoalgebra.finset_sup_finite`:
  finite generation is preserved by finite joins.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

omit [Coalgebra R C] in
private lemma tensorSquare_range_mono {P Q : Submodule R C} (hPQ : P ≤ Q) :
    LinearMap.range (TensorProduct.map P.subtype P.subtype) ≤
      LinearMap.range (TensorProduct.map Q.subtype Q.subtype) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨TensorProduct.map (Submodule.inclusion hPQ) (Submodule.inclusion hPQ) x, ?_⟩
  induction x with
  | zero => simp
  | tmul p q => rfl
  | add x y hx hy => simp [hx, hy]

private lemma comul_mem_sup (D E : Subcoalgebra R C) {c : C}
    (hc : c ∈ D.toSubmodule ⊔ E.toSubmodule) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range
        (TensorProduct.map (D.toSubmodule ⊔ E.toSubmodule).subtype
          (D.toSubmodule ⊔ E.toSubmodule).subtype) := by
  rcases Submodule.mem_sup.1 hc with ⟨d, hd, e, he, rfl⟩
  rw [LinearMap.map_add]
  exact add_mem
    (tensorSquare_range_mono
      (P := D.toSubmodule) (Q := D.toSubmodule ⊔ E.toSubmodule) le_sup_left
      (D.comul_mem hd))
    (tensorSquare_range_mono
      (P := E.toSubmodule) (Q := D.toSubmodule ⊔ E.toSubmodule) le_sup_right
      (E.comul_mem he))

private lemma comul_mem_sSup (S : Set (Subcoalgebra R C)) {c : C}
    (hc : c ∈ ⨆ D : S, (D : Subcoalgebra R C).toSubmodule) :
    Coalgebra.comul (R := R) (A := C) c ∈
      LinearMap.range
        (TensorProduct.map (⨆ D : S, (D : Subcoalgebra R C).toSubmodule).subtype
          (⨆ D : S, (D : Subcoalgebra R C).toSubmodule).subtype) := by
  classical
  rw [Submodule.mem_iSup_iff_exists_finsupp] at hc
  rcases hc with ⟨f, hf, rfl⟩
  rw [Finsupp.sum, map_sum]
  exact Submodule.sum_mem _ fun D _ =>
    tensorSquare_range_mono
      (P := (D : Subcoalgebra R C).toSubmodule)
      (Q := ⨆ D : S, (D : Subcoalgebra R C).toSubmodule)
      (le_iSup (fun D : S => (D : Subcoalgebra R C).toSubmodule) D)
      (D.1.comul_mem (hf D))

/-- The join of two subcoalgebras has underlying submodule the join of the underlying
submodules. -/
instance instMax : Max (Subcoalgebra R C) where
  max D E :=
    { carrier := D.toSubmodule ⊔ E.toSubmodule
      comul_mem' := by
        intro c hc
        exact comul_mem_sup D E hc }

/-- The supremum of a set of subcoalgebras has underlying submodule the supremum of the
underlying submodules. -/
instance instSupSet : SupSet (Subcoalgebra R C) where
  sSup S :=
    { carrier := ⨆ D : S, (D : Subcoalgebra R C).toSubmodule
      comul_mem' := by
        intro c hc
        exact comul_mem_sSup S hc }

/-- The underlying submodule of the join is the join of the underlying submodules. -/
@[simp]
theorem sup_toSubmodule (D E : Subcoalgebra R C) :
    (D ⊔ E).toSubmodule = D.toSubmodule ⊔ E.toSubmodule :=
  rfl

/-- Membership in the join of two subcoalgebras. -/
theorem mem_sup {D E : Subcoalgebra R C} {c : C} :
    c ∈ D ⊔ E ↔ ∃ d ∈ D, ∃ e ∈ E, d + e = c := by
  rw [← mem_toSubmodule, sup_toSubmodule, Submodule.mem_sup]
  rfl

/-- Subcoalgebras form a semilattice under the join whose carrier is the supremum of the
underlying submodules. -/
instance instSemilatticeSup : SemilatticeSup (Subcoalgebra R C) :=
  SemilatticeSup.mk (fun D E => D ⊔ E)
    (fun _ _ => by
      intro c hc
      rw [← mem_toSubmodule, sup_toSubmodule]
      exact Submodule.mem_sup_left ((mem_toSubmodule).2 hc))
    (fun _ _ => by
      intro c hc
      rw [← mem_toSubmodule, sup_toSubmodule]
      exact Submodule.mem_sup_right ((mem_toSubmodule).2 hc))
    (fun _ _ _ hD hE => by
      intro c hc
      rw [mem_sup] at hc
      rcases hc with ⟨d, hd, e, he, rfl⟩
      exact add_mem (hD hd) (hE he))

/-- The underlying submodule of a supremum of a set of subcoalgebras is the supremum of the
underlying submodules indexed by that set. -/
@[simp]
theorem sSup_toSubmodule (S : Set (Subcoalgebra R C)) :
    (sSup S).toSubmodule = ⨆ D : S, (D : Subcoalgebra R C).toSubmodule :=
  rfl

/-- Membership in the supremum of a set of subcoalgebras. -/
theorem mem_sSup {S : Set (Subcoalgebra R C)} {c : C} :
    c ∈ sSup S ↔
      ∃ f : S →₀ C, (∀ D : S, f D ∈ (D : Subcoalgebra R C)) ∧
        f.sum (fun _ x => x) = c := by
  rw [← mem_toSubmodule, sSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp
    (fun D : S => (D : Subcoalgebra R C).toSubmodule) c

/-- The underlying submodule of a supremum of subcoalgebras is the supremum of the
underlying submodules. -/
@[simp]
theorem iSup_toSubmodule {ι : Sort*} (D : ι → Subcoalgebra R C) :
    (⨆ i, D i).toSubmodule = ⨆ i, (D i).toSubmodule := by
  rw [iSup, sSup_toSubmodule]
  ext c
  simp [Submodule.mem_iSup]

/-- Membership in the supremum of a family of subcoalgebras. -/
theorem mem_iSup {ι : Type*} {D : ι → Subcoalgebra R C} {c : C} :
    c ∈ ⨆ i, D i ↔
      ∃ f : ι →₀ C, (∀ i, f i ∈ D i) ∧ f.sum (fun _ x => x) = c := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  exact Submodule.mem_iSup_iff_exists_finsupp (fun i => (D i).toSubmodule) c

/-- Membership in a nonempty directed supremum of subcoalgebras reduces to membership in one
member of the family. -/
theorem mem_iSup_of_directed {ι : Type*} [Nonempty ι] {D : ι → Subcoalgebra R C}
    (hD : Directed (· ≤ ·) D) {c : C} :
    c ∈ ⨆ i, D i ↔ ∃ i, c ∈ D i := by
  rw [← mem_toSubmodule, iSup_toSubmodule]
  apply Submodule.mem_iSup_of_directed
  intro i j
  obtain ⟨k, hik, hjk⟩ := hD i j
  exact ⟨k, toSubmodule_le_toSubmodule.2 hik, toSubmodule_le_toSubmodule.2 hjk⟩

/-- The carrier of a nonempty directed supremum of subcoalgebras is the union of their
carriers. -/
theorem coe_iSup_of_directed {ι : Type*} [Nonempty ι] {D : ι → Subcoalgebra R C}
    (hD : Directed (· ≤ ·) D) : ((⨆ i, D i : Subcoalgebra R C) : Set C) = ⋃ i, (D i : Set C) := by
  ext c
  simp only [SetLike.mem_coe, Set.mem_iUnion, mem_iSup_of_directed hD]

/-- Membership in the supremum of a nonempty directed set of subcoalgebras reduces to
membership in one member of the set. -/
theorem mem_sSup_of_directedOn {S : Set (Subcoalgebra R C)} (hne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {c : C} :
    c ∈ sSup S ↔ ∃ D ∈ S, c ∈ D := by
  haveI : Nonempty S := hne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hS.directed_val, SetCoe.exists, exists_prop]

/-- The carrier of the supremum of a nonempty directed set of subcoalgebras is the union of
their carriers. -/
theorem coe_sSup_of_directedOn {S : Set (Subcoalgebra R C)} (hne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(sSup S) : Set C) = ⋃ D ∈ S, (D : Set C) := by
  ext c
  simp [mem_sSup_of_directedOn hne hS]

/-- Subcoalgebras have arbitrary suprema, computed on underlying submodules. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Subcoalgebra R C) where
  sSup := sSup
  isLUB_sSup S :=
    ⟨fun D hD c hc => by
      rw [← mem_toSubmodule, sSup_toSubmodule]
      exact Submodule.mem_iSup_of_mem ⟨D, hD⟩ ((mem_toSubmodule).2 hc),
    fun D hD c hc => by
      rw [← mem_toSubmodule, sSup_toSubmodule] at hc
      rw [← mem_toSubmodule]
      have hle : (⨆ E : S, (E : Subcoalgebra R C).toSubmodule) ≤ D.toSubmodule := by
        refine iSup_le fun E : S => ?_
        exact toSubmodule_le_toSubmodule.2 (hD E.2)
      exact hle hc⟩

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
theorem sup_finite (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule := by
  rw [sup_toSubmodule, Module.Finite.iff_fg]
  exact (Module.Finite.iff_fg.mp inferInstance).sup (Module.Finite.iff_fg.mp inferInstance)

/-- The join of finitely generated subcoalgebras is finitely generated as an `R`-module. -/
instance instFiniteSup (D E : Subcoalgebra R C)
    [Module.Finite R D.toSubmodule] [Module.Finite R E.toSubmodule] :
    Module.Finite R (D ⊔ E).toSubmodule :=
  sup_finite D E

variable {ι : Type*}

/-- The underlying submodule of a finite join of subcoalgebras is the finite join of the
underlying submodules. -/
@[simp]
theorem finset_sup_toSubmodule (s : Finset ι) (D : ι → Subcoalgebra R C) :
    (s.sup D).toSubmodule = s.sup fun i => (D i).toSubmodule := by
  classical
  induction s using Finset.induction_on with
  | empty => exact bot_toSubmodule
  | insert a s _ ih =>
      rw [Finset.sup_insert, sup_toSubmodule, ih, Finset.sup_insert]

/-- Membership in a finite join of subcoalgebras. -/
theorem mem_finset_sup {s : Finset ι} {D : ι → Subcoalgebra R C} {c : C} :
    c ∈ s.sup D ↔ ∃ μ : ∀ i, (D i).toSubmodule, (∑ i ∈ s, (μ i : C)) = c := by
  rw [← mem_toSubmodule, finset_sup_toSubmodule]
  simpa only [Finset.sup_eq_iSup] using
    (Submodule.mem_iSup_finset_iff_exists_sum (fun i => (D i).toSubmodule) c)

/-- A finite supremum of finitely generated subcoalgebras is finitely generated as an
`R`-module. -/
theorem iSup_finite [Finite ι] (D : ι → Subcoalgebra R C)
    (hD : ∀ i, Module.Finite R (D i).toSubmodule) :
    Module.Finite R (⨆ i, D i).toSubmodule := by
  classical
  cases nonempty_fintype ι
  rw [iSup_toSubmodule, Module.Finite.iff_fg]
  simpa [Finset.sup_eq_iSup] using
    Submodule.fg_finset_sup Finset.univ (fun i => (D i).toSubmodule)
      fun i _ => Module.Finite.iff_fg.mp (hD i)

/-- A finite join of finitely generated subcoalgebras is finitely generated as an
`R`-module. -/
theorem finset_sup_finite (s : Finset ι) (D : ι → Subcoalgebra R C)
    (hD : ∀ i ∈ s, Module.Finite R (D i).toSubmodule) :
    Module.Finite R (s.sup D).toSubmodule := by
  classical
  rw [finset_sup_toSubmodule, Module.Finite.iff_fg]
  exact Submodule.fg_finset_sup s (fun i => (D i).toSubmodule)
    fun i hi => Module.Finite.iff_fg.mp (hD i hi)

end Subcoalgebra

end TauCeti
