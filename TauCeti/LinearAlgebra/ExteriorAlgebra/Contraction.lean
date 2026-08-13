/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

private theorem contractLeft_ιMulti_eq_zero {n : ℕ}
    (d : Module.Dual R M) (v : Fin n → M) (h : ∀ i, d (v i) = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R n v) = 0 := by
  induction n with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact contractLeft_one (Q := (0 : QuadraticForm R M)) d
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, h 0, zero_smul,
        ih (Matrix.vecTail v) (fun i ↦ h i.succ), mul_zero, sub_zero]

private theorem contractLeft_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply]
  apply contractLeft_ιMulti_eq_zero
  intro j
  simp only [Function.comp_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · exfalso
    apply hi
    rw [← h]
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.prodEquiv.symm s).2
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2 j)).mp
      ⟨j, rfl⟩
    exact hj
  · rfl

private theorem basis_exteriorAlgebra_singleton_eq_ι {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  let a : Set.powersetCard I 1 :=
    Set.powersetCard.ofCard (s := {i}) (Finset.card_singleton i)
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  rw [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    a (Set.powersetCard.ofFinEmbEquiv.symm a 0)).mp ⟨0, rfl⟩
  have hj' : Set.powersetCard.ofFinEmbEquiv.symm a 0 ∈ ({i} : Finset I) := hj
  have heq : Set.powersetCard.ofFinEmbEquiv.symm a 0 = i := Finset.eq_of_mem_singleton hj'
  exact congrArg (fun j ↦ ExteriorAlgebra.ι R (b j)) heq

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate. -/
@[simp]
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  split_ifs with hi
  · let a : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
    let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
    have hdisj : Disjoint a.val t.val := by simp [a, t]
    have hunion : Set.powersetCard.disjUnion hdisj =
        (Set.powersetCard.ofCard (s := s) (by
          rw [Finset.card_erase_of_mem hi]
          have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
      apply Subtype.ext
      simp [Set.powersetCard.disjUnion, a, t, hi]
    have hprod := ExteriorAlgebra.basis_mul_of_disjoint b a t hdisj
    rw [hunion] at hprod
    simp only [a, t, Set.powersetCard.val_ofCard] at hprod
    have hfixed : ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
          (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) := by
      rw [basis_exteriorAlgebra_singleton_eq_ι]
      rw [contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rw [hprod] at hfixed
    rcases Int.units_eq_one_or (Equiv.Perm.sign
      (Set.powersetCard.permOfDisjoint hdisj)) with hsign | hsign <;>
      rw [hsign] at hfixed <;> simpa using hfixed
  · rw [contractLeft_basis_eq_zero_of_not_mem b i s hi, mul_zero]

end TauCeti.ExteriorAlgebra
