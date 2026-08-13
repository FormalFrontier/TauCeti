/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction

/-!
# Exterior creation and contraction generate all endomorphisms

For a finite free module, left exterior multiplication and contraction by dual vectors generate
the full endomorphism algebra of its exterior algebra.

## Main result

* `TauCeti.ExteriorAlgebra.creation_contraction_adjoin_eq_top`: creation and contraction generate
  every endomorphism.

## References

* [Spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md)
-/

public section

open Module CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v

variable {K : Type u} [CommRing K] {W : Type v} [AddCommGroup W] [Module K W]

private noncomputable def occupationProjection {n : ℕ} (b : Module.Basis (Fin n) K W)
    (i : Fin n) : Module.End K (ExteriorAlgebra K W) :=
  (LinearMap.mulLeft K ((ExteriorAlgebra.ι K) (b i))).comp
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) (b.coord i))

private noncomputable def vacancyProjection {n : ℕ} (b : Module.Basis (Fin n) K W)
    (i : Fin n) : Module.End K (ExteriorAlgebra K W) :=
  LinearMap.id - occupationProjection b i

private noncomputable def basisProjection {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : Module.End K (ExteriorAlgebra K W) :=
  List.prod ((List.ofFn fun i : Fin n ↦ i).map fun i ↦
    if i ∈ s then occupationProjection b i else vacancyProjection b i)

private noncomputable def actionRange {n : ℕ} (b : Module.Basis (Fin n) K W) :
    Subalgebra K (Module.End K (ExteriorAlgebra K W)) :=
  Algebra.adjoin K
    (Set.range fun i : Fin n ↦
      (LinearMap.mulLeft K ((ExteriorAlgebra.ι K) (b i)) : Module.End K _) ) ⊔
  Algebra.adjoin K
    (Set.range fun i : Fin n ↦
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) (b.coord i) : Module.End K _))

private theorem occupationProjection_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (i : Fin n) : occupationProjection b i ∈ actionRange b := by
  apply (actionRange b).mul_mem
  -- View each generator algebra through its inclusion into `actionRange`.
  · exact (show Algebra.adjoin K _ ≤ actionRange b from le_sup_left)
      (Algebra.subset_adjoin (Set.mem_range_self i))
  · exact (show Algebra.adjoin K _ ≤ actionRange b from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_range_self i))

private theorem vacancyProjection_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (i : Fin n) : vacancyProjection b i ∈ actionRange b := by
  exact (actionRange b).sub_mem (actionRange b).one_mem
    (occupationProjection_mem_actionRange b i)

private theorem basisProjection_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : basisProjection b s ∈ actionRange b := by
  rw [basisProjection]
  apply Submonoid.list_prod_mem
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
  split_ifs
  · exact occupationProjection_mem_actionRange b i
  · exact vacancyProjection_mem_actionRange b i

private theorem vacancyProjection_basis {n : ℕ}
    (b : Module.Basis (Fin n) K W) (i : Fin n) (s : Finset (Fin n)) :
    vacancyProjection b i (b.ExteriorAlgebra s) =
      if i ∈ s then 0 else b.ExteriorAlgebra s := by
  rw [vacancyProjection, LinearMap.sub_apply, LinearMap.id_apply, occupationProjection,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, ι_mul_contractLeft_coord_basis]
  split_ifs <;> simp

private theorem basisFactor_apply {n : ℕ}
    (b : Module.Basis (Fin n) K W) (s t : Finset (Fin n)) (i : Fin n) :
    (if i ∈ s then occupationProjection b i else vacancyProjection b i)
        (b.ExteriorAlgebra t) =
      (if (i ∈ s ↔ i ∈ t) then 1 else 0) • b.ExteriorAlgebra t := by
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp [his, hit, occupationProjection, ι_mul_contractLeft_coord_basis,
      vacancyProjection_basis]

private theorem listProd_basisFactor_apply {n : ℕ}
    (b : Module.Basis (Fin n) K W) (s t : Finset (Fin n)) (l : List (Fin n)) :
    (l.map (fun i ↦ if i ∈ s then occupationProjection b i else vacancyProjection b i)).prod
        (b.ExteriorAlgebra t) =
      (List.prod (l.map (fun i ↦ (if (i ∈ s ↔ i ∈ t) then 1 else 0 : K))) •
        b.ExteriorAlgebra t) := by
  induction l with
  | nil => simp
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
        basisFactor_apply]
      simp

private theorem basisProjection_basis {n : ℕ}
    (b : Module.Basis (Fin n) K W) (s t : Finset (Fin n)) :
    basisProjection b s (b.ExteriorAlgebra t) =
      if s = t then b.ExteriorAlgebra t else 0 := by
  rw [basisProjection, listProd_basisFactor_apply]
  by_cases hst : s = t
  · subst t
    simp only [iff_self, ite_true]
    have hall : (List.ofFn fun i : Fin n ↦ i).map (fun _ ↦ (1 : K)) =
        List.replicate n 1 := by
      apply List.eq_replicate_iff.mpr
      simp
    rw [hall, List.prod_replicate, one_pow, one_smul]
  · have hdiff : ∃ i : Fin n, ¬ (i ∈ s ↔ i ∈ t) := by
      contrapose! hst
      exact Finset.ext hst
    obtain ⟨i, hi⟩ := hdiff
    have hzero : (0 : K) ∈
        (List.ofFn fun i : Fin n ↦ i).map
          (fun i ↦ (if (i ∈ s ↔ i ∈ t) then 1 else 0 : K)) := by
      apply List.mem_map.mpr
      exact ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, by simp [hi]⟩
    rw [ite_eq_right hst]
    rw [List.prod_eq_zero hzero, zero_smul]

private noncomputable def create {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : Module.End K (ExteriorAlgebra K W) :=
  List.prod ((List.ofFn fun j : Fin s.card ↦
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2 j).map
      fun i ↦ (LinearMap.mulLeft K ((ExteriorAlgebra.ι K) (b i)) : Module.End K _))

private noncomputable def annihilate {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : Module.End K (ExteriorAlgebra K W) :=
  List.prod (((List.ofFn fun j : Fin s.card ↦
    Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2 j).map
      fun i ↦ (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W))
        (b.coord i) : Module.End K _)).reverse)

private theorem create_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : create b s ∈ actionRange b := by
  rw [create]
  apply Submonoid.list_prod_mem
  intro f hf
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf
  -- View the creation algebra through its inclusion into `actionRange`.
  exact (show Algebra.adjoin K _ ≤ actionRange b from le_sup_left)
    (Algebra.subset_adjoin (Set.mem_range_self i))

private theorem annihilate_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) : annihilate b s ∈ actionRange b := by
  rw [annihilate]
  apply Submonoid.list_prod_mem
  intro f hf
  have hf' : f ∈ (List.ofFn fun j : Fin s.card ↦
      Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.prodEquiv.symm s).2 j).map
        fun i ↦ (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W))
          (b.coord i) : Module.End K _) := by simpa using hf
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hf'
  -- View the contraction algebra through its inclusion into `actionRange`.
  exact (show Algebra.adjoin K _ ≤ actionRange b from le_sup_right)
    (Algebra.subset_adjoin (Set.mem_range_self i))

private noncomputable def matrixUnit {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s t : Finset (Fin n)) : Module.End K (ExteriorAlgebra K W) :=
  create b s * annihilate b t * basisProjection b t

private theorem matrixUnit_mem_actionRange {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s t : Finset (Fin n)) : matrixUnit b s t ∈ actionRange b :=
  (actionRange b).mul_mem
    ((actionRange b).mul_mem (create_mem_actionRange b s) (annihilate_mem_actionRange b t))
    (basisProjection_mem_actionRange b t)

private theorem create_basis_empty {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) :
    create b s (b.ExteriorAlgebra ∅) = b.ExteriorAlgebra s := by
  have hEmpty : b.ExteriorAlgebra (∅ : Finset (Fin n)) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  rw [create, hEmpty, ExteriorAlgebra.basis_apply]
  have hmap (xs : List (Fin n)) :
      (xs.map (fun i ↦ LinearMap.mulLeft K (ExteriorAlgebra.ι K (b i)))).prod 1 =
        (xs.map fun i ↦ ExteriorAlgebra.ι K (b i)).prod := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [ih, Module.End.mul_apply]
  rw [hmap]
  -- Expose the `ιMulti` family underlying the exterior basis vector.
  change _ = ExteriorAlgebra.ιMulti K s.card
    (b ∘ Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.prodEquiv.symm s).2)
  rw [ExteriorAlgebra.ιMulti_apply]
  rw [List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.mpr
  rfl

private theorem contractLeft_listProd_eq_zero_of_not_mem {n : ℕ}
    (b : Module.Basis (Fin n) K W) (i : Fin n) (xs : List (Fin n)) (hi : i ∉ xs) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) (b.coord i)
      (xs.map fun j ↦ ExteriorAlgebra.ι K (b j)).prod = 0 := by
  induction xs with
  | nil => exact CliffordAlgebra.contractLeft_one (Q := (0 : QuadraticForm K W)) (b.coord i)
  | cons j xs ih =>
      rw [List.map_cons, List.prod_cons, CliffordAlgebra.contractLeft_ι_mul]
      have hij : i ≠ j := by
        intro h
        exact hi (by simp [h])
      have hit : i ∉ xs := by
        intro h
        exact hi (by simp [h])
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [ite_eq_right hij.symm]
      rw [zero_smul, ih hit, mul_zero, sub_zero]

private theorem annihilate_listProd_self {n : ℕ}
    (b : Module.Basis (Fin n) K W) (xs : List (Fin n)) (hxs : xs.Nodup) :
    (xs.map fun i ↦ (CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm K W)) (b.coord i) : Module.End K _)).reverse.prod
      (xs.map fun i ↦ ExteriorAlgebra.ι K (b i)).prod = 1 := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
        Module.End.mul_apply]
      -- Expose application of the bundled endomorphism product.
      change (xs.map fun i ↦ (CliffordAlgebra.contractLeft
        (Q := (0 : QuadraticForm K W)) (b.coord i) : Module.End K _)).reverse.prod
          ((CliffordAlgebra.contractLeft
            (Q := (0 : QuadraticForm K W)) (b.coord i))
              (ExteriorAlgebra.ι K (b i) *
                (xs.map fun j ↦ ExteriorAlgebra.ι K (b j)).prod)) = 1
      rw [CliffordAlgebra.contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_listProd_eq_zero_of_not_mem b i xs hxs.notMem, mul_zero, sub_zero]
      simp only [ite_true, one_smul]
      rw [ih hxs.tail]

private theorem annihilate_basis_self {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s : Finset (Fin n)) :
    annihilate b s (b.ExteriorAlgebra s) = b.ExteriorAlgebra ∅ := by
  have hEmpty : b.ExteriorAlgebra (∅ : Finset (Fin n)) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  rw [annihilate, ExteriorAlgebra.basis_apply, hEmpty]
  -- Expose `annihilate` as its reversed product of contraction maps.
  change ((List.map (fun i ↦ (CliffordAlgebra.contractLeft
      (Q := (0 : QuadraticForm K W)) (b.coord i) : Module.End K _))
      (List.ofFn fun j : Fin s.card ↦
        Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.prodEquiv.symm s).2 j)).reverse.prod)
    (ExteriorAlgebra.ιMulti K s.card
    (b ∘ Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.prodEquiv.symm s).2)) = 1
  rw [ExteriorAlgebra.ιMulti_apply]
  -- Put the contraction and exterior products in the same list representation.
  change ((List.ofFn fun j : Fin s.card ↦
      Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.prodEquiv.symm s).2 j).map fun i ↦
          (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W))
            (b.coord i) : Module.End K _)).reverse.prod
    ((List.ofFn fun j : Fin s.card ↦
      ExteriorAlgebra.ι K (b (Set.powersetCard.ofFinEmbEquiv.symm
        (Set.powersetCard.prodEquiv.symm s).2 j))).prod) = 1
  let xs := List.ofFn fun j : Fin s.card ↦ Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.prodEquiv.symm s).2 j
  have hxmap : xs.map (fun i ↦ ExteriorAlgebra.ι K (b i)) =
      List.ofFn (fun j : Fin s.card ↦ ExteriorAlgebra.ι K
        (b (Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.prodEquiv.symm s).2 j))) := by
    dsimp only [xs]
    rw [List.map_ofFn]
    congr 1
  rw [← hxmap]
  apply annihilate_listProd_self b xs
  exact List.nodup_ofFn.mpr
    (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.prodEquiv.symm s).2).injective

private theorem matrixUnit_basis {n : ℕ} (b : Module.Basis (Fin n) K W)
    (s t u : Finset (Fin n)) :
    matrixUnit b s t (b.ExteriorAlgebra u) =
      if t = u then b.ExteriorAlgebra s else 0 := by
  rw [matrixUnit, Module.End.mul_apply, Module.End.mul_apply, basisProjection_basis]
  split_ifs with h
  · subst u
    rw [annihilate_basis_self, create_basis_empty]
  · rw [map_zero, map_zero]

private theorem actionRange_eq_top {n : ℕ} (b : Module.Basis (Fin n) K W) :
    actionRange b = ⊤ := by
  apply top_unique
  intro f _
  rw [← b.ExteriorAlgebra.end.sum_repr f]
  apply Submodule.sum_mem (p := (actionRange b).toSubmodule)
  intro st _
  -- Replace the basis matrix by the pointwise-equal constructed matrix unit.
  rw [show b.ExteriorAlgebra.end.repr f st • b.ExteriorAlgebra.end st =
      b.ExteriorAlgebra.end.repr f st • matrixUnit b st.1 st.2 by
    apply b.ExteriorAlgebra.ext
    intro u
    simp only [LinearMap.smul_apply]
    rw [Module.Basis.end_apply_apply]
    rw [matrixUnit_basis]]
  exact (actionRange b).smul_mem (matrixUnit_mem_actionRange b st.1 st.2) _

/-- Exterior creation and contraction generate every endomorphism of a finite free module's
exterior algebra. -/
theorem creation_contraction_adjoin_eq_top [Module.Free K W] [Module.Finite K W] :
    Algebra.adjoin K
      (Set.range (fun x : W ↦
        (LinearMap.mulLeft K (ExteriorAlgebra.ι K x) : Module.End K (ExteriorAlgebra K W))) ∪
       Set.range (fun d : Module.Dual K W ↦
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm K W)) d :
          Module.End K (ExteriorAlgebra K W)))) = ⊤ := by
  let _ := Fintype.ofFinite (Module.Free.ChooseBasisIndex K W)
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex K W))) K W :=
    (Module.Free.chooseBasis K W).reindex (Fintype.equivFin _)
  apply top_unique
  rw [← actionRange_eq_top b]
  apply sup_le
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin (Or.inl ⟨b i, rfl⟩)
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin (Or.inr ⟨b.coord i, rfl⟩)

end TauCeti.ExteriorAlgebra
