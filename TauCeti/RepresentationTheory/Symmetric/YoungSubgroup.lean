/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Young subgroups of symmetric groups

For a partition `μ` of `n`, this file defines its Young subgroup of `Equiv.Perm (Fin n)`.
The decreasing parts of `μ` cut `Fin n` into consecutive blocks, and the Young subgroup consists
exactly of the permutations preserving those blocks.  We identify it with the product of the
symmetric groups on the individual blocks and compute its cardinality and index.

The construction uses Mathlib's `finSigmaFinEquiv` to enumerate the consecutive blocks and
`Equiv.Perm.sigmaCongrRightHom` to combine independent permutations of them.

The consecutive-block design and the principal declaration signatures follow
`TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md` and its `Suggested.lean`.
-/

public section

namespace TauCeti

open Equiv

/-- The equivalence which enumerates the consecutive blocks whose sizes are the decreasing parts
of `μ`.

The coordinate `⟨i, j⟩` denotes position `j` in block `i`. -/
noncomputable def youngBlocksEquiv {n : ℕ} (μ : n.Partition) :
    (Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) ≃ Fin n :=
  finSigmaFinEquiv.trans <| finCongr <| by
    simp_rw [List.get_eq_getElem]
    rw [Fin.sum_univ_getElem, ← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]

/-- The consecutive-block equivalence sends a local coordinate to the preceding block sizes
plus that coordinate. -/
@[simp]
theorem youngBlocksEquiv_apply {n : ℕ} (μ : n.Partition)
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (youngBlocksEquiv μ x : ℕ) =
      ∑ i : Fin x.1,
        (μ.parts.sort (· ≥ ·)).get (Fin.castLE x.1.2.le i) + x.2 := by
  simp [youngBlocksEquiv]

/-- The block containing an element of `Fin n`. -/
noncomputable def youngBlock {n : ℕ} (μ : n.Partition) (j : Fin n) :
    Fin (μ.parts.sort (· ≥ ·)).length :=
  ((youngBlocksEquiv μ).symm j).1

/-- The block-coordinate equivalence sends a local coordinate to its block label. -/
@[simp]
theorem youngBlock_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    youngBlock μ (youngBlocksEquiv μ x) = x.1 := by
  simp [youngBlock]

private noncomputable def youngSubgroupHom {n : ℕ} (μ : n.Partition) :
    (∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i))) →*
      Equiv.Perm (Fin n) :=
  (youngBlocksEquiv μ).permCongrHom.toMonoidHom.comp <|
    Equiv.Perm.sigmaCongrRightHom fun i =>
      Fin ((μ.parts.sort (· ≥ ·)).get i)

private theorem youngSubgroupHom_injective {n : ℕ} (μ : n.Partition) :
    Function.Injective (youngSubgroupHom μ) :=
  (youngBlocksEquiv μ).permCongrHom.injective.comp
    Equiv.Perm.sigmaCongrRightHom_injective

private theorem youngSubgroupHom_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (p : ∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i)))
    (x : Σ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    youngSubgroupHom μ p (youngBlocksEquiv μ x) =
      youngBlocksEquiv μ ⟨x.1, p x.1 x.2⟩ := by
  simp [youngSubgroupHom]

/-- The Young subgroup associated to `μ`, acting independently on the consecutive blocks whose
sizes are the decreasing parts of `μ`. -/
noncomputable def youngSubgroup {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (youngSubgroupHom μ).range

/-- The Young subgroup is the product of the symmetric groups on its consecutive blocks. -/
noncomputable def youngSubgroupMulEquiv {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ ≃*
      (∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
        Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i))) :=
  (MonoidHom.ofInjective (youngSubgroupHom_injective μ)).symm

private theorem youngSubgroupMulEquiv_symm_apply {n : ℕ} (μ : n.Partition)
    (p : ∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i))) :
    ((youngSubgroupMulEquiv μ).symm p : Equiv.Perm (Fin n)) =
      youngSubgroupHom μ p :=
  MonoidHom.ofInjective_apply (youngSubgroupHom_injective μ)

/-- The inverse product decomposition acts on each consecutive block by the corresponding
permutation. -/
@[simp]
theorem youngSubgroupMulEquiv_symm_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (p : ∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
      Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i)))
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    ((youngSubgroupMulEquiv μ).symm p : Equiv.Perm (Fin n))
        (youngBlocksEquiv μ ⟨i, j⟩) =
      youngBlocksEquiv μ ⟨i, p i j⟩ := by
  rw [youngSubgroupMulEquiv_symm_apply]
  exact youngSubgroupHom_apply_youngBlocksEquiv μ p ⟨i, j⟩

/-- The product decomposition records the local coordinate induced on each consecutive block. -/
@[simp]
theorem youngSubgroupMulEquiv_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (youngBlocksEquiv μ).symm
        ((σ : Equiv.Perm (Fin n)) (youngBlocksEquiv μ ⟨i, j⟩)) =
      ⟨i, (youngSubgroupMulEquiv μ σ) i j⟩ := by
  have h := youngSubgroupMulEquiv_symm_apply_youngBlocksEquiv μ
    (youngSubgroupMulEquiv μ σ) i j
  rw [MulEquiv.symm_apply_apply] at h
  apply (youngBlocksEquiv μ).injective
  simpa using h

/-- The local coordinates in block `i` are equivalent to the fiber of `youngBlock μ` over `i`. -/
noncomputable def youngBlockEquiv {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)]) ≃
      {j : Fin n // youngBlock μ j = i} :=
  Equiv.ofBijective
    (fun j => ⟨youngBlocksEquiv μ ⟨i, j⟩, youngBlock_youngBlocksEquiv μ ⟨i, j⟩⟩)
    ⟨by
      intro a b h
      have hs : (⟨i, a⟩ : Σ k, Fin ((μ.parts.sort (· ≥ ·)).get k)) = ⟨i, b⟩ :=
        (youngBlocksEquiv μ).injective (Subtype.ext_iff.mp h)
      cases hs
      rfl,
    by
      rintro ⟨j, hj⟩
      obtain ⟨⟨k, x⟩, rfl⟩ := (youngBlocksEquiv μ).surjective j
      simp only [youngBlock_youngBlocksEquiv] at hj
      subst k
      exact ⟨x, rfl⟩⟩

/-- The block-fiber equivalence is the consecutive-block equivalence with its block-membership
proof. -/
@[simp]
theorem youngBlockEquiv_apply {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)])) :
    youngBlockEquiv μ i j =
      ⟨youngBlocksEquiv μ ⟨i, j⟩, youngBlock_youngBlocksEquiv μ ⟨i, j⟩⟩ :=
  Subtype.ext rfl

private theorem prod_factorial_sorted_parts {n : ℕ} (μ : n.Partition) :
    (∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
        ((μ.parts.sort (· ≥ ·)).get i).factorial) =
      (μ.parts.map Nat.factorial).prod := by
  simp_rw [List.get_eq_getElem]
  rw [Fin.prod_univ_fun_getElem, ← Multiset.prod_coe, ← Multiset.map_coe,
    Multiset.sort_eq]

/-- The order of a Young subgroup is the product of the factorials of the parts. -/
theorem card_youngSubgroup {n : ℕ} (μ : n.Partition) :
    Nat.card (youngSubgroup μ) = (μ.parts.map Nat.factorial).prod := by
  rw [Nat.card_congr (youngSubgroupMulEquiv μ).toEquiv, Nat.card_pi]
  simp only [Nat.card_perm, Nat.card_fin]
  exact prod_factorial_sorted_parts μ

private noncomputable def youngBlockStabilizer {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ)).unop

private theorem mem_youngBlockStabilizer_iff {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngBlockStabilizer μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  change DomMulAct.mk σ ∈
    MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ) ↔ _
  exact DomMulAct.mem_stabilizer_iff

private theorem card_youngBlockStabilizer {n : ℕ} (μ : n.Partition) :
    Nat.card (youngBlockStabilizer μ) =
      (μ.parts.map Nat.factorial).prod := by
  let e : youngBlockStabilizer μ ≃
      {σ : Equiv.Perm (Fin n) // youngBlock μ ∘ σ = youngBlock μ} :=
    Equiv.subtypeEquiv (Equiv.refl _) (mem_youngBlockStabilizer_iff μ)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  calc
    (∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
        (Fintype.card {j : Fin n // youngBlock μ j = i}).factorial) =
        ∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
          ((μ.parts.sort (· ≥ ·)).get i).factorial := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.card_congr (youngBlockEquiv μ i).symm]
      simp
    _ = (μ.parts.map Nat.factorial).prod := prod_factorial_sorted_parts μ

/-- Membership in the Young subgroup is equivalent to preserving the consecutive-block label. -/
@[simp]
theorem mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  have hle : youngSubgroup μ ≤ youngBlockStabilizer μ := by
    intro a ha
    obtain ⟨p, rfl⟩ := ha
    rw [mem_youngBlockStabilizer_iff]
    ext j
    obtain ⟨x, rfl⟩ := (youngBlocksEquiv μ).surjective j
    simp only [Function.comp_apply, youngSubgroupHom_apply_youngBlocksEquiv,
      youngBlock_youngBlocksEquiv]
  have hcard :
      Nat.card (youngBlockStabilizer μ) ≤ Nat.card (youngSubgroup μ) := by
    rw [card_youngBlockStabilizer, card_youngSubgroup]
  have heq : youngSubgroup μ = youngBlockStabilizer μ :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq, mem_youngBlockStabilizer_iff]

/-- The index of a Young subgroup times its order is `n!`. -/
theorem youngSubgroup_index_mul {n : ℕ} (μ : n.Partition) :
    (youngSubgroup μ).index * (μ.parts.map Nat.factorial).prod = n.factorial := by
  rw [← card_youngSubgroup, Subgroup.index_mul_card, Nat.card_perm, Nat.card_fin]

/-- The index of a Young subgroup is the multinomial quotient by the factorials of the parts. -/
theorem youngSubgroup_index {n : ℕ} (μ : n.Partition) :
    (youngSubgroup μ).index =
      n.factorial / (μ.parts.map Nat.factorial).prod :=
  Nat.eq_div_of_mul_eq_right
    (by
      apply Multiset.prod_ne_zero
      intro h
      obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp h
      exact Nat.factorial_ne_zero x hx)
    (by simpa only [mul_comm] using youngSubgroup_index_mul μ)

end TauCeti
