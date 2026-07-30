/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.DomMulAct
public import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# Young subgroups of symmetric groups

For a partition `μ` of `n`, this file defines its Young subgroup of `Equiv.Perm (Fin n)`.
The decreasing parts of `μ` cut `Fin n` into consecutive blocks, and the Young subgroup consists
exactly of the permutations preserving those blocks.  We identify it with the product of the
symmetric groups on the individual blocks and compute its cardinality and index.

The construction uses Mathlib's `finSigmaFinEquiv` to enumerate the consecutive blocks and
`DomMulAct.stabilizerMulEquiv` to decompose their stabilizer.

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

private theorem youngBlockEquiv_val {n : ℕ} (μ : n.Partition)
    (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·))[(i : ℕ)])) :
    (youngBlockEquiv μ i j).1 = youngBlocksEquiv μ ⟨i, j⟩ := by
  simpa only using congrArg Subtype.val (youngBlockEquiv_apply μ i j)

/-- The Young subgroup associated to `μ`, acting independently on the consecutive blocks whose
sizes are the decreasing parts of `μ`. -/
noncomputable def youngSubgroup {n : ℕ} (μ : n.Partition) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ)).unop

private noncomputable def youngSubgroupStabilizerMulEquiv {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ ≃*
      (MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ))ᵐᵒᵖ where
  toFun σ := MulOpposite.op ⟨DomMulAct.mk σ, σ.prop⟩
  invFun σ := ⟨DomMulAct.mk.symm σ.unop, σ.unop.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem mem_youngSubgroup_stabilizer_iff {n : ℕ} (μ : n.Partition)
    (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔
      DomMulAct.mk σ ∈
        MulAction.stabilizer (Equiv.Perm (Fin n))ᵈᵐᵃ (youngBlock μ) :=
  Iff.rfl

/-- The Young subgroup is the product of the symmetric groups on its consecutive blocks. -/
noncomputable def youngSubgroupMulEquiv {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ ≃*
      (∀ i : Fin (μ.parts.sort (· ≥ ·)).length,
        Equiv.Perm (Fin ((μ.parts.sort (· ≥ ·)).get i))) :=
  (youngSubgroupStabilizerMulEquiv μ).trans <|
    (DomMulAct.stabilizerMulEquiv (youngBlock μ)).trans <|
      MulEquiv.piCongrRight fun i => (youngBlockEquiv μ i).symm.permCongrHom

private theorem youngSubgroupStabilizerMulEquiv_apply {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) :
    DomMulAct.mk.symm (youngSubgroupStabilizerMulEquiv μ σ).unop =
      (σ : Equiv.Perm (Fin n)) :=
  rfl

private theorem youngSubgroupMulEquiv_apply {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) (i : Fin (μ.parts.sort (· ≥ ·)).length) :
    youngSubgroupMulEquiv μ σ i =
      (youngBlockEquiv μ i).symm.permCongrHom
        ((DomMulAct.stabilizerMulEquiv (youngBlock μ))
          (youngSubgroupStabilizerMulEquiv μ σ) i) :=
  rfl

/-- The product decomposition records the local coordinate induced on each consecutive block. -/
@[simp]
theorem youngSubgroupMulEquiv_apply_youngBlocksEquiv {n : ℕ} (μ : n.Partition)
    (σ : youngSubgroup μ) (i : Fin (μ.parts.sort (· ≥ ·)).length)
    (j : Fin ((μ.parts.sort (· ≥ ·)).get i)) :
    (youngBlocksEquiv μ).symm
        ((σ : Equiv.Perm (Fin n)) (youngBlocksEquiv μ ⟨i, j⟩)) =
      ⟨i, (youngSubgroupMulEquiv μ σ) i j⟩ := by
  apply (youngBlocksEquiv μ).injective
  rw [Equiv.apply_symm_apply]
  rw [← youngBlockEquiv_val μ i ((youngSubgroupMulEquiv μ σ) i j)]
  have h := DomMulAct.stabilizerMulEquiv_apply
    (youngSubgroupStabilizerMulEquiv μ σ) (youngBlock_youngBlocksEquiv μ ⟨i, j⟩)
  rw [youngSubgroupStabilizerMulEquiv_apply] at h
  rw [← h]
  rw [← youngBlockEquiv_apply μ i j, youngSubgroupMulEquiv_apply]
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

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
  apply (youngBlocksEquiv μ).symm.injective
  rw [Equiv.symm_apply_apply, youngSubgroupMulEquiv_apply_youngBlocksEquiv,
    MulEquiv.apply_symm_apply]

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

/-- Membership in the Young subgroup is equivalent to preserving the consecutive-block label. -/
@[simp]
theorem mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  rw [mem_youngSubgroup_stabilizer_iff]
  exact DomMulAct.mem_stabilizer_iff

/-- The Young subgroup is the subgroup preserving the fibers of its consecutive-block map. -/
theorem youngSubgroup_eq_fiberSubgroup {n : ℕ} (μ : n.Partition) :
    youngSubgroup μ = fiberSubgroup (youngBlock μ) := by
  ext σ
  rw [mem_youngSubgroup_iff, mem_fiberSubgroup]
  simp only [funext_iff, Function.comp_apply]

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
