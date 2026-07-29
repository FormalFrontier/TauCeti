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
  change youngSubgroupHom μ p (youngBlocksEquiv μ ⟨i, j⟩) = _
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

/-- The order of a Young subgroup is the product of the factorials of the parts. -/
theorem card_youngSubgroup {n : ℕ} (μ : n.Partition) :
    Nat.card (youngSubgroup μ) = (μ.parts.map Nat.factorial).prod := by
  rw [Nat.card_congr (youngSubgroupMulEquiv μ).toEquiv, Nat.card_pi]
  simp only [Nat.card_perm, Nat.card_fin]
  simp_rw [List.get_eq_getElem]
  rw [Fin.prod_univ_fun_getElem, ← Multiset.prod_coe, ← Multiset.map_coe,
    Multiset.sort_eq]

private theorem card_youngBlock_stabilizer {n : ℕ} (μ : n.Partition) :
    Nat.card
        {σ : Equiv.Perm (Fin n) //
          youngBlock μ ∘ σ = youngBlock μ} =
      (μ.parts.map Nat.factorial).prod := by
  rw [Nat.card_eq_fintype_card, DomMulAct.stabilizer_card]
  calc
    (∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
        (Fintype.card {j : Fin n // youngBlock μ j = i}).factorial) =
        ∏ i : Fin (μ.parts.sort (· ≥ ·)).length,
          ((μ.parts.sort (· ≥ ·)).get i).factorial := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.card_congr (youngBlockEquiv μ i).symm]
      simp
    _ = (μ.parts.map Nat.factorial).prod := by
      simp_rw [List.get_eq_getElem]
      rw [Fin.prod_univ_fun_getElem, ← Multiset.prod_coe, ← Multiset.map_coe,
        Multiset.sort_eq]

/-- Membership in the Young subgroup is equivalent to preserving the consecutive-block label. -/
@[simp]
theorem mem_youngSubgroup_iff {n : ℕ} (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    σ ∈ youngSubgroup μ ↔ youngBlock μ ∘ σ = youngBlock μ := by
  let K : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {σ | youngBlock μ ∘ σ = youngBlock μ}
      one_mem' := by ext j; rfl
      mul_mem' := by
        intro a b ha hb
        apply funext
        intro j
        simpa only [Function.comp_apply, Equiv.Perm.mul_apply] using
          (congrFun ha (b j)).trans (congrFun hb j)
      inv_mem' := by
        intro a ha
        apply funext
        intro j
        simpa only [Function.comp_apply, Equiv.Perm.coe_inv, Equiv.apply_symm_apply] using
          (congrFun ha (a.symm j)).symm }
  have hle : youngSubgroup μ ≤ K := by
    intro a ha
    obtain ⟨p, rfl⟩ := ha
    ext j
    obtain ⟨x, rfl⟩ := (youngBlocksEquiv μ).surjective j
    simp only [Function.comp_apply, youngSubgroupHom_apply_youngBlocksEquiv,
      youngBlock_youngBlocksEquiv]
  have hcardK : Nat.card K = (μ.parts.map Nat.factorial).prod := by
    let e : K ≃
        {σ : Equiv.Perm (Fin n) // youngBlock μ ∘ σ = youngBlock μ} :=
      { toFun := fun σ => ⟨σ.1, σ.2⟩
        invFun := fun σ => ⟨σ.1, σ.2⟩
        left_inv := fun σ => Subtype.ext rfl
        right_inv := fun σ => Subtype.ext rfl }
    exact (Nat.card_congr e).trans (card_youngBlock_stabilizer μ)
  have hcard : Nat.card K ≤ Nat.card (youngSubgroup μ) := by
    rw [hcardK, card_youngSubgroup]
  have heq : youngSubgroup μ = K :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [heq]
  rfl

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
