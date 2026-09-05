/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.Perm.FiberSubgroup

/-!
# Young subgroups of symmetric groups

For a partition `μ` of `n`, this file defines its Young subgroup of `Equiv.Perm (Fin n)`.
The decreasing parts of `μ` cut `Fin n` into consecutive blocks, and the Young subgroup consists
exactly of the permutations preserving those blocks.  We identify it with the product of the
symmetric groups on the individual blocks and compute its cardinality and index.  Counting the
labels lying in the first `k` blocks recovers the partial sums of the decreasing parts
(`TauCeti.card_filter_youngBlock_lt`), which is the form in which the parts enter the dominance
order.

The Young subgroups of the shapes that have a name are computed here as well: the coarsest shape
`(n)` gives the whole symmetric group, the finest shape `(1ⁿ)` the trivial subgroup, and the shape
`(n+1, 1)` the stabilizer of the last label (`TauCeti.youngSubgroup_singletonSecondRow`), its two
blocks being all the labels but the last one and the last one alone.

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

/-- The labels whose `μ`-block is among the first `k` are as many as the first `k` parts of `μ`
add up to. -/
theorem card_filter_youngBlock_lt {n : ℕ} (μ : n.Partition) (k : ℕ) :
    (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) < k).card =
      ((μ.parts.sort (· ≥ ·)).take k).sum := by
  classical
  -- Each block of `μ` is the fiber of `youngBlock μ` over its label, and has the size of a part.
  have hfiber : ∀ i : ℕ, (Finset.univ.filter fun x : Fin n => (youngBlock μ x : ℕ) = i).card =
      (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro i
    by_cases hi : i < (μ.parts.sort (· ≥ ·)).length
    · rw [List.getD_eq_getElem _ _ hi, ← Fintype.card_subtype]
      refine (Fintype.card_congr ((youngBlockEquiv μ ⟨i, hi⟩).trans
        (Equiv.subtypeEquivRight fun x => ?_))).symm.trans (Fintype.card_fin _)
      exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi), Finset.card_eq_zero,
        Finset.filter_eq_empty_iff]
      exact fun x _ h => hi (h ▸ (youngBlock μ x).2)
  -- A partial sum of a list is the sum of its first entries, read off with `List.getD`.
  have hsum : ∀ m : ℕ, ((μ.parts.sort (· ≥ ·)).take m).sum =
      ∑ i ∈ Finset.range m, (μ.parts.sort (· ≥ ·)).getD i 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      rcases lt_or_ge m (μ.parts.sort (· ≥ ·)).length with h | h
      · rw [List.sum_take_succ _ _ h, List.getD_eq_getElem _ _ h]
      · rw [List.take_of_length_le h, List.take_of_length_le (h.trans (Nat.le_succ m)),
          List.getD_eq_default _ _ h, add_zero]
  -- Split the labels into blocks, and the partial sum into parts.
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin n => (youngBlock μ x : ℕ)) (t := Finset.range k) (fun x hx => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simpa using hx),
    hsum k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← hfiber i]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  exact fun h => h ▸ Finset.mem_range.mp hi

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

/-- The Young subgroup of the coarsest partition `(n)` is the whole symmetric group: its at most
one block imposes no condition. -/
@[simp]
theorem youngSubgroup_indiscrete (n : ℕ) :
    youngSubgroup (Nat.Partition.indiscrete n) = ⊤ :=
  Subgroup.eq_top_of_card_eq _ <| by
    rw [card_youngSubgroup, Nat.Partition.prod_map_factorial_indiscrete, Nat.card_perm,
      Nat.card_fin]

/-- The Young subgroup of the all-ones partition `(1ⁿ)` is trivial: every block is a singleton,
so only the identity preserves them all. -/
@[simp]
theorem youngSubgroup_ones (n : ℕ) : youngSubgroup (Nat.Partition.ones n) = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ <| by
    rw [card_youngSubgroup]
    simp

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

/-! ### The shape `(n+1, 1)`

The blocks of `Nat.Partition.singletonSecondRow n = (n+1, 1)` are the first `n+1` labels and the
last one, so its Young subgroup is the stabilizer of `Fin.last (n+1)`. -/

/-- Entries of the sorted parts of `(n+1, 1)`, in a form whose index is a bare natural number, so
that rewriting the sorted list does not disturb the bound on the index. -/
private theorem getElem_sort_parts_singletonSecondRow (n i : ℕ)
    (h : i < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length) :
    ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·))[i] = [n + 1, 1].getD i 0 := by
  rw [← List.getD_eq_getElem _ (0 : ℕ) h, Nat.Partition.sort_parts_singletonSecondRow]

/-- **The last label lies in the second block of the shape `(n+1, 1)`.**  The blocks are
consecutive with sizes `n+1` and `1`, so the block-coordinate equivalence sends the single
coordinate of the second block to `Fin.last (n+1)`. -/
@[simp]
theorem youngBlock_singletonSecondRow_last (n : ℕ) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) (Fin.last (n + 1))) : ℕ) = 1 := by
  have hlen : ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length = 2 := by
    rw [Nat.Partition.sort_parts_singletonSecondRow]
    rfl
  have h1 : (1 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).length := by omega
  have h0 : (0 : ℕ) < ((Nat.Partition.singletonSecondRow n).parts.sort (· ≥ ·)).get ⟨1, h1⟩ := by
    rw [List.get_eq_getElem, getElem_sort_parts_singletonSecondRow]
    simp
  have hlast : youngBlocksEquiv (Nat.Partition.singletonSecondRow n) ⟨⟨1, h1⟩, ⟨0, h0⟩⟩ =
      Fin.last (n + 1) := by
    refine Fin.ext ?_
    rw [youngBlocksEquiv_apply, Fin.sum_univ_one, List.get_eq_getElem,
      getElem_sort_parts_singletonSecondRow]
    simp
  rw [← hlast, youngBlock_youngBlocksEquiv]

/-- **Every other label lies in the first block of the shape `(n+1, 1)`.**  The first block has
`n+1` of the `n+2` labels, so its complement is the single label already located by
`TauCeti.youngBlock_singletonSecondRow_last`. -/
@[simp]
theorem youngBlock_singletonSecondRow_eq_zero (n : ℕ) {x : Fin (n + 2)}
    (hx : x ≠ Fin.last (n + 1)) :
    ((youngBlock (Nat.Partition.singletonSecondRow n) x) : ℕ) = 0 := by
  classical
  have hcard : (Finset.univ.filter fun y : Fin (n + 2) =>
      ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card = n + 1 := by
    rw [card_filter_youngBlock_lt, Nat.Partition.sort_parts_singletonSecondRow]
    simp
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 2))))
    (p := fun y => ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1))
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hsum
  by_contra hne
  have hx' : ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) x : ℕ) < 1) := by omega
  have hlt : 1 < (Finset.univ.filter fun y : Fin (n + 2) =>
      ¬ ((youngBlock (Nat.Partition.singletonSecondRow n) y : ℕ) < 1)).card :=
    Finset.one_lt_card.mpr ⟨x, by simpa using hx', Fin.last (n + 1), by simp, hx⟩
  omega

/-- **The Young subgroup of the shape `(n+1, 1)` is a point stabilizer.**  Its blocks are the last
label alone and all the others, so a permutation preserves them exactly when it fixes the last
label. -/
@[simp]
theorem youngSubgroup_singletonSecondRow (n : ℕ) :
    youngSubgroup (Nat.Partition.singletonSecondRow n) =
      MulAction.stabilizer (Equiv.Perm (Fin (n + 2))) (Fin.last (n + 1)) := by
  rw [youngSubgroup_eq_fiberSubgroup]
  refine fiberSubgroup_eq_stabilizer (fun x hx h => ?_) (fun x y hx hy => Fin.ext ?_)
  · have hv := congrArg Fin.val h
    rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_last] at hv
    exact absurd hv (by omega)
  · rw [youngBlock_singletonSecondRow_eq_zero n hx, youngBlock_singletonSecondRow_eq_zero n hy]

end TauCeti
