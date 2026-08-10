/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.List.Sym
public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Auditable Coxeter relator lists and the Y-diagrams

A Coxeter presentation is normally published as a diagram: a set of involutions, one per node, with
a braid relation on each edge and a commuting relation on each non-edge. Mathlib turns a
`CoxeterMatrix` into a group through `CoxeterMatrix.relationsSet`, the *range* of
`CoxeterMatrix.relation`, which is a set indexed by ordered pairs rather than an explicit list whose
entries and length a reviewer can audit. This file produces that finite relator list, one relator
per unordered pair of nodes, the diagonal included, so that the `n` involution relators `sᵢ ^ 2` are
among them.

The count is the point. `TauCeti.length_coxeterRelators` says that a diagram on `n` nodes has
`(n + 1).choose 2 = n * (n + 1) / 2` relators — the number of unordered pairs with repetition
allowed, not `n.choose 2` — which is exactly the relator count that published Y-diagram
presentations of sporadic groups record.

The ordered-pair set and the unordered-pair list do not agree: `(sᵢ sⱼ) ^ mᵢⱼ` and
`(sⱼ sᵢ) ^ mᵢⱼ` are distinct elements of the free group, so the list has to pick one of the two
orders — here the one increasing in the node numbering. They are conjugate, so the two sets have
the same normal closure, which is what `TauCeti.normalClosure_relatorSet_coxeterRelators` proves
and what makes the presented groups the same.

## Main definitions

* `TauCeti.coxeterRelator`: the relator expression `(sᵢ sⱼ) ^ M i j`.
* `TauCeti.coxeterRelatorsOfList` and `TauCeti.coxeterRelators`: one Coxeter relator per unordered
  pair of nodes, the diagonal included.
* `TauCeti.yParent`: the neighbour of a node towards the centre of a `Y_{p,q,r}` diagram.
* `TauCeti.YAdjacent`: adjacency in a `Y_{p,q,r}` diagram.
* `TauCeti.yCoxeterMatrix`: the Coxeter matrix of the `Y_{p,q,r}` diagram, three arms of `p`, `q`,
  and `r` nodes attached to a central node.

## Main results

* `TauCeti.length_coxeterRelators`: the relator count of a diagram on `n` nodes.
* `TauCeti.normalClosure_relatorSet_coxeterRelators`: the finite list and Mathlib's ordered-pair
  set have the same normal closure.
* `TauCeti.mulEquivCoxeterGroup` and `TauCeti.GroupPresentation.mulEquivCoxeterGroup`: a
  transcription whose relators are the Coxeter relators of `M` presents `M.Group`.
* `TauCeti.mulEquivPresentedGroupCoxeterAppend` and
  `TauCeti.GroupPresentation.mulEquivPresentedGroupCoxeterAppend`: a transcription that appends
  further relators to the Coxeter relators of `M` presents the group defined by Mathlib's Coxeter
  relations together with those extra relations. This is the shape a published Y-diagram
  presentation has, its extra relator being the spider relator.
* `TauCeti.yCoxeterMatrix_of_adjacent` and `TauCeti.yCoxeterMatrix_of_not_adjacent`: the `Y`-diagram
  entries, together with the shape lemmas `TauCeti.YAdjacent_pred` and
  `TauCeti.YAdjacent_secondArmHead_zero` pinning the arms and the centre.

## References

This file supplies the generic Coxeter-diagram half of milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which asks for the `Y₄₄₃` presentation of the Monster,
the `Y₄₃₃` presentation of the Baby Monster, and the smaller `Y`-diagrams of the Fischer groups.
The pinned diagrams themselves, their spider relators, and their published relator counts live in
`TauCeti.GroupTheory.SpecificGroups.CFSG.YDiagram`. No presentation of a named group is asserted
here.

`TauCeti.coxeterRelatorsOfList` is built from Mathlib's `List.sym2` in `Mathlib.Data.List.Sym`,
whose `List.length_sym2` supplies the relator count, and from `Sym2.inf`/`Sym2.sup` in
`Mathlib.Data.Sym.Sym2.Order`, which pick the canonical ordered representative of an unordered
pair.
-/

public section

namespace TauCeti

open Function

/-! ## The Coxeter relators of a Coxeter matrix -/

section Coxeter

variable {B : Type*}

/-- The Coxeter relator `(sᵢ sⱼ) ^ M i j`, as an auditable relator expression. On the diagonal
`M i i = 1`, so this is the involution relator `sᵢ ^ 2` written as `(sᵢ sᵢ) ^ 1`. -/
def coxeterRelator (M : CoxeterMatrix B) (i j : B) : Relator B :=
  .pow (.mul (.gen i) (.gen j)) (M i j)

@[simp]
theorem toFreeGroup_coxeterRelator (M : CoxeterMatrix B) (i j : B) :
    (coxeterRelator M i j).toFreeGroup = M.relation i j := by
  simp only [coxeterRelator, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_gen, CoxeterMatrix.relation]

/-- The Coxeter relators drawn from a list of nodes: one relator `(sᵢ sⱼ) ^ M i j` for each
unordered pair `{i, j}` of nodes of the list, the diagonal pairs `{i, i}` included, so that the
involution relators are among them. The pair is written in increasing order.

The unordered pairs are Mathlib's `List.sym2`; `Sym2.inf` and `Sym2.sup` name the smaller and the
larger node, which is the choice of order the free group forces on the transcription. -/
def coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B) (l : List B) : List (Relator B) :=
  l.sym2.map fun z => coxeterRelator M z.inf z.sup

/-- The Coxeter relator list spelled out as a map over the unordered pairs of the node list. -/
theorem coxeterRelatorsOfList_eq [LinearOrder B] (M : CoxeterMatrix B) (l : List B) :
    coxeterRelatorsOfList M l = l.sym2.map fun z => coxeterRelator M z.inf z.sup := by
  rw [coxeterRelatorsOfList]

/-- A list of `n` nodes yields `(n + 1).choose 2` Coxeter relators, the number of unordered pairs
of nodes with repetition allowed. -/
theorem length_coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B) (l : List B) :
    (coxeterRelatorsOfList M l).length = (l.length + 1).choose 2 := by
  rw [coxeterRelatorsOfList, List.length_map, List.length_sym2]

/-- Every Coxeter relator in the list is the relator of a pair of nodes. -/
theorem exists_eq_coxeterRelator_of_mem [LinearOrder B] {M : CoxeterMatrix B} {l : List B}
    {t : Relator B} (ht : t ∈ coxeterRelatorsOfList M l) : ∃ i j, t = coxeterRelator M i j := by
  rw [coxeterRelatorsOfList, List.mem_map] at ht
  obtain ⟨z, -, rfl⟩ := ht
  exact ⟨z.inf, z.sup, rfl⟩

/-- For any two nodes of the list, the list carries the Coxeter relator of the pair in one of its
two orders. Which one it is is fixed by the linear order on the nodes, and the two differ, so this
is the sharpest statement available. -/
theorem coxeterRelator_mem_or_swap_mem [LinearOrder B] (M : CoxeterMatrix B) {l : List B} {i j : B}
    (hi : i ∈ l) (hj : j ∈ l) :
    coxeterRelator M i j ∈ coxeterRelatorsOfList M l ∨
      coxeterRelator M j i ∈ coxeterRelatorsOfList M l := by
  have hmem : (fun z : Sym2 B => coxeterRelator M z.inf z.sup) s(i, j) ∈
      coxeterRelatorsOfList M l :=
    List.mem_map_of_mem (List.mk_mem_sym2 hi hj)
  rcases le_total i j with h | h
  · exact Or.inl (by simpa [inf_of_le_left h, sup_of_le_right h] using hmem)
  · exact Or.inr (by simpa [inf_of_le_right h, sup_of_le_left h] using hmem)

/-- The Coxeter relators of a matrix indexed by `Fin n`, in the order of the Bourbaki-style node
numbering `0, 1, …, n - 1`. -/
def coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) : List (Relator (Fin n)) :=
  coxeterRelatorsOfList M (List.finRange n)

/-- The Coxeter relator list of a `Fin n`-indexed matrix is the one drawn from `List.finRange n`. -/
theorem coxeterRelators_eq {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    coxeterRelators M = coxeterRelatorsOfList M (List.finRange n) := by
  rw [coxeterRelators]

/-- A Coxeter diagram on `n` nodes has `(n + 1).choose 2` relators. -/
theorem length_coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    (coxeterRelators M).length = (n + 1).choose 2 := by
  rw [coxeterRelators, length_coxeterRelatorsOfList, List.length_finRange]

/-- If `(b * a) ^ m` lies in a normal subgroup `N`, then so does `(a * b) ^ m`, the two being
conjugate by `a`. -/
private theorem pow_mul_mem_of_pow_mul_swap_mem {G : Type*} [Group G] {N : Subgroup G}
    (hN : N.Normal) (a b : G) (m : ℕ) (h : (b * a) ^ m ∈ N) : (a * b) ^ m ∈ N := by
  have key : a * (b * a) ^ m * a⁻¹ = (a * b) ^ m := by rw [← mul_pow_mul, mul_inv_cancel_right]
  exact key ▸ hN.conj_mem _ h a

/-- **The finite Coxeter relator list presents the same group as Mathlib's relation set.** The two
sets of relations differ, since only one of `(sᵢ sⱼ) ^ mᵢⱼ` and `(sⱼ sᵢ) ^ mᵢⱼ` is transcribed, but
they are conjugate and so have the same normal closure. -/
theorem normalClosure_relatorSet_coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B)
    {l : List B} (hl : ∀ i : B, i ∈ l) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelatorsOfList M l)) =
      Subgroup.normalClosure M.relationsSet := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · intro r hr
    rw [Relator.mem_relatorSet] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    obtain ⟨i, j, rfl⟩ := exists_eq_coxeterRelator_of_mem ht
    rw [toFreeGroup_coxeterRelator]
    exact Subgroup.subset_normalClosure ⟨(i, j), rfl⟩
  · rintro r ⟨⟨i, j⟩, rfl⟩
    have key : ∀ a b : B, coxeterRelator M a b ∈ coxeterRelatorsOfList M l →
        M.relation a b ∈
          Subgroup.normalClosure (Relator.relatorSet (coxeterRelatorsOfList M l)) :=
      fun a b hab => Subgroup.subset_normalClosure <|
        Relator.mem_relatorSet.mpr ⟨_, hab, toFreeGroup_coxeterRelator M a b⟩
    rw [Function.uncurry_apply_pair]
    rcases coxeterRelator_mem_or_swap_mem M (hl i) (hl j) with h | h
    · exact key i j h
    · have hji := key j i h
      simp only [CoxeterMatrix.relation] at hji ⊢
      rw [M.symmetric j i] at hji
      exact pow_mul_mem_of_pow_mul_swap_mem Subgroup.normalClosure_normal _ _ _ hji

/-- The `Fin n`-indexed form of `TauCeti.normalClosure_relatorSet_coxeterRelatorsOfList`. -/
theorem normalClosure_relatorSet_coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelators M)) =
      Subgroup.normalClosure M.relationsSet :=
  normalClosure_relatorSet_coxeterRelatorsOfList M fun _ => List.mem_finRange _

/-- Appending further relators to the Coxeter relator list imposes Mathlib's Coxeter relations
together with the extra relations. A published Y-diagram presentation has this shape, its extra
relator being the spider relator. -/
theorem normalClosure_relatorSet_coxeterRelators_append {n : ℕ} (M : CoxeterMatrix (Fin n))
    (extra : List (Relator (Fin n))) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelators M ++ extra)) =
      Subgroup.normalClosure (M.relationsSet ∪ Relator.relatorSet extra) := by
  rw [Relator.relatorSet_append, Subgroup.normalClosure_union, Subgroup.normalClosure_union,
    normalClosure_relatorSet_coxeterRelators]

/-- The group presented by the finite Coxeter relator list is Mathlib's Coxeter group. -/
def mulEquivCoxeterGroup {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    PresentedGroup (Relator.relatorSet (coxeterRelators M)) ≃* M.Group :=
  QuotientGroup.quotientMulEquivOfEq (normalClosure_relatorSet_coxeterRelators M)

@[simp]
theorem mulEquivCoxeterGroup_of {n : ℕ} (M : CoxeterMatrix (Fin n)) (i : Fin n) :
    mulEquivCoxeterGroup M (PresentedGroup.of i) = M.simple i :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

/-- **The Coxeter relator list followed by further relators presents Mathlib's Coxeter relations
together with those extra relations.** Taking `extra = []` recovers
`TauCeti.mulEquivCoxeterGroup`. -/
def mulEquivPresentedGroupCoxeterAppend {n : ℕ} (M : CoxeterMatrix (Fin n))
    (extra : List (Relator (Fin n))) :
    PresentedGroup (Relator.relatorSet (coxeterRelators M ++ extra)) ≃*
      PresentedGroup (M.relationsSet ∪ Relator.relatorSet extra) :=
  QuotientGroup.quotientMulEquivOfEq (normalClosure_relatorSet_coxeterRelators_append M extra)

@[simp]
theorem mulEquivPresentedGroupCoxeterAppend_of {n : ℕ} (M : CoxeterMatrix (Fin n))
    (extra : List (Relator (Fin n))) (i : Fin n) :
    mulEquivPresentedGroupCoxeterAppend M extra (PresentedGroup.of i) = PresentedGroup.of i :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

/-- **A transcription whose relators are exactly the Coxeter relators of `M` presents `M.Group`.**
A presentation row that adds relators to the diagram — every published Y-diagram row does, its
spider relator being the addition — is served by
`TauCeti.GroupPresentation.mulEquivPresentedGroupCoxeterAppend` instead. -/
def GroupPresentation.mulEquivCoxeterGroup (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (h : P.transcribed = coxeterRelators M) :
    P.Group ≃* M.Group :=
  QuotientGroup.quotientMulEquivOfEq (by
    rw [show P.relatorSet = Relator.relatorSet (coxeterRelators M) from congrArg _ h,
      normalClosure_relatorSet_coxeterRelators])

@[simp]
theorem GroupPresentation.mulEquivCoxeterGroup_of (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (h : P.transcribed = coxeterRelators M)
    (i : Fin P.generatorCount) :
    P.mulEquivCoxeterGroup M h (PresentedGroup.of i) = M.simple i :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

/-- **A transcription that appends further relators to the Coxeter relators of `M` presents the
Coxeter relations together with those extra relations.** This is the form an audited Y-diagram
presentation row uses: the record supplies the generator names, the source, and the count checks,
the diagram supplies the Coxeter relators, and the row's own relators — the spider relator, and for
the Monster the relator `Z` as well — are the extras. -/
def GroupPresentation.mulEquivPresentedGroupCoxeterAppend (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (extra : List (Relator (Fin P.generatorCount)))
    (h : P.transcribed = coxeterRelators M ++ extra) :
    P.Group ≃* PresentedGroup (M.relationsSet ∪ Relator.relatorSet extra) :=
  QuotientGroup.quotientMulEquivOfEq (by
    rw [show P.relatorSet = Relator.relatorSet (coxeterRelators M ++ extra) from congrArg _ h,
      normalClosure_relatorSet_coxeterRelators_append])

@[simp]
theorem GroupPresentation.mulEquivPresentedGroupCoxeterAppend_of (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (extra : List (Relator (Fin P.generatorCount)))
    (h : P.transcribed = coxeterRelators M ++ extra) (i : Fin P.generatorCount) :
    P.mulEquivPresentedGroupCoxeterAppend M extra h (PresentedGroup.of i) = PresentedGroup.of i :=
  QuotientGroup.quotientMulEquivOfEq_mk _ _

end Coxeter

/-! ## The Y-diagrams -/

/-- The neighbour of node `i` towards the centre of a `Y_{p,q,r}` diagram whose central node is
`0`, whose first arm is `1, …, p`, whose second arm is `p + 1, …, p + q`, and whose third arm is
`p + q + 1, …, p + q + r`. The first node of each arm has the centre as its neighbour, and every
later node has its predecessor. -/
def yParent (p q i : ℕ) : ℕ :=
  if i = p + 1 ∨ i = p + q + 1 then 0 else i - 1

/-- The neighbour towards the centre spelled out, so that a consumer outside this file can compute
with it. -/
theorem yParent_eq (p q i : ℕ) :
    yParent p q i = if i = p + 1 ∨ i = p + q + 1 then 0 else i - 1 := by
  rw [yParent]

/-- Adjacency in a `Y_{p,q,r}` diagram: two distinct nodes are joined exactly when one is the
neighbour of the other towards the centre. -/
def YAdjacent (p q i j : ℕ) : Prop :=
  (i ≠ 0 ∧ yParent p q i = j) ∨ (j ≠ 0 ∧ yParent p q j = i)

/-- Adjacency spelled out, so that a consumer outside this file can both establish and refute
it. -/
theorem YAdjacent_iff (p q i j : ℕ) :
    YAdjacent p q i j ↔ (i ≠ 0 ∧ yParent p q i = j) ∨ (j ≠ 0 ∧ yParent p q j = i) :=
  Iff.rfl

instance (p q i j : ℕ) : Decidable (YAdjacent p q i j) :=
  inferInstanceAs (Decidable ((i ≠ 0 ∧ yParent p q i = j) ∨ (j ≠ 0 ∧ yParent p q j = i)))

/-- Non-adjacency in terms of the arm arithmetic: neither node is a non-central node whose
neighbour towards the centre is the other. -/
theorem not_YAdjacent_iff (p q i j : ℕ) :
    ¬YAdjacent p q i j ↔
      (i = 0 ∨ yParent p q i ≠ j) ∧ (j = 0 ∨ yParent p q j ≠ i) := by
  rw [YAdjacent_iff]
  tauto

/-- Adjacency in a `Y`-diagram is symmetric. -/
theorem YAdjacent_comm {p q i j : ℕ} : YAdjacent p q i j ↔ YAdjacent p q j i :=
  or_comm

/-- Adjacent nodes of a `Y`-diagram are distinct. -/
theorem YAdjacent.ne {p q i j : ℕ} (h : YAdjacent p q i j) : i ≠ j := by
  rintro rfl
  rcases h with ⟨hi, hparent⟩ | ⟨hi, hparent⟩
  all_goals
    rw [yParent] at hparent
    split at hparent <;> omega

@[simp]
theorem yParent_one (p q : ℕ) : yParent p q 1 = 0 := by
  rw [yParent]
  split <;> omega

@[simp]
theorem yParent_secondArmHead (p q : ℕ) : yParent p q (p + 1) = 0 := by
  rw [yParent, if_pos (Or.inl rfl)]

@[simp]
theorem yParent_thirdArmHead (p q : ℕ) : yParent p q (p + q + 1) = 0 := by
  rw [yParent, if_pos (Or.inr rfl)]

/-- Away from the head of an arm, the neighbour towards the centre is the predecessor, so each arm
of the diagram is a chain in the node numbering. -/
theorem yParent_of_ne_head (p q i : ℕ) (h₂ : i ≠ p + 1) (h₃ : i ≠ p + q + 1) :
    yParent p q i = i - 1 := by
  rw [yParent, if_neg (by tauto)]

/-- The head of the first arm is joined to the centre. When the first arm is empty, node `1` heads
the first nonempty arm instead, and is joined to the centre as well. -/
theorem YAdjacent_one_zero (p q : ℕ) : YAdjacent p q 1 0 :=
  Or.inl ⟨one_ne_zero, yParent_one p q⟩

/-- The head of the second arm is joined to the centre. -/
theorem YAdjacent_secondArmHead_zero (p q : ℕ) : YAdjacent p q (p + 1) 0 :=
  Or.inl ⟨by omega, yParent_secondArmHead p q⟩

/-- The head of the third arm is joined to the centre. -/
theorem YAdjacent_thirdArmHead_zero (p q : ℕ) : YAdjacent p q (p + q + 1) 0 :=
  Or.inl ⟨by omega, yParent_thirdArmHead p q⟩

/-- Consecutive nodes of one arm are joined. -/
theorem YAdjacent_pred (p q i : ℕ) (h₁ : i ≠ 0) (h₂ : i ≠ p + 1) (h₃ : i ≠ p + q + 1) :
    YAdjacent p q i (i - 1) :=
  Or.inl ⟨h₁, yParent_of_ne_head p q i h₂ h₃⟩

/-- The Coxeter matrix of the `Y_{p,q,r}` diagram: `p + q + r + 1` nodes, all generators
involutions, a braid relation of order three along each of the three arms, and commuting
generators otherwise. -/
def yCoxeterMatrix (p q r : ℕ) : CoxeterMatrix (Fin (p + q + r + 1)) where
  M := Matrix.of fun i j => if i = j then 1 else if YAdjacent p q i j then 3 else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rcases eq_or_ne i j with rfl | h
    · rfl
    · rw [if_neg (Ne.symm h), if_neg h]
      exact if_congr YAdjacent_comm rfl rfl
  diagonal i := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, if_neg h]
    split <;> decide

/-- The matrix entry is `1` on the diagonal, `3` for adjacent nodes, and `2` otherwise. -/
theorem yCoxeterMatrix_apply (p q r : ℕ) (i j : Fin (p + q + r + 1)) :
    yCoxeterMatrix p q r i j =
      if i = j then 1 else if YAdjacent p q i j then 3 else 2 := by
  rw [yCoxeterMatrix]
  rfl

/-- Every `Y`-diagram is simply laced: an entry of its Coxeter matrix is `1`, `2`, or `3`, so the
diagram carries only single edges. -/
theorem yCoxeterMatrix_le_three (p q r : ℕ) (i j : Fin (p + q + r + 1)) :
    yCoxeterMatrix p q r i j ≤ 3 := by
  rw [yCoxeterMatrix_apply]
  split
  · omega
  · split <;> omega

/-- Adjacent nodes of a `Y`-diagram carry a braid relation of order three. -/
theorem yCoxeterMatrix_of_adjacent (p q r : ℕ) {i j : Fin (p + q + r + 1)}
    (h : YAdjacent p q i j) : yCoxeterMatrix p q r i j = 3 := by
  have hij : i ≠ j := fun hij => h.ne (congrArg Fin.val hij)
  rw [yCoxeterMatrix_apply, if_neg hij, if_pos h]

/-- Non-adjacent distinct nodes of a `Y`-diagram carry commuting generators. -/
theorem yCoxeterMatrix_of_not_adjacent (p q r : ℕ) {i j : Fin (p + q + r + 1)} (hne : i ≠ j)
    (h : ¬YAdjacent p q i j) : yCoxeterMatrix p q r i j = 2 := by
  rw [yCoxeterMatrix_apply, if_neg hne, if_neg h]

end TauCeti
