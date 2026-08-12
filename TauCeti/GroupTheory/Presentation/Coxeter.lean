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

/-!
# Auditable Coxeter relator lists

A Coxeter presentation is normally published as a diagram: a set of involutions, one per node, with
a braid relation on each edge and a commuting relation on each non-edge. Mathlib turns a
`CoxeterMatrix` into a group through `CoxeterMatrix.relationsSet`, the *range* of
`CoxeterMatrix.relation`, which is a set indexed by ordered pairs rather than an explicit list whose
entries and length a reviewer can audit. This file produces that finite relator list, one relator
per unordered pair of nodes, the diagonal included, so that the `n` involution relators `sᵢ ^ 2` are
among them.

The count is the point. `TauCeti.length_coxeterRelators` says that a diagram on `n` nodes has
`(n + 1).choose 2 = n * (n + 1) / 2` relators — the number of unordered pairs with repetition
allowed, not `n.choose 2`.

The ordered-pair set and the unordered-pair list need not agree: for distinct nodes,
`(sᵢ sⱼ) ^ mᵢⱼ` and `(sⱼ sᵢ) ^ mᵢⱼ` can be distinct elements of the free group, so the list has to
pick one of the two orders — here the one increasing in the node numbering. They are conjugate, so
the two sets have the same normal closure, which is what
`TauCeti.normalClosure_relatorSet_coxeterRelators` proves and what makes the presented groups the
same.

A published diagram is usually simply laced: every edge carries the label three and every non-edge
the label two. `TauCeti.coxeterMatrixOfEdges` builds the `CoxeterMatrix` of such a diagram from the
list of its edges, so that a transcribed row records the edges the source draws rather than a
hand-built matrix.

## Main definitions

* `TauCeti.coxeterMatrixOfEdges`: the Coxeter matrix of a simply laced diagram, from its edges.
* `TauCeti.coxeterRelator`: the relator expression `(sᵢ sⱼ) ^ M i j`.
* `TauCeti.coxeterRelatorsOfList` and `TauCeti.coxeterRelators`: one Coxeter relator per unordered
  pair of nodes, the diagonal included.

## Main results

* `TauCeti.length_coxeterRelators`: the relator count of a diagram on `n` nodes.
* `TauCeti.normalClosure_relatorSet_coxeterRelators`: the finite list and Mathlib's ordered-pair
  set have the same normal closure.
* `TauCeti.mulEquivCoxeterGroup` and `TauCeti.GroupPresentation.mulEquivCoxeterGroup`: a
  transcription whose relators are the Coxeter relators of `M` presents `M.Group`.
* `TauCeti.mulEquivPresentedGroupCoxeterAppend` and
  `TauCeti.GroupPresentation.mulEquivPresentedGroupCoxeterAppend`: a transcription that appends
  further relators to the Coxeter relators of `M` presents the group defined by Mathlib's Coxeter
  relations together with those extra relations.

## References

This file supplies reusable Coxeter-presentation machinery needed by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. No presentation of a named group is asserted here.

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

/-- The Coxeter matrix of the simply laced diagram with the given edges: a node with itself has
entry one, a pair of distinct nodes joined by an edge has entry three, and every other pair of
distinct nodes has entry two.

The edge list is read symmetrically, so each edge may be oriented either way, and repeated edges are
harmless. The body is exposed so that the checks a transcribed diagram runs on its own matrix
reduce. -/
@[expose]
def coxeterMatrixOfEdges [DecidableEq B] (edges : List (B × B)) : CoxeterMatrix B where
  M := Matrix.of fun i j =>
    if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2
  isSymm := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rcases eq_or_ne i j with rfl | h
    · rfl
    · simp only [h, Ne.symm h, ↓reduceIte]
      exact if_congr or_comm rfl rfl
  diagonal i := by simp
  off_diagonal i j h := by
    simp only [Matrix.of_apply, h, ↓reduceIte]
    split <;> omega

/-- Evaluation of the Coxeter matrix of a simply laced diagram directly from its edge list. -/
@[simp]
theorem coxeterMatrixOfEdges_apply [DecidableEq B] (edges : List (B × B)) (i j : B) :
    coxeterMatrixOfEdges edges i j =
      if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2 := by
  simp only [coxeterMatrixOfEdges, Matrix.of_apply]

/-- The Coxeter relator `(sᵢ sⱼ) ^ M i j`, as an auditable relator expression. On the diagonal
`M i i = 1`, so this is the involution relator `sᵢ ^ 2` written as `(sᵢ sᵢ) ^ 1`. -/
def coxeterRelator (M : CoxeterMatrix B) (i j : B) : Relator B :=
  .pow (.mul (.gen i) (.gen j)) (M i j)

/-- The compiled signed word of a Coxeter relator. -/
@[simp]
theorem toWord_coxeterRelator (M : CoxeterMatrix B) (i j : B) :
    (coxeterRelator M i j).toWord =
      (List.replicate (M i j) [(i, true), (j, true)]).flatten := by
  simp [coxeterRelator]

/-- A Coxeter relator contains twice as many signed letters as its matrix entry. -/
theorem length_toWord_coxeterRelator (M : CoxeterMatrix B) (i j : B) :
    (coxeterRelator M i j).toWord.length = 2 * M i j := by
  rw [toWord_coxeterRelator, List.length_flatten]
  simp [Nat.mul_comm]

/-- The signed word of a Coxeter relator is cyclically reduced. -/
theorem isCyclicallyReduced_toWord_coxeterRelator (M : CoxeterMatrix B) (i j : B) :
    FreeGroup.IsCyclicallyReduced (coxeterRelator M i j).toWord := by
  rw [toWord_coxeterRelator]
  apply FreeGroup.IsCyclicallyReduced.flatten_replicate
  simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- Interpreting a Coxeter relator in the free group yields Mathlib's Coxeter relation. -/
@[simp]
theorem toFreeGroup_coxeterRelator (M : CoxeterMatrix B) (i j : B) :
    (coxeterRelator M i j).toFreeGroup = M.relation i j := by
  simp only [coxeterRelator, Relator.toFreeGroup_pow, Relator.toFreeGroup_mul,
    Relator.toFreeGroup_gen, CoxeterMatrix.relation]

/-- The Coxeter relators drawn from a list of nodes: one relator `(sᵢ sⱼ) ^ M i j` for each
unordered pair of list entries, including pairs that use the same entry, so that the involution
relators are among them. Duplicate entries can produce repeated relators. The pair is written in
increasing order.

The unordered pairs are Mathlib's `List.sym2`; `Sym2.inf` and `Sym2.sup` name the smaller and the
larger node, which is the choice of order the free group forces on the transcription. -/
def coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B) (l : List B) : List (Relator B) :=
  l.sym2.map fun z => coxeterRelator M z.inf z.sup

/-- The Coxeter relator list is obtained by mapping the canonically ordered representative of
each unordered pair of list positions to its Coxeter relator.

This is the unfolding lemma for the sealed body, and like `TauCeti.GroupPresentation.relators_def`
it is deliberately not `@[simp]`: it lets a concrete finite presentation audit the compiled words
without the definition being exposed. -/
theorem coxeterRelatorsOfList_def [LinearOrder B] (M : CoxeterMatrix B) (l : List B) :
    coxeterRelatorsOfList M l = l.sym2.map fun z => coxeterRelator M z.inf z.sup := by
  rw [coxeterRelatorsOfList]

/-- A list of length `n` yields `(n + 1).choose 2` Coxeter relators, the number of unordered pairs
of list positions with repetition allowed. -/
@[simp]
theorem length_coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B) (l : List B) :
    (coxeterRelatorsOfList M l).length = (l.length + 1).choose 2 := by
  rw [coxeterRelatorsOfList, List.length_map, List.length_sym2]

/-- Membership in the Coxeter relator list, in terms of two nodes of the source list and their
canonical increasing order. -/
@[simp]
theorem mem_coxeterRelatorsOfList_iff [LinearOrder B] {M : CoxeterMatrix B} {l : List B}
    {t : Relator B} :
    t ∈ coxeterRelatorsOfList M l ↔
      ∃ i ∈ l, ∃ j ∈ l, t = coxeterRelator M s(i, j).inf s(i, j).sup := by
  rw [coxeterRelatorsOfList, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    induction z with
    | _ i j =>
      exact ⟨i, List.left_mem_of_mk_mem_sym2 hz, j, List.right_mem_of_mk_mem_sym2 hz, rfl⟩
  · rintro ⟨i, hi, j, hj, rfl⟩
    exact ⟨s(i, j), List.mk_mem_sym2 hi hj, rfl⟩

/-- For any two nodes of the list, the list carries the Coxeter relator of the pair in one of its
two orders. Which one it is is fixed by the linear order on the nodes, and the two may differ, so
this is the sharpest statement available. -/
private theorem coxeterRelator_mem_or_swap_mem [LinearOrder B] (M : CoxeterMatrix B)
    {l : List B} {i j : B}
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

/-- The numbered Coxeter relator list uses the nodes `0, …, n - 1` in that order. This is the
unfolding lemma for the sealed body, and like `coxeterRelatorsOfList_def` it is not `@[simp]`. -/
theorem coxeterRelators_def {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    coxeterRelators M = coxeterRelatorsOfList M (List.finRange n) := by
  rw [coxeterRelators]

/-- Membership in the Coxeter relator list of a `Fin n`-indexed matrix: every pair of nodes
contributes, so the only condition is that the relator be the one of a pair, written in the
canonical increasing order. -/
@[simp]
theorem mem_coxeterRelators_iff {n : ℕ} {M : CoxeterMatrix (Fin n)} {t : Relator (Fin n)} :
    t ∈ coxeterRelators M ↔ ∃ i j : Fin n, t = coxeterRelator M s(i, j).inf s(i, j).sup := by
  rw [coxeterRelators, mem_coxeterRelatorsOfList_iff]
  exact ⟨fun ⟨i, _, j, _, h⟩ => ⟨i, j, h⟩,
    fun ⟨i, j, h⟩ => ⟨i, List.mem_finRange i, j, List.mem_finRange j, h⟩⟩

/-- A Coxeter diagram on `n` nodes has `(n + 1).choose 2` relators. -/
@[simp]
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
sets of relations need not coincide: for distinct nodes, only one of `(sᵢ sⱼ) ^ mᵢⱼ` and
`(sⱼ sᵢ) ^ mᵢⱼ` is transcribed. They are conjugate and so have the same normal closure. -/
theorem normalClosure_relatorSet_coxeterRelatorsOfList [LinearOrder B] (M : CoxeterMatrix B)
    {l : List B} (hl : ∀ i : B, i ∈ l) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelatorsOfList M l)) =
      Subgroup.normalClosure M.relationsSet := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · intro r hr
    rw [Relator.mem_relatorSet] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    obtain ⟨i, -, j, -, rfl⟩ := mem_coxeterRelatorsOfList_iff.mp ht
    rw [toFreeGroup_coxeterRelator]
    exact Subgroup.subset_normalClosure ⟨(s(i, j).inf, s(i, j).sup), rfl⟩
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

/-- Appending further relators to the Coxeter relator list imposes Mathlib's Coxeter relations
together with the extra relations. A published Y-diagram presentation has this shape, its extra
relator being the spider relator. -/
theorem normalClosure_relatorSet_coxeterRelatorsOfList_append [LinearOrder B] (M : CoxeterMatrix B)
    {l : List B} (hl : ∀ i : B, i ∈ l) (extra : List (Relator B)) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelatorsOfList M l ++ extra)) =
      Subgroup.normalClosure (M.relationsSet ∪ Relator.relatorSet extra) := by
  rw [Relator.relatorSet_append, Subgroup.normalClosure_union, Subgroup.normalClosure_union,
    normalClosure_relatorSet_coxeterRelatorsOfList M hl]

/-- The `Fin n`-indexed form of `TauCeti.normalClosure_relatorSet_coxeterRelatorsOfList`. -/
theorem normalClosure_relatorSet_coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelators M)) =
      Subgroup.normalClosure M.relationsSet :=
  normalClosure_relatorSet_coxeterRelatorsOfList M fun _ => List.mem_finRange _

/-- The `Fin n`-indexed form of
`TauCeti.normalClosure_relatorSet_coxeterRelatorsOfList_append`. -/
theorem normalClosure_relatorSet_coxeterRelators_append {n : ℕ} (M : CoxeterMatrix (Fin n))
    (extra : List (Relator (Fin n))) :
    Subgroup.normalClosure (Relator.relatorSet (coxeterRelators M ++ extra)) =
      Subgroup.normalClosure (M.relationsSet ∪ Relator.relatorSet extra) :=
  normalClosure_relatorSet_coxeterRelatorsOfList_append M (fun _ => List.mem_finRange _) extra

/-- The group presented by the finite Coxeter relator list is Mathlib's Coxeter group. -/
def mulEquivCoxeterGroup {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    PresentedGroup (Relator.relatorSet (coxeterRelators M)) ≃* M.Group :=
  QuotientGroup.quotientMulEquivOfEq (normalClosure_relatorSet_coxeterRelators M)

@[simp]
theorem mulEquivCoxeterGroup_apply_of {n : ℕ} (M : CoxeterMatrix (Fin n)) (i : Fin n) :
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
theorem mulEquivPresentedGroupCoxeterAppend_apply_of {n : ℕ} (M : CoxeterMatrix (Fin n))
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
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [P.relatorSet_eq_relatorSet_transcribed, h])).trans
      (_root_.TauCeti.mulEquivCoxeterGroup M)

@[simp]
theorem GroupPresentation.mulEquivCoxeterGroup_apply_of (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (h : P.transcribed = coxeterRelators M)
    (i : Fin P.generatorCount) :
    P.mulEquivCoxeterGroup M h (PresentedGroup.of i) = M.simple i :=
  by
    rw [GroupPresentation.mulEquivCoxeterGroup]
    calc
      _ = _root_.TauCeti.mulEquivCoxeterGroup M
          (QuotientGroup.quotientMulEquivOfEq _ (PresentedGroup.of i)) :=
        MulEquiv.trans_apply _ _ _
      _ = _root_.TauCeti.mulEquivCoxeterGroup M (PresentedGroup.of i) :=
        congrArg (_root_.TauCeti.mulEquivCoxeterGroup M)
          (QuotientGroup.quotientMulEquivOfEq_mk _ (FreeGroup.of i))
      _ = _ := _root_.TauCeti.mulEquivCoxeterGroup_apply_of M i

/-- **A transcription that appends further relators to the Coxeter relators of `M` presents the
Coxeter relations together with those extra relations.** This is the form an audited Y-diagram
presentation row uses: the record supplies the generator names, the source, and the count checks,
the diagram supplies the Coxeter relators, and the row's own relators — the spider relator, and for
the Monster the relator `Z` as well — are the extras. -/
def GroupPresentation.mulEquivPresentedGroupCoxeterAppend (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (extra : List (Relator (Fin P.generatorCount)))
    (h : P.transcribed = coxeterRelators M ++ extra) :
    P.Group ≃* PresentedGroup (M.relationsSet ∪ Relator.relatorSet extra) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [P.relatorSet_eq_relatorSet_transcribed, h])).trans
      (_root_.TauCeti.mulEquivPresentedGroupCoxeterAppend M extra)

@[simp]
theorem GroupPresentation.mulEquivPresentedGroupCoxeterAppend_apply_of (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (extra : List (Relator (Fin P.generatorCount)))
    (h : P.transcribed = coxeterRelators M ++ extra) (i : Fin P.generatorCount) :
    P.mulEquivPresentedGroupCoxeterAppend M extra h (PresentedGroup.of i) = PresentedGroup.of i :=
  by
    rw [GroupPresentation.mulEquivPresentedGroupCoxeterAppend]
    calc
      _ = _root_.TauCeti.mulEquivPresentedGroupCoxeterAppend M extra
          (QuotientGroup.quotientMulEquivOfEq _ (PresentedGroup.of i)) :=
        MulEquiv.trans_apply _ _ _
      _ = _root_.TauCeti.mulEquivPresentedGroupCoxeterAppend M extra
          (PresentedGroup.of i) :=
        congrArg (_root_.TauCeti.mulEquivPresentedGroupCoxeterAppend M extra)
          (QuotientGroup.quotientMulEquivOfEq_mk _ (FreeGroup.of i))
      _ = _ := _root_.TauCeti.mulEquivPresentedGroupCoxeterAppend_apply_of M extra i

end Coxeter

end TauCeti
