/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Auditable Coxeter relator lists and the Y-diagrams

A Coxeter presentation is normally published as a diagram: a set of involutions, one per node, with
a braid relation on each edge and a commuting relation on each non-edge. Mathlib turns a
`CoxeterMatrix` into a group through `CoxeterMatrix.relationsSet`, the *range* of
`CoxeterMatrix.relation`, which is a set indexed by ordered pairs and is therefore neither a finite
list nor countable by a reviewer. This file produces the finite relator list a transcription review
needs, one relator per unordered pair of nodes, and identifies the group it presents with Mathlib's
Coxeter group.

The count is the point. `TauCeti.length_coxeterRelators` says that a diagram on `n` nodes has
`(n + 1).choose 2 = n * (n + 1) / 2` relators, which is exactly the relator count that published
Y-diagram presentations of sporadic groups record: `79 = 78 + 1` for `Y₄₄₃` and `92 = 91 + 1` for
`Y₄₄₄`, the extra relator in each case being the spider relator.

The ordered-pair set and the unordered-pair list do not agree: `(sᵢ sⱼ) ^ mᵢⱼ` and
`(sⱼ sᵢ) ^ mᵢⱼ` are distinct elements of the free group. They are conjugate, so the two sets have
the same normal closure, which is what `TauCeti.normalClosure_relationSet_coxeterRelators` proves
and what makes the presented groups the same. That is also why the relator list cannot be obtained
by mapping over Mathlib's `List.sym2`: the relator is not a function of the unordered pair.

## Main definitions

* `TauCeti.Relator.relationSet`: the relations denoted by a list of relator expressions.
* `TauCeti.coxeterRelator`: the relator expression `(sᵢ sⱼ) ^ M i j`.
* `TauCeti.coxeterRelatorsOfList` and `TauCeti.coxeterRelators`: one Coxeter relator per unordered
  pair of nodes.
* `TauCeti.yCoxeterMatrix`: the Coxeter matrix of the `Y_{p,q,r}` diagram, three arms of `p`, `q`,
  and `r` nodes attached to a central node.
* `TauCeti.ySpiderRelator`: the spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y`-diagram.

## Main results

* `TauCeti.length_coxeterRelators`: the relator count of a diagram on `n` nodes.
* `TauCeti.normalClosure_relationSet_coxeterRelators`: the finite list and Mathlib's ordered-pair
  set have the same normal closure.
* `TauCeti.PresentedGroup.mulEquivOfNormalClosureEq` and
  `TauCeti.GroupPresentation.mulEquivCoxeterGroup`: a transcription whose relators are the Coxeter
  relators of `M` presents `M.Group`.
* `TauCeti.yCoxeterMatrix_of_adjacent` and `TauCeti.yCoxeterMatrix_of_not_adjacent`: the `Y`-diagram
  entries, together with the shape lemmas `TauCeti.YAdjacent_pred` and
  `TauCeti.YAdjacent_secondArmHead_zero` pinning the arms and the centre.

## References

This file supplies the Coxeter-diagram half of milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which asks for the `Y₄₄₃` presentation of the Monster
("the 12 nodes of that diagram, the Coxeter relations, the spider relation, and `Z = 1`"), the
`Y₄₃₃` presentation of the Baby Monster, and the smaller `Y`-diagrams of the Fischer groups. The
node numbering, the arm labels `a, bᵢ, cᵢ, dᵢ, eᵢ`, the spider word, and the relator counts `79`
and `92` follow J. N. Bray's
[presentation pages](https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html); the theorems
that these diagrams present the groups in question are Norton's (1990) and Ivanov's (1999) and are
not formalized here. No presentation of a named group is asserted in this file.
-/

@[expose] public section

namespace TauCeti

open Function

/-! ## Relations denoted by a list of relator expressions -/

namespace Relator

variable {α : Type*}

/-- The relations denoted by a list of relator expressions, as a set of free-group elements.

This is the list-level counterpart of `TauCeti.GroupPresentation.relatorSet`, stated against
`TauCeti.Relator.toFreeGroup` so that no consumer has to unfold the word compiler. -/
def relationSet (l : List (Relator α)) : Set (FreeGroup α) :=
  {r | ∃ t ∈ l, t.toFreeGroup = r}

@[simp]
theorem mem_relationSet {l : List (Relator α)} {r : FreeGroup α} :
    r ∈ relationSet l ↔ ∃ t ∈ l, t.toFreeGroup = r :=
  Iff.rfl

/-- Appending relator lists unions their relation sets. -/
theorem relationSet_append (l l' : List (Relator α)) :
    relationSet (l ++ l') = relationSet l ∪ relationSet l' := by
  ext r
  simp only [mem_relationSet, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨t, ht | ht, rfl⟩
    exacts [Or.inl ⟨t, ht, rfl⟩, Or.inr ⟨t, ht, rfl⟩]
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    exacts [⟨t, Or.inl ht, rfl⟩, ⟨t, Or.inr ht, rfl⟩]

/-- The relator expression spelling out a nonempty word of generators, with no inverses. -/
def ofGenerators : α → List α → Relator α
  | x, [] => .gen x
  | x, y :: l => .mul (.gen x) (ofGenerators y l)

/-- Compiling a spelled-out generator word returns exactly its letters, each with positive sign. -/
@[simp]
theorem toWord_ofGenerators (x : α) (l : List α) :
    (ofGenerators x l).toWord = (x, true) :: l.map (fun y => (y, true)) := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => simp [ofGenerators, toWord, ih]

end Relator

/-- The relations of a presentation record are the relations denoted by its transcribed
expressions. -/
theorem GroupPresentation.relatorSet_eq_relationSet (P : GroupPresentation) :
    P.relatorSet = Relator.relationSet P.transcribed := by
  ext r
  simp

/-! ## Presented groups only see the normal closure of their relations -/

namespace PresentedGroup

/-- Two sets of relations with the same normal closure present the same group.

Mathlib's `PresentedGroup.equivPresentedGroup` reindexes the generators; this instead compares two
relation sets over the same generators, which is what happens when a published finite relator list
is compared with an equivalent infinite family of relations. -/
def mulEquivOfNormalClosureEq {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) :
    PresentedGroup S ≃* PresentedGroup T :=
  QuotientGroup.quotientMulEquivOfEq h

@[simp]
theorem mulEquivOfNormalClosureEq_of {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (x : α) :
    mulEquivOfNormalClosureEq h (PresentedGroup.of x) = PresentedGroup.of x :=
  rfl

end PresentedGroup

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
  simp only [coxeterRelator, Relator.toFreeGroup, CoxeterMatrix.relation]

/-- On the diagonal the Coxeter relator denotes the involution relation `sᵢ ^ 2`. -/
theorem toFreeGroup_coxeterRelator_self (M : CoxeterMatrix B) (i : B) :
    (coxeterRelator M i i).toFreeGroup = FreeGroup.of i ^ 2 := by
  rw [toFreeGroup_coxeterRelator]
  simp only [CoxeterMatrix.relation, M.diagonal, pow_one, ← sq]

/-- The Coxeter relators drawn from a list of nodes: for each node `i` of the list, one relator
`(sᵢ sⱼ) ^ M i j` for `j` running over `i` itself and the nodes after it. On a duplicate-free list
this is one relator per unordered pair of nodes. -/
def coxeterRelatorsOfList (M : CoxeterMatrix B) : List B → List (Relator B)
  | [] => []
  | i :: l => ((i :: l).map fun j => coxeterRelator M i j) ++ coxeterRelatorsOfList M l

@[simp]
theorem coxeterRelatorsOfList_nil (M : CoxeterMatrix B) :
    coxeterRelatorsOfList M [] = [] :=
  rfl

theorem coxeterRelatorsOfList_cons (M : CoxeterMatrix B) (i : B) (l : List B) :
    coxeterRelatorsOfList M (i :: l) =
      ((i :: l).map fun j => coxeterRelator M i j) ++ coxeterRelatorsOfList M l :=
  rfl

/-- A list of `n` nodes yields `(n + 1).choose 2` Coxeter relators, the number of unordered pairs
of nodes with repetition allowed. -/
theorem length_coxeterRelatorsOfList (M : CoxeterMatrix B) (l : List B) :
    (coxeterRelatorsOfList M l).length = (l.length + 1).choose 2 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [coxeterRelatorsOfList_cons, List.length_append, List.length_map, List.length_cons,
      Nat.choose_succ_succ, ← ih, Nat.choose_one_right]

/-- Every Coxeter relator in the list is the relator of a pair of nodes of the list. -/
theorem exists_eq_coxeterRelator_of_mem {M : CoxeterMatrix B} {l : List B} {t : Relator B}
    (ht : t ∈ coxeterRelatorsOfList M l) : ∃ i j, t = coxeterRelator M i j := by
  induction l with
  | nil => simp at ht
  | cons i l ih =>
    rw [coxeterRelatorsOfList_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · obtain ⟨j, -, rfl⟩ := List.mem_map.mp ht
      exact ⟨i, j, rfl⟩
    · exact ih ht

/-- For any two nodes of the list, the list carries the Coxeter relator of the pair in one of its
two orders. Which one it is depends on the order of the list, and the two differ, so this is the
sharpest statement available. -/
theorem coxeterRelator_mem_or_swap_mem (M : CoxeterMatrix B) {l : List B} {i j : B}
    (hi : i ∈ l) (hj : j ∈ l) :
    coxeterRelator M i j ∈ coxeterRelatorsOfList M l ∨
      coxeterRelator M j i ∈ coxeterRelatorsOfList M l := by
  induction l with
  | nil => simp at hi
  | cons c l ih =>
    rcases List.mem_cons.mp hi with rfl | hi'
    · exact Or.inl (List.mem_append_left _ (List.mem_map_of_mem hj))
    · rcases List.mem_cons.mp hj with rfl | hj'
      · exact Or.inr (List.mem_append_left _ (List.mem_map_of_mem hi))
      · exact (ih hi' hj').imp (List.mem_append_right _) (List.mem_append_right _)

/-- The Coxeter relators of a matrix indexed by `Fin n`, in the order of the Bourbaki-style node
numbering `0, 1, …, n - 1`. -/
def coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) : List (Relator (Fin n)) :=
  coxeterRelatorsOfList M (List.finRange n)

/-- A Coxeter diagram on `n` nodes has `(n + 1).choose 2` relators. -/
theorem length_coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    (coxeterRelators M).length = (n + 1).choose 2 := by
  rw [coxeterRelators, length_coxeterRelatorsOfList, List.length_finRange]

/-- The relator count of a Coxeter diagram on `n` nodes in closed form. -/
theorem length_coxeterRelators_eq_div {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    (coxeterRelators M).length = (n + 1) * n / 2 := by
  rw [length_coxeterRelators, Nat.choose_two_right, Nat.add_sub_cancel]

/-- Conjugating a group element past a normal subgroup swaps the two factors of a power of a
product. -/
private theorem pow_mul_mem_of_pow_mul_mem {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (a b : G) (m : ℕ) (h : (b * a) ^ m ∈ N) : (a * b) ^ m ∈ N := by
  have hsc : SemiconjBy a (b * a) (a * b) := by
    simp only [SemiconjBy, mul_assoc]
  have key : a * (b * a) ^ m * a⁻¹ = (a * b) ^ m := by
    rw [show a * (b * a) ^ m = (a * b) ^ m * a from hsc.pow_right m, mul_inv_cancel_right]
  exact key ▸ hN.conj_mem _ h a

/-- **The finite Coxeter relator list presents the same group as Mathlib's relation set.** The two
sets of relations differ, since only one of `(sᵢ sⱼ) ^ mᵢⱼ` and `(sⱼ sᵢ) ^ mᵢⱼ` is transcribed, but
they are conjugate and so have the same normal closure. -/
theorem normalClosure_relationSet_coxeterRelatorsOfList (M : CoxeterMatrix B) {l : List B}
    (hl : ∀ i : B, i ∈ l) :
    Subgroup.normalClosure (Relator.relationSet (coxeterRelatorsOfList M l)) =
      Subgroup.normalClosure M.relationsSet := by
  refine le_antisymm (Subgroup.normalClosure_le_normal ?_) (Subgroup.normalClosure_le_normal ?_)
  · rintro r ⟨t, ht, rfl⟩
    obtain ⟨i, j, rfl⟩ := exists_eq_coxeterRelator_of_mem ht
    rw [toFreeGroup_coxeterRelator]
    exact Subgroup.subset_normalClosure ⟨(i, j), rfl⟩
  · rintro r ⟨⟨i, j⟩, rfl⟩
    have key : ∀ a b : B, coxeterRelator M a b ∈ coxeterRelatorsOfList M l →
        M.relation a b ∈
          Subgroup.normalClosure (Relator.relationSet (coxeterRelatorsOfList M l)) :=
      fun a b hab => Subgroup.subset_normalClosure ⟨_, hab, toFreeGroup_coxeterRelator M a b⟩
    change M.relation i j ∈ _
    rcases coxeterRelator_mem_or_swap_mem M (hl i) (hl j) with h | h
    · exact key i j h
    · have hji := key j i h
      simp only [CoxeterMatrix.relation] at hji ⊢
      rw [M.symmetric j i] at hji
      exact pow_mul_mem_of_pow_mul_mem Subgroup.normalClosure_normal _ _ _ hji

/-- The `Fin n`-indexed form of `TauCeti.normalClosure_relationSet_coxeterRelatorsOfList`. -/
theorem normalClosure_relationSet_coxeterRelators {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    Subgroup.normalClosure (Relator.relationSet (coxeterRelators M)) =
      Subgroup.normalClosure M.relationsSet :=
  normalClosure_relationSet_coxeterRelatorsOfList M fun _ => List.mem_finRange _

/-- The group presented by the finite Coxeter relator list is Mathlib's Coxeter group. -/
def mulEquivCoxeterGroup {n : ℕ} (M : CoxeterMatrix (Fin n)) :
    PresentedGroup (Relator.relationSet (coxeterRelators M)) ≃* M.Group :=
  PresentedGroup.mulEquivOfNormalClosureEq (normalClosure_relationSet_coxeterRelators M)

@[simp]
theorem mulEquivCoxeterGroup_of {n : ℕ} (M : CoxeterMatrix (Fin n)) (i : Fin n) :
    mulEquivCoxeterGroup M (PresentedGroup.of i) = M.simple i :=
  rfl

/-- **A transcription whose relators are the Coxeter relators of `M` presents `M.Group`.** This is
the form an audited presentation row uses: the record supplies the generator names, the source, and
the count checks, and this identifies the group it defines. -/
def GroupPresentation.mulEquivCoxeterGroup (P : GroupPresentation)
    (M : CoxeterMatrix (Fin P.generatorCount)) (h : P.transcribed = coxeterRelators M) :
    P.Group ≃* M.Group :=
  PresentedGroup.mulEquivOfNormalClosureEq (by
    rw [P.relatorSet_eq_relationSet, h, normalClosure_relationSet_coxeterRelators])

end Coxeter

/-! ## The Y-diagrams -/

/-- The neighbour of node `i` towards the centre of a `Y_{p,q,r}` diagram whose central node is
`0`, whose first arm is `1, …, p`, whose second arm is `p + 1, …, p + q`, and whose third arm is
`p + q + 1, …, p + q + r`. The first node of each arm has the centre as its neighbour, and every
later node has its predecessor. -/
def yParent (p q i : ℕ) : ℕ :=
  if i = p + 1 ∨ i = p + q + 1 then 0 else i - 1

/-- Adjacency in a `Y_{p,q,r}` diagram: two distinct nodes are joined exactly when one is the
neighbour of the other towards the centre. -/
def YAdjacent (p q i j : ℕ) : Prop :=
  (i ≠ 0 ∧ yParent p q i = j) ∨ (j ≠ 0 ∧ yParent p q j = i)

instance (p q i j : ℕ) : Decidable (YAdjacent p q i j) :=
  inferInstanceAs (Decidable ((i ≠ 0 ∧ yParent p q i = j) ∨ (j ≠ 0 ∧ yParent p q j = i)))

/-- Adjacency in a `Y`-diagram is symmetric. -/
theorem YAdjacent_comm {p q i j : ℕ} : YAdjacent p q i j ↔ YAdjacent p q j i :=
  or_comm

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

/-- The head of the first arm is joined to the centre. When `p = 0` the first arm is empty and node
`1` heads the second arm instead, which is joined to the centre as well. -/
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

theorem yCoxeterMatrix_apply (p q r : ℕ) (i j : Fin (p + q + r + 1)) :
    yCoxeterMatrix p q r i j =
      if i = j then 1 else if YAdjacent p q i j then 3 else 2 :=
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
theorem yCoxeterMatrix_of_adjacent (p q r : ℕ) {i j : Fin (p + q + r + 1)} (hne : i ≠ j)
    (h : YAdjacent p q i j) : yCoxeterMatrix p q r i j = 3 := by
  rw [yCoxeterMatrix_apply, if_neg hne, if_pos h]

/-- Non-adjacent distinct nodes of a `Y`-diagram carry commuting generators. -/
theorem yCoxeterMatrix_of_not_adjacent (p q r : ℕ) {i j : Fin (p + q + r + 1)} (hne : i ≠ j)
    (h : ¬YAdjacent p q i j) : yCoxeterMatrix p q r i j = 2 := by
  rw [yCoxeterMatrix_apply, if_neg hne, if_neg h]

/-- A `Y_{p,q,r}` diagram carries `(p + q + r + 2).choose 2` Coxeter relators. -/
theorem length_coxeterRelators_yCoxeterMatrix (p q r : ℕ) :
    (coxeterRelators (yCoxeterMatrix p q r)).length = (p + q + r + 2).choose 2 :=
  length_coxeterRelators _

/-- The spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y_{p,q,r}` diagram, where `a` is the
central node and `bᵢ, cᵢ` are the first two nodes of the `i`-th arm. Each arm needs two nodes for
these to be arm nodes, which is what the hypotheses record. -/
def ySpiderRelator (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) (k : ℕ) :
    Relator (Fin (p + q + r + 1)) :=
  have harm : 2 ≤ p ∧ 2 ≤ q ∧ 2 ≤ r := ⟨hp, hq, hr⟩
  .pow (Relator.ofGenerators ⟨0, by omega⟩
    [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨0, by omega⟩,
      ⟨p + 1, by omega⟩, ⟨p + 2, by omega⟩, ⟨0, by omega⟩,
      ⟨p + q + 1, by omega⟩, ⟨p + q + 2, by omega⟩]) k

/-! ### The `Y₄₄₃` diagram

The twelve nodes are numbered `a = 0`, `b₁ c₁ d₁ e₁ = 1 2 3 4`, `b₂ c₂ d₂ e₂ = 5 6 7 8`, and
`b₃ c₃ d₃ = 9 10 11`, so that Bray's diagram

```text
e₁ -- d₁ -- c₁ -- b₁ -- a -- b₂ -- c₂ -- d₂ -- e₂
                        |
                        b₃ -- c₃ -- d₃
```

is `4 -- 3 -- 2 -- 1 -- 0 -- 5 -- 6 -- 7 -- 8` with the arm `0 -- 9 -- 10 -- 11`. -/

/-- The Coxeter matrix of the `Y₄₄₃` diagram, on twelve nodes. -/
abbrev y443CoxeterMatrix : CoxeterMatrix (Fin 12) := yCoxeterMatrix 4 4 3

/-- The spider relator of the `Y₄₄₃` diagram, `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ 10`. -/
def y443SpiderRelator : Relator (Fin 12) :=
  ySpiderRelator 4 4 3 (by omega) (by omega) (by omega) 10

/-- The spider relator of `Y₄₄₃` spelled out against the node numbering above. -/
theorem y443SpiderRelator_eq :
    y443SpiderRelator = .pow (Relator.ofGenerators 0 [1, 2, 0, 5, 6, 0, 9, 10]) 10 :=
  rfl

/-- The relators of the `Y₄₄₃` presentation: the Coxeter relators of the diagram followed by the
spider relator. -/
def y443Relators : List (Relator (Fin 12)) :=
  coxeterRelators y443CoxeterMatrix ++ [y443SpiderRelator]

/-- The `Y₄₄₃` diagram has `78` Coxeter relators, so the presentation has `79`. This is the count
Bray records for the group `M × 2` that `Y₄₄₃` presents; a presentation of the Monster itself adds
one further relator, `Z = 1` for the central involution, for `80`. -/
theorem length_y443Relators : y443Relators.length = 79 := by
  rw [y443Relators, List.length_append, length_coxeterRelators]
  rfl

/-- The `Y₄₄₄` diagram, on thirteen nodes, has `91` Coxeter relators, so its presentation of
`(M × M) : 2` has the `92` relators Bray records. -/
theorem length_coxeterRelators_y444 :
    (coxeterRelators (yCoxeterMatrix 4 4 4)).length + 1 = 92 := by
  rw [length_coxeterRelators]
  rfl

/-- The `Y₄₃₃` diagram, on eleven nodes, has `66` Coxeter relators. -/
theorem length_coxeterRelators_y433 :
    (coxeterRelators (yCoxeterMatrix 4 3 3)).length = 66 := by
  rw [length_coxeterRelators]
  rfl

/-! ### Executable checks on the pinned `Y₄₄₃` numbering

Each entry of the Coxeter matrix is `3` on an edge of the diagram and `2` off it, so these examples
read the diagram back out of the definition. -/

/-- The centre is joined to the first node of each of the three arms. -/
example : y443CoxeterMatrix 0 1 = 3 ∧ y443CoxeterMatrix 0 5 = 3 ∧ y443CoxeterMatrix 0 9 = 3 := by
  decide

/-- The first arm is the chain `0 -- 1 -- 2 -- 3 -- 4`. -/
example : y443CoxeterMatrix 1 2 = 3 ∧ y443CoxeterMatrix 2 3 = 3 ∧ y443CoxeterMatrix 3 4 = 3 := by
  decide

/-- The second arm is the chain `0 -- 5 -- 6 -- 7 -- 8`. -/
example : y443CoxeterMatrix 5 6 = 3 ∧ y443CoxeterMatrix 6 7 = 3 ∧ y443CoxeterMatrix 7 8 = 3 := by
  decide

/-- The third arm is the chain `0 -- 9 -- 10 -- 11`, of length three rather than four. -/
example : y443CoxeterMatrix 9 10 = 3 ∧ y443CoxeterMatrix 10 11 = 3 := by
  decide

/-- Distinct arms meet only at the centre, and no arm doubles back to it. -/
example : y443CoxeterMatrix 1 5 = 2 ∧ y443CoxeterMatrix 1 9 = 2 ∧ y443CoxeterMatrix 5 9 = 2 ∧
    y443CoxeterMatrix 0 2 = 2 ∧ y443CoxeterMatrix 0 4 = 2 ∧ y443CoxeterMatrix 4 8 = 2 := by
  decide

/-- The last node of the second arm is `8`, so `Y₄₄₃` has no node `12`: the arm ends rather than
continuing into the third arm. -/
example : y443CoxeterMatrix 8 9 = 2 := by
  decide

end TauCeti
