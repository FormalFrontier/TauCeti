/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.Coxeter

/-!
# The `Y`-diagrams of the sporadic presentations

The Coxeter presentations that milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md` records for
the sporadic groups are `Y`-diagram presentations: the Coxeter relators of a `Y_{p,q,r}` diagram
together with one further relator, the *spider relator*. This file defines the parametric diagram
family and pins the `Y₄₄₃` node numbering, spider relator, and relator list used for the Monster.
It also checks the Coxeter-relator counts for `Y₄₄₄` and `Y₄₃₃`.

The counts are the check, and they are checked against published data rather than only against
themselves. J. N. Bray's presentation pages record `Y₄₄₃` as a 12-generator, 79-relator
presentation of `M × 2` and `Y₄₄₄` as a 13-generator, 92-relator presentation of `(M × M) : 2`.
Here `TauCeti.length_y443Relators` reproduces `79 = 78 + 1`, while
`TauCeti.length_coxeterRelators_y444` checks the `91` Coxeter relators before the spider relator,
which is not pinned for `Y₄₄₄` here. The roadmap's `80` for the Monster is `79` plus the relator
`Z = 1` for the central involution. These published counts fix the encoding convention: diagonal
entries `mᵢᵢ = 1` contribute the involution relators and each off-diagonal unordered pair
contributes exactly one relator.

## Main definitions

* `TauCeti.yParent`, `TauCeti.YAdjacent`, and `TauCeti.yCoxeterMatrix`: the node numbering,
  adjacency relation, and Coxeter matrix of the parametric `Y_{p,q,r}` diagram.
* `TauCeti.ySpiderRelator`: the spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y`-diagram.
* `TauCeti.y443CoxeterMatrix`, `TauCeti.y443SpiderRelator`, and `TauCeti.y443Relators`: the `Y₄₄₃`
  diagram, its spider relator, and the relator list they make up.

## Main results

* `TauCeti.length_y443Relators`: the total relator count for the pinned `Y₄₄₃` list.
* `TauCeti.length_coxeterRelators_y444` and `TauCeti.length_coxeterRelators_y433`: the
  Coxeter-relator count checks for those diagrams.
* `TauCeti.y443SpiderRelator_eq`: the spider word spelled out against the pinned node numbering.
* `TauCeti.y443RelatorsMulEquiv`: the group presented by `TauCeti.y443Relators` is the Coxeter
  group of the diagram with the spider relation imposed on top.

## References

The node numbering, the arm labels `a, bᵢ, cᵢ, dᵢ, eᵢ`, the spider word, and the relator counts `79`
and `92` follow J. N. Bray's
[presentation pages](https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html). The theorems
that these diagrams present the groups in question are Norton's (1990) and Ivanov's (1999) and are
not formalized here: no presentation of a named group is asserted in this file.
-/

public section

namespace TauCeti

/-! ## The parametric Y-diagram -/

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

/-- Non-adjacency in terms of the arm arithmetic: neither node is a non-central node whose
neighbour towards the centre is the other. -/
theorem not_YAdjacent_iff (p q i j : ℕ) :
    ¬YAdjacent p q i j ↔
      (i = 0 ∨ yParent p q i ≠ j) ∧ (j = 0 ∨ yParent p q j ≠ i) := by
  rw [YAdjacent]
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

/-- The spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃) ^ k` of a `Y_{p,q,r}` diagram, where `a` is the
central node and `bᵢ, cᵢ` are the first two nodes of the `i`-th arm. Each arm needs two nodes for
these to be arm nodes, which is what the hypotheses record. -/
def ySpiderRelator (p q r : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r) (k : ℕ) :
    Relator (Fin (p + q + r + 1)) :=
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
    y443SpiderRelator = .pow (Relator.ofGenerators 0 [1, 2, 0, 5, 6, 0, 9, 10]) 10 := by
  rw [y443SpiderRelator, ySpiderRelator]
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

/-- The group presented by the `Y₄₄₃` relator list is the Coxeter group of the diagram with the
spider relation imposed on top. -/
def y443RelatorsMulEquiv :
    PresentedGroup (Relator.relatorSet y443Relators) ≃*
      PresentedGroup (y443CoxeterMatrix.relationsSet ∪ Relator.relatorSet [y443SpiderRelator]) :=
  QuotientGroup.quotientMulEquivOfEq (by
    rw [y443Relators, normalClosure_relatorSet_coxeterRelators_append])

/-- The `Y₄₄₄` diagram, on thirteen nodes, has `91` Coxeter relators. Its spider relator is not
formalized here; adding that published relator gives the `92` relators Bray records for its
presentation of `(M × M) : 2`. -/
theorem length_coxeterRelators_y444 :
    (coxeterRelators (yCoxeterMatrix 4 4 4)).length = 91 := by
  rw [length_coxeterRelators]
  rfl

/-- The `Y₄₃₃` diagram, on eleven nodes, has `66` Coxeter relators. -/
theorem length_coxeterRelators_y433 :
    (coxeterRelators (yCoxeterMatrix 4 3 3)).length = 66 := by
  rw [length_coxeterRelators]
  rfl

/-! ### Executable checks on the pinned `Y₄₄₃` numbering

Each entry of the Coxeter matrix is `3` on an edge of the diagram and `2` off it, so these examples
read the diagram back out of the definitions. -/

/-- The centre is joined to the first node of each of the three arms. -/
example : y443CoxeterMatrix 0 1 = 3 ∧ y443CoxeterMatrix 0 5 = 3 ∧ y443CoxeterMatrix 0 9 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

/-- The first arm is the chain `0 -- 1 -- 2 -- 3 -- 4`. -/
example : y443CoxeterMatrix 1 2 = 3 ∧ y443CoxeterMatrix 2 3 = 3 ∧ y443CoxeterMatrix 3 4 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

/-- The second arm is the chain `0 -- 5 -- 6 -- 7 -- 8`. -/
example : y443CoxeterMatrix 5 6 = 3 ∧ y443CoxeterMatrix 6 7 = 3 ∧ y443CoxeterMatrix 7 8 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

/-- The third arm is the chain `0 -- 9 -- 10 -- 11`, of length three rather than four. -/
example : y443CoxeterMatrix 9 10 = 3 ∧ y443CoxeterMatrix 10 11 = 3 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

/-- Distinct arms meet only at the centre, and no arm doubles back to it. -/
example : y443CoxeterMatrix 1 5 = 2 ∧ y443CoxeterMatrix 1 9 = 2 ∧ y443CoxeterMatrix 5 9 = 2 ∧
    y443CoxeterMatrix 0 2 = 2 ∧ y443CoxeterMatrix 0 4 = 2 ∧ y443CoxeterMatrix 4 8 = 2 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

/-- The last node of the second arm is `8`, so `Y₄₄₃` has no node `12`: the arm ends rather than
continuing into the third arm. -/
example : y443CoxeterMatrix 8 9 = 2 := by
  simp only [yCoxeterMatrix_apply, YAdjacent, yParent]
  decide

end TauCeti
