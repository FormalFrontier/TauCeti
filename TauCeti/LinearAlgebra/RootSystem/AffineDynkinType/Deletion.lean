/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

/-!
# Deleting the affine node of an affine simply-laced diagram

An affine simply-laced diagram carries one node more than the finite simply-laced diagram it
extends, and deleting the distinguished node `TauCeti.AffineDynkinType.affineNode` recovers that
finite diagram. This file makes the statement precise, and in the form its consumers need: not as a
bare existence of some relabelling, but as one explicit injection
`TauCeti.AffineDynkinType.bourbakiNode` of the finite node set into the affine one, whose image is
the complement of the affine node and along which the generalized Cartan matrix restricts to the
standard Bourbaki-numbered Cartan matrix of `TauCeti.AffineDynkinType.finiteType`.

The relabelling is not the identity, because the two numberings are chosen for different purposes.
`TauCeti.AffineDynkinType.graph` numbers a diagram so that every node other than `0` has a
neighbour with a smaller number, which is what makes connectedness a single induction; the finite
`TauCeti.DynkinType.cartanMatrix` is numbered as in Bourbaki's plates. Concretely:

* `Ãₙ` is the cycle on `Fin (n + 1)` and its affine node is `0`, so the Bourbaki node `i` of `Aₙ`
  is node `i + 1` of the affine diagram: deleting `0` from a cycle leaves a path.
* The affine `Dₙ` is the path `0 - ⋯ - (n-2)` with a leaf `n - 1` at node `1` and a leaf `n` at
  node `n - 3`, and its affine node is `0`. Deleting it leaves the chain
  `(n-1) - 1 - 2 - ⋯ - (n-3)` forking into `n - 2` and `n`, which is `Dₙ` with the Bourbaki node
  `0` at node `n - 1` of the affine diagram, the Bourbaki nodes `1, …, n - 2` unmoved, and the
  Bourbaki node `n - 1` at node `n` of the affine diagram.
* The affine `E₆`, `E₇` and `E₈` are the stars `T₃,₃,₃`, `T₂,₄,₄` and `T₂,₃,₆` with the trivalent
  node numbered `0` and arms numbered outwards, and their affine nodes are the outermost nodes
  `2`, `4` and `8` of a longest arm. Deleting one shortens that arm by one, giving `T₂,₃,₃`,
  `T₂,₃,₄` and `T₂,₃,₅`; the relabelling sends Bourbaki's trivalent node `3` to `0` and matches
  the arms by length.

`Ã₁`, the one diagram whose generalized Cartan matrix is not read off a simple graph, is included:
deleting either of its two nodes leaves the single node of `A₁`, and the doubled edge disappears
with the node it is deleted from. So the theorems below assume only
`TauCeti.AffineDynkinType.Valid`.

## Main definitions

* `TauCeti.AffineDynkinType.finiteType`: the finite `TauCeti.DynkinType` an affine simply-laced
  diagram extends.
* `TauCeti.AffineDynkinType.bourbakiNode`: the node of the affine diagram carrying a given
  Bourbaki-numbered node of that finite type.
* `TauCeti.AffineDynkinType.bourbakiGraphEmbedding`: the same map, bundled as an embedding of the
  finite Dynkin diagram into the affine one.

## Main results

* `TauCeti.AffineDynkinType.range_bourbakiNode`: **the relabelling is a bijection onto the
  complement of the affine node**, so it does describe a deletion.
* `TauCeti.AffineDynkinType.cartanMatrix_submatrix_bourbakiNode`: **deleting the affine node from
  the generalized Cartan matrix gives the standard Cartan matrix of the finite type**, in the
  Bourbaki numbering.
* `TauCeti.AffineDynkinType.comap_graph_bourbakiNode`: the same statement for the diagrams
  themselves.
* `TauCeti.AffineDynkinType.rank_finiteType_add_one` and
  `TauCeti.AffineDynkinType.Valid.finiteType`: the finite type has one node fewer, and is valid
  when the affine type is.

## References

This is the affine-node deletion clause of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See V. Kac, *Infinite dimensional Lie algebras*,
3rd ed., Chapter 4 and Table Aff 1, and Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*,
plates I-VII for the finite numbering.
-/

public section

namespace TauCeti

namespace AffineDynkinType

/-- The finite Dynkin type an affine simply-laced diagram extends: the type of the same name.
This is exposed because `TauCeti.DynkinType.rank` of it appears in the *type* of
`TauCeti.AffineDynkinType.bourbakiNode`. -/
@[expose] def finiteType : AffineDynkinType → DynkinType
  | .A n => .A n
  | .D n => .D n
  | .E6 => .E6
  | .E7 => .E7
  | .E8 => .E8

@[simp] lemma finiteType_A (n : ℕ) : (A n).finiteType = .A n := (rfl)
@[simp] lemma finiteType_D (n : ℕ) : (D n).finiteType = .D n := (rfl)
@[simp] lemma finiteType_E6 : E6.finiteType = .E6 := (rfl)
@[simp] lemma finiteType_E7 : E7.finiteType = .E7 := (rfl)
@[simp] lemma finiteType_E8 : E8.finiteType = .E8 := (rfl)

/-- **An affine simply-laced diagram has one node more than the finite type it extends.** -/
@[simp] lemma rank_finiteType_add_one (t : AffineDynkinType) : t.finiteType.rank + 1 = t.nodes := by
  cases t <;> rfl

/-- The finite type extended by a valid affine type is valid: the two validity ranges are the
same, `1 ≤ n` for `Aₙ` and `4 ≤ n` for `Dₙ`. -/
lemma Valid.finiteType {t : AffineDynkinType} (ht : t.Valid) : t.finiteType.Valid := by
  cases t with
  | A n => exact DynkinType.valid_A.mpr (valid_A.mp ht)
  | D n => exact DynkinType.valid_D.mpr (valid_D.mp ht)
  | E6 => exact DynkinType.valid_E6
  | E7 => exact DynkinType.valid_E7
  | E8 => exact DynkinType.valid_E8

/-- The finite type extended by an affine simply-laced type is simply laced. -/
lemma isSimplyLaced_finiteType (t : AffineDynkinType) : t.finiteType.IsSimplyLaced := by
  cases t with
  | A n => exact DynkinType.isSimplyLaced_A n
  | D n => exact DynkinType.isSimplyLaced_D n
  | E6 => exact DynkinType.isSimplyLaced_E6
  | E7 => exact DynkinType.isSimplyLaced_E7
  | E8 => exact DynkinType.isSimplyLaced_E8

/-! ## The relabelling -/

/-- The **Bourbaki relabelling**: the node of an affine simply-laced diagram carrying the node
numbered `i` in the Bourbaki numbering of the finite type it extends. It is injective and its image
is the complement of `TauCeti.AffineDynkinType.affineNode`
(`TauCeti.AffineDynkinType.range_bourbakiNode`), so it exhibits the finite diagram as the affine
one with its affine node deleted.

The three exceptional maps are read off the arms: Bourbaki's trivalent node `3` goes to the
trivalent node `0`, its length-one arm `1` to the length-one arm `1`, its length-two arm `2, 0` to
the length-two arm, and its long arm outwards along the long arm of the affine diagram. -/
def bourbakiNode : (t : AffineDynkinType) → Fin t.finiteType.rank → Fin t.nodes
  | .A _ => Fin.succ
  | .D n => fun i ↦
      ⟨if (i : ℕ) = 0 then n - 1 else if (i : ℕ) = n - 1 then n else (i : ℕ), by
        have hi : (i : ℕ) < n := i.isLt
        have hnodes : (D n).nodes = n + 1 := rfl
        rw [hnodes]
        split_ifs <;> omega⟩
  | .E6 => ![4, 1, 3, 0, 5, 6]
  | .E7 => ![3, 1, 2, 0, 5, 6, 7]
  | .E8 => ![3, 1, 2, 0, 4, 5, 6, 7]

lemma bourbakiNode_A (n : ℕ) : (A n).bourbakiNode = Fin.succ := (rfl)

/-- Bourbaki node `i` maps to affine node `i + 1` in the cycle `Ãₙ`. -/
@[simp] lemma bourbakiNode_A_val (n : ℕ) (i : Fin (A n).finiteType.rank) :
    (((A n).bourbakiNode i : Fin (A n).nodes) : ℕ) = (i : ℕ) + 1 := (rfl)

/-- The relabelling of the affine `Dₙ` moves only the two ends: the Bourbaki node `0` sits at the
affine leaf `n - 1`, and the Bourbaki node `n - 1` at the affine leaf `n`. -/
@[simp] lemma bourbakiNode_D_val (n : ℕ) (i : Fin (D n).finiteType.rank) :
    (((D n).bourbakiNode i : Fin (D n).nodes) : ℕ) =
      if (i : ℕ) = 0 then n - 1 else if (i : ℕ) = n - 1 then n else (i : ℕ) := (rfl)

@[simp] lemma bourbakiNode_E6 : E6.bourbakiNode = ![4, 1, 3, 0, 5, 6] := (rfl)
@[simp] lemma bourbakiNode_E7 : E7.bourbakiNode = ![3, 1, 2, 0, 5, 6, 7] := (rfl)
@[simp] lemma bourbakiNode_E8 : E8.bourbakiNode = ![3, 1, 2, 0, 4, 5, 6, 7] := (rfl)

/-- **The relabelling is injective.** -/
theorem bourbakiNode_injective {t : AffineDynkinType} (ht : t.Valid) :
    Function.Injective t.bourbakiNode := by
  cases t with
  | A n => rw [bourbakiNode_A]; exact Fin.succ_injective n
  | D n =>
      intro i j hij
      have hn : 4 ≤ n := valid_D.mp ht
      have hi : (i : ℕ) < n := i.isLt
      have hj : (j : ℕ) < n := j.isLt
      have hval := congrArg Fin.val hij
      rw [bourbakiNode_D_val, bourbakiNode_D_val] at hval
      refine Fin.ext ?_
      split_ifs at hval <;> omega
  | E6 =>
      have h : Function.Injective (![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) := by decide
      rw [bourbakiNode_E6]
      exact h
  | E7 =>
      have h : Function.Injective (![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) := by decide
      rw [bourbakiNode_E7]
      exact h
  | E8 =>
      have h : Function.Injective (![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) := by decide
      rw [bourbakiNode_E8]
      exact h

/-- **The relabelling avoids the affine node**: no Bourbaki-numbered node of the finite type is
sent to the node that is being deleted. -/
theorem bourbakiNode_ne_affineNode {t : AffineDynkinType} (ht : t.Valid)
    (i : Fin t.finiteType.rank) : t.bourbakiNode i ≠ t.affineNode := by
  cases t with
  | A n =>
      rw [affineNode_A, Ne, Fin.ext_iff, bourbakiNode_A_val, Fin.val_zero]
      omega
  | D n =>
      have hn : 4 ≤ n := valid_D.mp ht
      have hi : (i : ℕ) < n := i.isLt
      rw [affineNode_D, Ne, Fin.ext_iff, bourbakiNode_D_val, Fin.val_zero]
      split_ifs <;> omega
  | E6 =>
      have h : ∀ a : Fin 6, (![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) a ≠ (2 : Fin 7) := by decide
      rw [bourbakiNode_E6, affineNode_E6]
      exact h i
  | E7 =>
      have h : ∀ a : Fin 7, (![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) a ≠ (4 : Fin 8) := by decide
      rw [bourbakiNode_E7, affineNode_E7]
      exact h i
  | E8 =>
      have h : ∀ a : Fin 8, (![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) a ≠ (8 : Fin 9) := by
        decide
      rw [bourbakiNode_E8, affineNode_E8]
      exact h i

/-- **Every node other than the affine one is hit by the relabelling.** -/
theorem exists_bourbakiNode_eq {t : AffineDynkinType} (ht : t.Valid) {x : Fin t.nodes}
    (hx : x ≠ t.affineNode) : ∃ i, t.bourbakiNode i = x := by
  cases t with
  | A n =>
      rw [affineNode_A, Ne, Fin.ext_iff, Fin.val_zero] at hx
      have hlt : (x : ℕ) < n + 1 := x.isLt
      have hr : (A n).finiteType.rank = n := rfl
      refine ⟨⟨(x : ℕ) - 1, by omega⟩, Fin.ext ?_⟩
      rw [bourbakiNode_A_val, Fin.val_mk]
      omega
  | D n =>
      have hn : 4 ≤ n := valid_D.mp ht
      rw [affineNode_D, Ne, Fin.ext_iff, Fin.val_zero] at hx
      have hlt : (x : ℕ) < n + 1 := x.isLt
      have hr : (D n).finiteType.rank = n := rfl
      rcases eq_or_ne (x : ℕ) (n - 1) with hx1 | hx1
      · refine ⟨⟨0, by omega⟩, Fin.ext ?_⟩
        rw [bourbakiNode_D_val, Fin.val_mk]
        split_ifs <;> omega
      · rcases eq_or_ne (x : ℕ) n with hx2 | hx2
        · refine ⟨⟨n - 1, by omega⟩, Fin.ext ?_⟩
          rw [bourbakiNode_D_val, Fin.val_mk]
          split_ifs <;> omega
        · refine ⟨⟨(x : ℕ), by omega⟩, Fin.ext ?_⟩
          rw [bourbakiNode_D_val, Fin.val_mk]
          split_ifs
          omega
  | E6 =>
      have h : ∀ y : Fin 7, y ≠ (2 : Fin 7) →
          ∃ a : Fin 6, (![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) a = y := by decide
      rw [affineNode_E6] at hx
      rw [bourbakiNode_E6]
      exact h x hx
  | E7 =>
      have h : ∀ y : Fin 8, y ≠ (4 : Fin 8) →
          ∃ a : Fin 7, (![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) a = y := by decide
      rw [affineNode_E7] at hx
      rw [bourbakiNode_E7]
      exact h x hx
  | E8 =>
      have h : ∀ y : Fin 9, y ≠ (8 : Fin 9) →
          ∃ a : Fin 8, (![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) a = y := by decide
      rw [affineNode_E8] at hx
      rw [bourbakiNode_E8]
      exact h x hx

/-- **Deleting the affine node**: the relabelling is a bijection from the nodes of the finite type
onto the nodes of the affine diagram other than the affine node. -/
theorem range_bourbakiNode {t : AffineDynkinType} (ht : t.Valid) :
    Set.range t.bourbakiNode = {t.affineNode}ᶜ := by
  ext x
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  exact ⟨by rintro ⟨i, rfl⟩; exact bourbakiNode_ne_affineNode ht i, exists_bourbakiNode_eq ht⟩

/-! ## Restricting the Cartan matrix -/

/-- An entrywise criterion for a matrix to be the principal submatrix of a generalized Cartan
matrix cut out by an injection: `2` on the diagonal, `-1` at an edge of the affine diagram and `0`
between two distinct nonadjacent nodes. -/
private lemma cartanMatrix_submatrix_eq {t : AffineDynkinType} (htg : t.IsGraphical)
    {m : ℕ} {f : Fin m → Fin t.nodes} (hf : Function.Injective f)
    {M : Matrix (Fin m) (Fin m) ℤ} (hdiag : ∀ i, M i i = 2)
    (hadj : ∀ i j, i ≠ j → t.graph.Adj (f i) (f j) → M i j = -1)
    (hnot : ∀ i j, i ≠ j → ¬ t.graph.Adj (f i) (f j) → M i j = 0) :
    t.cartanMatrix.submatrix f f = M := by
  ext i j
  rcases eq_or_ne i j with rfl | hne
  · rw [Matrix.submatrix_apply, cartanMatrix_apply_same, hdiag]
  · by_cases hA : t.graph.Adj (f i) (f j)
    · rw [Matrix.submatrix_apply, cartanMatrix_apply_of_adj htg hA, hadj i j hne hA]
    · rw [Matrix.submatrix_apply,
        cartanMatrix_apply_of_not_adj (fun hc ↦ hne (hf hc)) hA, hnot i j hne hA]

/-- The standard Cartan matrix of the finite type, entry by entry, in the shape needed to compare
it with the affine one. The generic `TauCeti.DynkinType.cartanMatrix_A` cannot be rewritten
directly under `TauCeti.AffineDynkinType.finiteType`, because the index type of a matrix depends on
the type it belongs to. -/
private lemma finiteType_cartanMatrix_apply_A (n : ℕ) (i j : Fin (A n).finiteType.rank) :
    (A n).finiteType.cartanMatrix i j = CartanMatrix.A n i j :=
  congrFun (congrFun (DynkinType.cartanMatrix_A n) i) j

private lemma finiteType_cartanMatrix_apply_D (n : ℕ) (i j : Fin (D n).finiteType.rank) :
    (D n).finiteType.cartanMatrix i j = CartanMatrix.D n i j :=
  congrFun (congrFun (DynkinType.cartanMatrix_D n) i) j

private lemma finiteType_cartanMatrix_apply_E6 (i j : Fin E6.finiteType.rank) :
    E6.finiteType.cartanMatrix i j = CartanMatrix.E 6 i j :=
  congrFun (congrFun DynkinType.cartanMatrix_E6 i) j

private lemma finiteType_cartanMatrix_apply_E7 (i j : Fin E7.finiteType.rank) :
    E7.finiteType.cartanMatrix i j = CartanMatrix.E 7 i j :=
  congrFun (congrFun DynkinType.cartanMatrix_E7 i) j

private lemma finiteType_cartanMatrix_apply_E8 (i j : Fin E8.finiteType.rank) :
    E8.finiteType.cartanMatrix i j = CartanMatrix.E 8 i j :=
  congrFun (congrFun DynkinType.cartanMatrix_E8 i) j

/-- The standard Cartan matrix of type `Aₙ`, entry by entry. -/
private lemma cartanMatrix_a_eq (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n i j =
      if i = j then 2 else
      if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0 :=
  rfl

/-- The standard Cartan matrix of type `Dₙ`, entry by entry. -/
private lemma cartanMatrix_d_eq (n : ℕ) (i j : Fin n) :
    CartanMatrix.D n i j =
      if i = j then 2 else
      if n ≤ 2 then 0 else
      if (i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n then -1 else
      if (j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n then -1 else
      if (i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n) then -1 else
      if (j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n) then -1 else 0 :=
  rfl

/-- The standard Cartan matrix of type `E6`, entry by entry, against the edge list of the affine
diagram read along the relabelling: the two agree node pair by node pair. -/
private lemma cartanMatrix_e6_eq (a b : Fin 6) :
    CartanMatrix.E 6 a b =
      if a = b then 2 else
      if (min (((![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) a : Fin 7) : ℕ)
            (((![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) b : Fin 7) : ℕ),
          max (((![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) a : Fin 7) : ℕ)
            (((![4, 1, 3, 0, 5, 6] : Fin 6 → Fin 7) b : Fin 7) : ℕ)) ∈
        [((0 : ℕ), (1 : ℕ)), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)] then -1 else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The standard Cartan matrix of type `E7`, entry by entry, against the edge list of the affine
diagram read along the relabelling: the two agree node pair by node pair. -/
private lemma cartanMatrix_e7_eq (a b : Fin 7) :
    CartanMatrix.E 7 a b =
      if a = b then 2 else
      if (min (((![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) a : Fin 8) : ℕ)
            (((![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) b : Fin 8) : ℕ),
          max (((![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) a : Fin 8) : ℕ)
            (((![3, 1, 2, 0, 5, 6, 7] : Fin 7 → Fin 8) b : Fin 8) : ℕ)) ∈
        [((0 : ℕ), (1 : ℕ)), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7)] then -1 else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- The standard Cartan matrix of type `E8`, entry by entry, against the edge list of the affine
diagram read along the relabelling: the two agree node pair by node pair. -/
private lemma cartanMatrix_e8_eq (a b : Fin 8) :
    CartanMatrix.E 8 a b =
      if a = b then 2 else
      if (min (((![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) a : Fin 9) : ℕ)
            (((![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) b : Fin 9) : ℕ),
          max (((![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) a : Fin 9) : ℕ)
            (((![3, 1, 2, 0, 4, 5, 6, 7] : Fin 8 → Fin 9) b : Fin 9) : ℕ)) ∈
        [((0 : ℕ), (1 : ℕ)), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)] then -1
      else 0 := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Adjacency in the affine `Dₙ` transported along the relabelling: exactly the edges of the
Bourbaki-numbered finite `Dₙ` diagram, the path `0 - ⋯ - (n-3)` forking into the leaves `n - 2` and
`n - 1`. -/
private lemma graph_D_adj_bourbakiNode {n : ℕ} (hn : 4 ≤ n) (i j : Fin (D n).finiteType.rank) :
    (D n).graph.Adj ((D n).bourbakiNode i) ((D n).bourbakiNode j) ↔
      ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < n) ∨ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < n) ∨
        ((i : ℕ) + 3 = n ∧ ((j : ℕ) + 2 = n ∨ (j : ℕ) + 1 = n)) ∨
        ((j : ℕ) + 3 = n ∧ ((i : ℕ) + 2 = n ∨ (i : ℕ) + 1 = n)) := by
  have hi : (i : ℕ) < n := i.isLt
  have hj : (j : ℕ) < n := j.isLt
  rw [graph_D_adj (n := n) hn (i := (D n).bourbakiNode i) (j := (D n).bourbakiNode j),
    bourbakiNode_D_val, bourbakiNode_D_val]
  split_ifs <;> omega

/-- **Deleting the affine node from the generalized Cartan matrix gives the standard Cartan matrix
of the finite type**, in the Bourbaki numbering: the principal submatrix of `t.cartanMatrix` on the
nodes other than `t.affineNode`, read along `TauCeti.AffineDynkinType.bourbakiNode`, is
`t.finiteType.cartanMatrix`. -/
theorem cartanMatrix_submatrix_bourbakiNode {t : AffineDynkinType} (ht : t.Valid) :
    t.cartanMatrix.submatrix t.bourbakiNode t.bourbakiNode = t.finiteType.cartanMatrix := by
  cases t with
  | A n =>
      rcases eq_or_ne n 1 with rfl | hn1
      · -- `Ã₁` is the one diagram whose matrix is not read off its graph; both sides are `!![2]`.
        ext i j
        have hi : (i : ℕ) < 1 := i.isLt
        have hj : (j : ℕ) < 1 := j.isLt
        have hij : i = j := Fin.ext (by omega)
        subst hij
        rw [Matrix.submatrix_apply, cartanMatrix_apply_same, finiteType_cartanMatrix_apply_A]
        exact ((cartanMatrix_a_eq 1 i i).trans (ite_eq_left rfl)).symm
      · refine cartanMatrix_submatrix_eq (by simp [hn1]) (bourbakiNode_injective ht)
          (fun i ↦ ?_) (fun i j hne hA ↦ ?_) (fun i j hne hA ↦ ?_)
        · rw [finiteType_cartanMatrix_apply_A]
          exact (cartanMatrix_a_eq n i i).trans (ite_eq_left rfl)
        · rw [graph_A_adj (valid_A.mp ht), bourbakiNode_A_val, bourbakiNode_A_val] at hA
          have h : (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) := by omega
          rw [finiteType_cartanMatrix_apply_A]
          exact (cartanMatrix_a_eq n i j).trans ((ite_eq_right hne).trans (ite_eq_left h))
        · rw [graph_A_adj (valid_A.mp ht), bourbakiNode_A_val, bourbakiNode_A_val] at hA
          have h : ¬((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) := by omega
          rw [finiteType_cartanMatrix_apply_A]
          exact (cartanMatrix_a_eq n i j).trans ((ite_eq_right hne).trans (ite_eq_right h))
  | D n =>
      have hn : 4 ≤ n := valid_D.mp ht
      refine cartanMatrix_submatrix_eq (by simp) (bourbakiNode_injective ht)
        (fun i ↦ ?_) (fun i j hne hA ↦ ?_) (fun i j hne hA ↦ ?_)
      · rw [finiteType_cartanMatrix_apply_D]
        exact CartanMatrix.D_diag n i
      · rw [graph_D_adj_bourbakiNode hn] at hA
        rw [finiteType_cartanMatrix_apply_D]
        refine (cartanMatrix_d_eq n i j).trans ((ite_eq_right hne).trans ?_)
        split_ifs <;> omega
      · rw [graph_D_adj_bourbakiNode hn] at hA
        rw [finiteType_cartanMatrix_apply_D]
        refine (cartanMatrix_d_eq n i j).trans ((ite_eq_right hne).trans ?_)
        split_ifs <;> omega
  | E6 =>
      refine cartanMatrix_submatrix_eq (by simp) (bourbakiNode_injective ht)
        (fun i ↦ ?_) (fun i j hne hA ↦ ?_) (fun i j hne hA ↦ ?_)
      · rw [finiteType_cartanMatrix_apply_E6]
        exact CartanMatrix.E_diag 6 i
      · rw [graph_E6_adj, bourbakiNode_E6] at hA
        rw [finiteType_cartanMatrix_apply_E6]
        exact (cartanMatrix_e6_eq i j).trans ((ite_eq_right hne).trans (ite_eq_left hA))
      · rw [graph_E6_adj, bourbakiNode_E6] at hA
        rw [finiteType_cartanMatrix_apply_E6]
        exact (cartanMatrix_e6_eq i j).trans ((ite_eq_right hne).trans (ite_eq_right hA))
  | E7 =>
      refine cartanMatrix_submatrix_eq (by simp) (bourbakiNode_injective ht)
        (fun i ↦ ?_) (fun i j hne hA ↦ ?_) (fun i j hne hA ↦ ?_)
      · rw [finiteType_cartanMatrix_apply_E7]
        exact CartanMatrix.E_diag 7 i
      · rw [graph_E7_adj, bourbakiNode_E7] at hA
        rw [finiteType_cartanMatrix_apply_E7]
        exact (cartanMatrix_e7_eq i j).trans ((ite_eq_right hne).trans (ite_eq_left hA))
      · rw [graph_E7_adj, bourbakiNode_E7] at hA
        rw [finiteType_cartanMatrix_apply_E7]
        exact (cartanMatrix_e7_eq i j).trans ((ite_eq_right hne).trans (ite_eq_right hA))
  | E8 =>
      refine cartanMatrix_submatrix_eq (by simp) (bourbakiNode_injective ht)
        (fun i ↦ ?_) (fun i j hne hA ↦ ?_) (fun i j hne hA ↦ ?_)
      · rw [finiteType_cartanMatrix_apply_E8]
        exact CartanMatrix.E_diag 8 i
      · rw [graph_E8_adj, bourbakiNode_E8] at hA
        rw [finiteType_cartanMatrix_apply_E8]
        exact (cartanMatrix_e8_eq i j).trans ((ite_eq_right hne).trans (ite_eq_left hA))
      · rw [graph_E8_adj, bourbakiNode_E8] at hA
        rw [finiteType_cartanMatrix_apply_E8]
        exact (cartanMatrix_e8_eq i j).trans ((ite_eq_right hne).trans (ite_eq_right hA))

/-! ## Restricting the diagram -/

/-- **Deleting the affine node from the diagram gives the finite Dynkin diagram**: pulling the
affine diagram back along the Bourbaki relabelling is the diagram of the standard Cartan matrix of
the finite type. -/
theorem comap_graph_bourbakiNode {t : AffineDynkinType} (ht : t.Valid) :
    t.graph.comap t.bourbakiNode = diagramGraph t.finiteType.cartanMatrix := by
  rw [← cartanMatrix_submatrix_bourbakiNode ht,
    diagramGraph_submatrix (bourbakiNode_injective ht), graph_eq_diagramGraph_cartanMatrix]

/-- The Bourbaki relabelling as an **embedding of the finite Dynkin diagram into the affine
diagram**, whose image is the complement of the affine node
(`TauCeti.AffineDynkinType.range_bourbakiNode`). -/
def bourbakiGraphEmbedding {t : AffineDynkinType} (ht : t.Valid) :
    diagramGraph t.finiteType.cartanMatrix ↪g t.graph where
  toFun := t.bourbakiNode
  inj' := bourbakiNode_injective ht
  map_rel_iff' := by
    intro i j
    rw [← comap_graph_bourbakiNode ht]
    exact Iff.rfl

@[simp] lemma bourbakiGraphEmbedding_apply {t : AffineDynkinType} (ht : t.Valid)
    (i : Fin t.finiteType.rank) : bourbakiGraphEmbedding ht i = t.bourbakiNode i := (rfl)

end AffineDynkinType

end TauCeti
