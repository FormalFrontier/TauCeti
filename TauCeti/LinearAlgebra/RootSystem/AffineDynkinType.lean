/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.LinearAlgebra.RootSystem.DynkinType

/-!
# Affine simply-laced Dynkin diagrams

The simply-laced affine diagrams carry one node more than the finite simply-laced diagram they
extend. Throughout this file a name such as `Aₙ` or `E₆` refers to the *affine* diagram, matching
the constructors below; the finite type it extends is `TauCeti.AffineDynkinType.finiteType`.

This file introduces the diagrams as an enumeration `TauCeti.AffineDynkinType`, attaches to each
its node count, its underlying `SimpleGraph` on `Fin t.nodes`, and its generalized Cartan matrix,
and proves the two facts every consumer needs: each diagram is connected, and its vector of *marks*
is a null vector of the Cartan matrix, positive at every node and normalized to `1` at a
distinguished one. The marks span the radical of the
symmetrized form; only the null-vector half of that statement is proved here.

Mathlib and Tau Ceti supply only the finite Cartan matrices: `TauCeti.DynkinType` has no affine
constructors. This file is the affine complement, and it is deliberately *graph* first, because its
consumers -- zigzag and preprojective algebras, and the McKay correspondence -- start from the
diagram rather than from a root system.

## Conventions

Except for `A₁`, an affine simply-laced diagram is a simple graph, and its generalized Cartan
matrix is `2I - A` for the adjacency matrix `A`. The exception is genuine: `A₁` has the
multiplicity-two matrix `!![2, -2; -2, 2]`, which is not `2I - A` for any simple graph
(`TauCeti.AffineDynkinType.cartanMatrix_A_one_ne_two_smul_one_sub_adjMatrix`). It is carved out by
`TauCeti.AffineDynkinType.IsGraphical`, which every simple-graph statement below assumes; the
underlying graph of `A₁` is still defined, as the single edge obtained by forgetting the
multiplicity, but it does not determine the matrix.

The node numberings are chosen so that every node other than `0` has a neighbour with a smaller
number, which reduces connectedness to a single induction. Explicitly:

* `Aₙ` is the cycle on `Fin (n + 1)`, Mathlib's `SimpleGraph.cycleGraph`;
* `Dₙ` is the path `0 - 1 - ⋯ - (n-2)` with a further leaf `n - 1` attached at node `1` and a
  further leaf `n` attached at node `n - 3`. For `n = 4` those two attachment nodes coincide and
  the diagram is the four-leaf star, as it should be;
* `E₆`, `E₇`, `E₈` are the trees `T₃,₃,₃`, `T₂,₄,₄`, `T₂,₃,₆` with the trivalent node numbered `0`
  and the arms numbered consecutively outwards.

## Main definitions

* `TauCeti.AffineDynkinType`: the enumeration `Aₙ`, `Dₙ`, `E₆`, `E₇`, `E₈`.
* `TauCeti.AffineDynkinType.nodes`, `.Valid`, `.IsGraphical`: node count and the two rank ranges.
* `TauCeti.AffineDynkinType.finiteType`: the finite Dynkin type an affine diagram extends.
* `TauCeti.AffineDynkinType.graph`: the underlying simple graph.
* `TauCeti.AffineDynkinType.cartanMatrix`: the generalized Cartan matrix.
* `TauCeti.AffineDynkinType.marks`: the marks, and `.affineNode`, the node whose mark is `1`.

## Main results

* `TauCeti.AffineDynkinType.connected_graph`: every affine simply-laced diagram is connected.
* `TauCeti.AffineDynkinType.cartanMatrix_eq_two_smul_one_sub_adjMatrix`: outside `A₁` the Cartan
  matrix is `2I - A`.
* `TauCeti.AffineDynkinType.sum_marks_neighborFinset`: twice the mark of a node is the sum of the
  marks of its neighbours.
* `TauCeti.AffineDynkinType.cartanMatrix_mulVec_marks`: the marks are a null vector, `Cδ = 0`.
* `TauCeti.AffineDynkinType.marks_affineNode`: the mark at the affine node is `1`.

## References

This is the affine simply-laced family of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See V. Kac, *Infinite dimensional Lie algebras*,
3rd ed., Chapter 4 and Table Aff 1, for the diagrams, their marks and the null root.
-/

public section

namespace TauCeti

open _root_.Matrix SimpleGraph

/-- A graph on `Fin n` in which every node other than `0` has a neighbour with a smaller number is
connected. Every numbering fixed below has this shape, which is why connectedness costs two lines
per diagram. -/
private theorem connected_of_exists_adj_lt {n : ℕ} [NeZero n] {G : SimpleGraph (Fin n)}
    (h : ∀ i : Fin n, (i : ℕ) ≠ 0 → ∃ j : Fin n, (j : ℕ) < (i : ℕ) ∧ G.Adj j i) :
    G.Connected := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let z : Fin n := ⟨0, hn⟩
  have hreach (i : Fin n) : G.Reachable z i := by
    induction hi : (i : ℕ) using Nat.strong_induction_on generalizing i with
    | _ k ih =>
        rcases eq_or_ne k 0 with rfl | hk
        · have hiz : i = z := Fin.ext (by simpa [z] using hi)
          rw [hiz]
        · obtain ⟨j, hji, hadj⟩ := h i (hi ▸ hk)
          exact (ih (j : ℕ) (hi ▸ hji) j rfl).trans hadj.reachable
  have : Nonempty (Fin n) := ⟨z⟩
  exact ⟨fun i j ↦ (hreach i).symm.trans (hreach j)⟩

/-- The simply-laced affine Dynkin diagrams: the families `Aₙ` and `Dₙ`, whose constructors accept
every natural number, together with the three exceptional diagrams. The ranges on which these are
the affine simply-laced diagrams of the classification are carried by
`TauCeti.AffineDynkinType.Valid`, not by the constructors. -/
inductive AffineDynkinType where
  /-- The affine diagram `Aₙ`, the cycle on `n + 1` nodes. -/
  | A (n : ℕ)
  /-- The affine diagram `Dₙ`, a path with two leaves attached at each end. -/
  | D (n : ℕ)
  /-- The exceptional affine diagram `E₆`. -/
  | E6
  /-- The exceptional affine diagram `E₇`. -/
  | E7
  /-- The exceptional affine diagram `E₈`. -/
  | E8
  deriving DecidableEq

namespace AffineDynkinType

/-- The number of nodes of an affine simply-laced diagram, one more than the rank of the finite
type it extends. This is exposed because it appears in the *type* of
`TauCeti.AffineDynkinType.graph`, so even reading `E6.graph` as a graph on `Fin 7` needs
`Fin E6.nodes` to reduce. -/
@[expose] def nodes : AffineDynkinType → ℕ
  | .A n => n + 1
  | .D n => n + 1
  | .E6 => 7
  | .E7 => 8
  | .E8 => 9

@[simp] lemma nodes_A (n : ℕ) : (A n).nodes = n + 1 := rfl
@[simp] lemma nodes_D (n : ℕ) : (D n).nodes = n + 1 := rfl
@[simp] lemma nodes_E6 : E6.nodes = 7 := rfl
@[simp] lemma nodes_E7 : E7.nodes = 8 := rfl
@[simp] lemma nodes_E8 : E8.nodes = 9 := rfl

lemma nodes_pos (t : AffineDynkinType) : 0 < t.nodes := by cases t <;> simp

instance (t : AffineDynkinType) : NeZero t.nodes := ⟨(t.nodes_pos).ne'⟩

/-- The finite Dynkin type that an affine simply-laced diagram extends. It has one node fewer
(`TauCeti.AffineDynkinType.nodes_eq_rank_finiteType_add_one`), the missing node being
`TauCeti.AffineDynkinType.affineNode`; the identification of the deleted diagram with the finite
one is not proved here. -/
def finiteType : AffineDynkinType → DynkinType
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

/-- An affine simply-laced diagram has one node more than the finite type it extends. -/
lemma nodes_eq_rank_finiteType_add_one (t : AffineDynkinType) :
    t.nodes = t.finiteType.rank + 1 := by cases t <;> rfl

/-- The finite type extended by an affine simply-laced diagram is simply laced. -/
lemma isSimplyLaced_finiteType (t : AffineDynkinType) : t.finiteType.IsSimplyLaced := by
  cases t <;> simp

/-- The ranges on which the affine simply-laced diagrams are pairwise distinct. Outside them the
names are degenerate or repeat one another: `A₀` names no diagram, while `D₃` is `A₃` and `D₂`
is `A₁ × A₁`. -/
def Valid : AffineDynkinType → Prop
  | .A n => 1 ≤ n
  | .D n => 4 ≤ n
  | .E6 | .E7 | .E8 => True

instance : DecidablePred Valid := fun t ↦
  match t with
  | .A n => inferInstanceAs (Decidable (1 ≤ n))
  | .D n => inferInstanceAs (Decidable (4 ≤ n))
  | .E6 | .E7 | .E8 => inferInstanceAs (Decidable True)

@[simp] lemma valid_A {n : ℕ} : (A n).Valid ↔ 1 ≤ n := Iff.rfl
@[simp] lemma valid_D {n : ℕ} : (D n).Valid ↔ 4 ≤ n := Iff.rfl
@[simp] lemma valid_E6 : E6.Valid := trivial
@[simp] lemma valid_E7 : E7.Valid := trivial
@[simp] lemma valid_E8 : E8.Valid := trivial

/-- A valid affine simply-laced diagram extends a valid finite Dynkin type. -/
lemma Valid.finiteType {t : AffineDynkinType} (ht : t.Valid) : t.finiteType.Valid := by
  cases t with
  | A n => simpa using ht
  | D n => simpa using ht
  | E6 | E7 | E8 => simp

/-- The valid affine simply-laced diagrams other than `A₁`, namely those whose generalized Cartan
matrix is `2I - A` for the adjacency matrix `A` of a simple graph. The one excluded diagram has the
multiplicity-two matrix `!![2, -2; -2, 2]`; see
`TauCeti.AffineDynkinType.cartanMatrix_A_one_ne_two_smul_one_sub_adjMatrix`. -/
def IsGraphical : AffineDynkinType → Prop
  | .A n => 2 ≤ n
  | .D n => 4 ≤ n
  | .E6 | .E7 | .E8 => True

instance : DecidablePred IsGraphical := fun t ↦
  match t with
  | .A n => inferInstanceAs (Decidable (2 ≤ n))
  | .D n => inferInstanceAs (Decidable (4 ≤ n))
  | .E6 | .E7 | .E8 => inferInstanceAs (Decidable True)

@[simp] lemma isGraphical_A {n : ℕ} : (A n).IsGraphical ↔ 2 ≤ n := Iff.rfl
@[simp] lemma isGraphical_D {n : ℕ} : (D n).IsGraphical ↔ 4 ≤ n := Iff.rfl
@[simp] lemma isGraphical_E6 : E6.IsGraphical := trivial
@[simp] lemma isGraphical_E7 : E7.IsGraphical := trivial
@[simp] lemma isGraphical_E8 : E8.IsGraphical := trivial

/-- A graphical affine simply-laced diagram is valid. -/
lemma IsGraphical.valid {t : AffineDynkinType} (ht : t.IsGraphical) : t.Valid := by
  cases t with
  | A n => simp only [isGraphical_A] at ht; simp only [valid_A]; omega
  | D n => exact ht
  | E6 | E7 | E8 => trivial

/-- Every valid affine simply-laced diagram other than `A₁` is graphical. -/
lemma IsGraphical.of_valid {t : AffineDynkinType} (ht : t.Valid) (h : t ≠ A 1) :
    t.IsGraphical := by
  cases t with
  | A n =>
      simp only [valid_A] at ht
      simp only [isGraphical_A]
      rcases Nat.lt_or_ge n 2 with h' | h'
      · exact absurd (congrArg A (by omega : n = 1)) h
      · exact h'
  | D n => exact ht
  | E6 | E7 | E8 => trivial

/-! ## The underlying graphs -/

/-- The edges of `Dₙ`, read on node numbers: the path `0 - 1 - ⋯ - (n-2)`, a leaf `n - 1`
attached at node `1`, and a leaf `n` attached at node `n - 3`. For `n = 4` the two attachment nodes
coincide, and the three clauses describe the four-leaf star. This is the *oriented* edge relation;
`TauCeti.AffineDynkinType.graph` symmetrizes it, and
`TauCeti.AffineDynkinType.adj_D_iff` reads the resulting adjacency back off. -/
@[expose] def dRel (n : ℕ) (i j : Fin (n + 1)) : Prop :=
  ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨
    ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((i : ℕ) = n - 3 ∧ (j : ℕ) = n)

instance (n : ℕ) : DecidableRel (dRel n) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The edges of `E₆ = T₃,₃,₃`: the trivalent node is `0`, and the three arms are `1, 2`, `3, 4`
and `5, 6`, numbered outwards. -/
def e6Edges : List (Fin 7 × Fin 7) := [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)]

/-- The edges of `E₇ = T₂,₄,₄`: the trivalent node is `0`, and the three arms are `1`, `2, 3, 4`
and `5, 6, 7`, numbered outwards. -/
def e7Edges : List (Fin 8 × Fin 8) := [(0, 1), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7)]

/-- The edges of `E₈ = T₂,₃,₆`: the trivalent node is `0`, and the three arms are `1`, `2, 3` and
`4, 5, 6, 7, 8`, numbered outwards. -/
def e8Edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- The underlying simple graph of an affine simply-laced diagram, on the node set `Fin t.nodes`.

Only `A₁` is not determined by this graph: its generalized Cartan matrix has the off-diagonal
entry `-2`, recording a double edge, and the graph below is the single edge left after forgetting
that multiplicity. Every statement relating the graph to the Cartan matrix therefore assumes
`TauCeti.AffineDynkinType.IsGraphical`. -/
def graph : (t : AffineDynkinType) → SimpleGraph (Fin t.nodes)
  | .A n => SimpleGraph.cycleGraph (n + 1)
  | .D n => SimpleGraph.fromRel (dRel n)
  | .E6 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e6Edges
  | .E7 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e7Edges
  | .E8 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e8Edges

@[simp] lemma graph_A (n : ℕ) : (A n).graph = SimpleGraph.cycleGraph (n + 1) := (rfl)
@[simp] lemma graph_D (n : ℕ) : (D n).graph = SimpleGraph.fromRel (dRel n) := (rfl)
@[simp] lemma graph_E6 : E6.graph = SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e6Edges := (rfl)
@[simp] lemma graph_E7 : E7.graph = SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e7Edges := (rfl)
@[simp] lemma graph_E8 : E8.graph = SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e8Edges := (rfl)

instance : (t : AffineDynkinType) → DecidableRel t.graph.Adj
  | .A n => inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph (n + 1)).Adj)
  | .D n => inferInstanceAs (DecidableRel (SimpleGraph.fromRel (dRel n)).Adj)
  | .E6 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e6Edges).Adj)
  | .E7 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e7Edges).Adj)
  | .E8 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e8Edges).Adj)

/-- Adjacency in `Dₙ`: the distinctness clause that `SimpleGraph.fromRel` adds is automatic, so
two nodes are adjacent exactly when one of them is joined to the other by `dRel`. -/
lemma adj_D_iff {n : ℕ} (hn : 4 ≤ n) {i j : Fin (n + 1)} :
    (D n).graph.Adj i j ↔ dRel n i j ∨ dRel n j i := by
  rw [graph_D, SimpleGraph.fromRel_adj]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  rintro rfl
  simp only [dRel] at h
  omega

/-! ## Connectedness -/

/-- Connectedness of `Dₙ`, stated on `Fin (n + 1)` so that the node numbers are literally the
numbers the proof reasons about. Node `k` with `1 ≤ k ≤ n - 2` is joined to `k - 1` along the
path, node `n - 1` is joined to node `1`, and node `n` is joined to node `n - 3`. -/
private theorem connected_fromRel_dRel {n : ℕ} (hn : 4 ≤ n) :
    (SimpleGraph.fromRel (dRel n)).Connected := by
  have key : ∀ i j : Fin (n + 1), dRel n i j → (SimpleGraph.fromRel (dRel n)).Adj i j := by
    intro i j h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    simp only [dRel] at h
    omega
  refine connected_of_exists_adj_lt fun i hi ↦ ?_
  have hi' : (i : ℕ) < n + 1 := i.isLt
  by_cases h1 : (i : ℕ) ≤ n - 2
  · have hlt : (i : ℕ) - 1 < n + 1 := by omega
    have hval : ((⟨(i : ℕ) - 1, hlt⟩ : Fin (n + 1)) : ℕ) = (i : ℕ) - 1 := rfl
    exact ⟨⟨(i : ℕ) - 1, hlt⟩, by omega, key ⟨(i : ℕ) - 1, hlt⟩ i (Or.inl ⟨by omega, h1⟩)⟩
  · have hlt : (1 : ℕ) < n + 1 := by omega
    have hval : ((⟨1, hlt⟩ : Fin (n + 1)) : ℕ) = 1 := rfl
    have hlt3 : n - 3 < n + 1 := by omega
    have hval3 : ((⟨n - 3, hlt3⟩ : Fin (n + 1)) : ℕ) = n - 3 := rfl
    by_cases h2 : (i : ℕ) = n - 1
    · exact ⟨⟨1, hlt⟩, by omega, key ⟨1, hlt⟩ i (Or.inr (Or.inl ⟨hval, h2⟩))⟩
    · exact ⟨⟨n - 3, hlt3⟩, by omega,
        key ⟨n - 3, hlt3⟩ i (Or.inr (Or.inr ⟨hval3, by omega⟩))⟩

/-- **Every affine simply-laced diagram is connected.** -/
theorem connected_graph {t : AffineDynkinType} (ht : t.Valid) : t.graph.Connected := by
  cases t with
  | A n => exact (graph_A n) ▸ SimpleGraph.cycleGraph_connected
  | D n => exact (graph_D n) ▸ connected_fromRel_dRel ht
  | E6 => exact connected_of_exists_adj_lt (by decide)
  | E7 => exact connected_of_exists_adj_lt (by decide)
  | E8 => exact connected_of_exists_adj_lt (by decide)

/-! ## The generalized Cartan matrix -/

/-- The generalized Cartan matrix of an affine simply-laced diagram: `2I - A` for the adjacency
matrix `A` of the underlying graph, except at `A₁`, whose two nodes carry a double edge and whose
matrix is `!![2, -2; -2, 2]`. -/
def cartanMatrix (t : AffineDynkinType) : Matrix (Fin t.nodes) (Fin t.nodes) ℤ :=
  match t with
  | .A 1 => !![2, -2; -2, 2]
  | x => (2 : ℤ) • (1 : Matrix (Fin x.nodes) (Fin x.nodes) ℤ) - x.graph.adjMatrix ℤ

@[simp] lemma cartanMatrix_A_one : (A 1).cartanMatrix = !![2, -2; -2, 2] := (rfl)

/-- Away from `A₁`, the generalized Cartan matrix is `2I - A`. -/
lemma cartanMatrix_eq_two_smul_one_sub_adjMatrix {t : AffineDynkinType} (ht : t.IsGraphical) :
    t.cartanMatrix = (2 : ℤ) • 1 - t.graph.adjMatrix ℤ := by
  cases t with
  | A n =>
      match n, ht with
      | 0, ht => exact absurd ht (by decide)
      | 1, ht => exact absurd ht (by decide)
      | (m + 2), _ => rfl
  | D n => rfl
  | E6 => rfl
  | E7 => rfl
  | E8 => rfl

/-- The entries of the generalized Cartan matrix away from `A₁`: `2` on the diagonal, `-1` at an
edge and `0` otherwise. -/
lemma cartanMatrix_apply {t : AffineDynkinType} (ht : t.IsGraphical) (i j : Fin t.nodes) :
    t.cartanMatrix i j = if i = j then 2 else if t.graph.Adj i j then -1 else 0 := by
  rw [cartanMatrix_eq_two_smul_one_sub_adjMatrix ht]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [ite_eq_right hij, ite_eq_right hij]
    split_ifs <;> norm_num

/-- The diagonal entries of the generalized Cartan matrix are `2`. -/
lemma cartanMatrix_apply_same {t : AffineDynkinType} (ht : t.IsGraphical)
    (i : Fin t.nodes) : t.cartanMatrix i i = 2 := by simp [cartanMatrix_apply ht]

/-- An edge of the diagram contributes the entry `-1`. -/
lemma cartanMatrix_apply_of_adj {t : AffineDynkinType} (ht : t.IsGraphical) {i j : Fin t.nodes}
    (h : t.graph.Adj i j) : t.cartanMatrix i j = -1 := by
  simp [cartanMatrix_apply ht, h, h.ne]

/-- Two distinct non-adjacent nodes contribute the entry `0`. -/
lemma cartanMatrix_apply_of_not_adj {t : AffineDynkinType} (ht : t.IsGraphical) {i j : Fin t.nodes}
    (hij : i ≠ j) (h : ¬ t.graph.Adj i j) : t.cartanMatrix i j = 0 := by
  simp [cartanMatrix_apply ht, hij, h]

/-- The generalized Cartan matrix of an affine simply-laced diagram is symmetric: the diagram is
simply laced, so no entry records a length ratio. -/
lemma isSymm_cartanMatrix {t : AffineDynkinType} (ht : t.IsGraphical) : t.cartanMatrix.IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, cartanMatrix_apply ht, cartanMatrix_apply ht]
  rcases eq_or_ne i j with rfl | hij
  · rfl
  · simp only [ite_eq_right hij, ite_eq_right hij.symm, adj_comm t.graph j i]

/-- **`A₁` is not the diagram of a simple graph.** Its off-diagonal entry is `-2`, while `2I - A`
has off-diagonal entries `0` and `-1` for the adjacency matrix `A` of any simple graph. This is why
every statement above relating `cartanMatrix` to `graph` assumes
`TauCeti.AffineDynkinType.IsGraphical`. -/
theorem cartanMatrix_A_one_ne_two_smul_one_sub_adjMatrix (G : SimpleGraph (Fin (A 1).nodes))
    [DecidableRel G.Adj] : (A 1).cartanMatrix ≠ (2 : ℤ) • 1 - G.adjMatrix ℤ := by
  intro h
  have h01 := congrFun (congrFun h 0) 1
  have hL : (A 1).cartanMatrix 0 1 = -2 := by decide
  rw [hL] at h01
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    SimpleGraph.adjMatrix_apply] at h01
  split_ifs at h01 <;> omega

/-! ## The marks and the null vector -/

/-- The marks of `Dₙ`: `2` at each interior path node `1, …, n - 3` and `1` at each of the four
leaves `0`, `n - 2`, `n - 1` and `n`. -/
@[expose] def dMarks (n : ℕ) (i : Fin (n + 1)) : ℤ :=
  if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ n - 3 then 2 else 1

/-- The **marks** of an affine simply-laced diagram: the positive integer vector `δ` killed by the
generalized Cartan matrix (`TauCeti.AffineDynkinType.cartanMatrix_mulVec_marks`), normalized so
that `δ` is `1` at `TauCeti.AffineDynkinType.affineNode`. Away from `A₁` this is the local balance
condition `2 δᵢ = ∑_{j ∼ i} δⱼ` at every node. -/
def marks : (t : AffineDynkinType) → Fin t.nodes → ℤ
  | .A _ => fun _ ↦ 1
  | .D n => dMarks n
  | .E6 => ![3, 2, 1, 2, 1, 2, 1]
  | .E7 => ![4, 2, 3, 2, 1, 3, 2, 1]
  | .E8 => ![6, 3, 4, 2, 5, 4, 3, 2, 1]

@[simp] lemma marks_A (n : ℕ) (i : Fin (A n).nodes) : (A n).marks i = 1 := (rfl)
@[simp] lemma marks_D (n : ℕ) : (D n).marks = dMarks n := (rfl)
@[simp] lemma marks_E6 : E6.marks = ![3, 2, 1, 2, 1, 2, 1] := (rfl)
@[simp] lemma marks_E7 : E7.marks = ![4, 2, 3, 2, 1, 3, 2, 1] := (rfl)
@[simp] lemma marks_E8 : E8.marks = ![6, 3, 4, 2, 5, 4, 3, 2, 1] := (rfl)

/-- The **affine node** of an affine simply-laced diagram: the distinguished node at which the
marks are normalized to `1` (`TauCeti.AffineDynkinType.marks_affineNode`). It is the node whose
deletion leaves the finite diagram of `TauCeti.AffineDynkinType.finiteType`. -/
def affineNode : (t : AffineDynkinType) → Fin t.nodes
  | .A _ => 0
  | .D _ => 0
  | .E6 => 2
  | .E7 => 4
  | .E8 => 8

@[simp] lemma affineNode_A (n : ℕ) : (A n).affineNode = 0 := (rfl)
@[simp] lemma affineNode_D (n : ℕ) : (D n).affineNode = 0 := (rfl)
@[simp] lemma affineNode_E6 : E6.affineNode = 2 := (rfl)
@[simp] lemma affineNode_E7 : E7.affineNode = 4 := (rfl)
@[simp] lemma affineNode_E8 : E8.affineNode = 8 := (rfl)

/-- Every mark is positive. -/
lemma marks_pos {t : AffineDynkinType} (i : Fin t.nodes) : 0 < t.marks i := by
  cases t with
  | A n => simp
  | D n => rw [marks_D]; unfold dMarks; split_ifs <;> norm_num
  | E6 => revert i; decide
  | E7 => revert i; decide
  | E8 => revert i; decide

/-- The marks are normalized to be `1` at the affine node. -/
@[simp] lemma marks_affineNode (t : AffineDynkinType) : t.marks t.affineNode = 1 := by
  cases t with
  | A n => rfl
  | D n => rw [marks_D, affineNode_D]; unfold dMarks; norm_num
  | E6 => decide
  | E7 => decide
  | E8 => decide

/-! ### The local balance condition -/

/-- Rewriting a sum over the neighbours of `i` as a sum over an explicitly listed set. -/
private lemma sum_neighborFinset_eq {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (f : V → ℤ) (i : V) (s : Finset V) (hs : ∀ j, G.Adj i j ↔ j ∈ s) :
    ∑ j ∈ G.neighborFinset i, f j = ∑ j ∈ s, f j := by
  refine Finset.sum_congr (Finset.ext fun j ↦ ?_) fun _ _ ↦ rfl
  rw [SimpleGraph.mem_neighborFinset, hs]

/-- The neighbours of a node of `Dₙ`, as an arithmetic condition on node numbers: the packed form
`TauCeti.AffineDynkinType.adj_D_iff` with both orientations of `dRel` written out. -/
private lemma adj_dRel_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n + 1)) :
    (SimpleGraph.fromRel (dRel n)).Adj i j ↔
      ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n - 1) ∨
          ((i : ℕ) = n - 3 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = n - 3 ∧ (i : ℕ) = n) := by
  have h := adj_D_iff (n := n) hn (i := i) (j := j)
  rw [graph_D] at h
  rw [h]
  simp only [dRel]
  omega

/-- **The local balance condition for `Dₙ`**: at every node the marks of the neighbours sum to
twice the mark of the node. The seven cases are the leaf `0`, the branch node `1`, an interior path
node, the branch node `n - 3`, and the three remaining leaves `n - 2`, `n - 1` and `n`; the star
`D₄`, where the two branch nodes coincide, is checked separately. -/
private lemma sum_dMarks_neighborFinset {n : ℕ} (hn : 4 ≤ n) (i : Fin (n + 1)) :
    ∑ j ∈ (SimpleGraph.fromRel (dRel n)).neighborFinset i, dMarks n j = 2 * dMarks n i := by
  rcases eq_or_lt_of_le hn with rfl | hn5
  · revert i; decide
  have hi : (i : ℕ) < n + 1 := i.isLt
  by_cases c0 : (i : ℕ) = 0
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨1, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs, Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  by_cases c1 : (i : ℕ) = 1
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n - 1, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega),
      Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  by_cases c2 : (i : ℕ) ≤ n - 4
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨(i : ℕ) - 1, by omega⟩, ⟨(i : ℕ) + 1, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs,
      Finset.sum_insert (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega),
      Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  by_cases c3 : (i : ℕ) = n - 3
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨n - 4, by omega⟩, ⟨n - 2, by omega⟩, ⟨n, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs,
      Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega),
      Finset.sum_insert (by simp only [Finset.mem_singleton, Fin.ext_iff]; omega),
      Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  by_cases c4 : (i : ℕ) = n - 2
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨n - 3, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs, Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  by_cases c5 : (i : ℕ) = n - 1
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨1, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs, Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega
  · have hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔
        j ∈ ({⟨n - 3, by omega⟩} : Finset (Fin (n + 1))) := by
      intro j
      rw [adj_dRel_iff hn]
      simp only [Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [sum_neighborFinset_eq _ i _ hs, Finset.sum_singleton]
    simp only [dMarks]
    split_ifs <;> omega

/-- The local balance condition for `Aₙ`: every node of a cycle on at least three nodes has two
neighbours, and every mark of `Aₙ` is `1`. -/
private lemma sum_one_neighborFinset_cycleGraph {m : ℕ} (i : Fin (m + 3)) :
    ∑ _j ∈ (SimpleGraph.cycleGraph (m + 3)).neighborFinset i, (1 : ℤ) = 2 * 1 := by
  rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.cycleGraph_degree_three_le]
  norm_num

/-- **The marks satisfy the local balance condition**: away from `A₁`, twice the mark of a node is
the sum of the marks of its neighbours. -/
theorem sum_marks_neighborFinset {t : AffineDynkinType} (ht : t.IsGraphical) (i : Fin t.nodes) :
    ∑ j ∈ t.graph.neighborFinset i, t.marks j = 2 * t.marks i := by
  cases t with
  | A n =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by simp only [isGraphical_A] at ht; omega⟩
      exact sum_one_neighborFinset_cycleGraph i
  | D n => exact sum_dMarks_neighborFinset ht i
  | E6 => revert i; decide
  | E7 => revert i; decide
  | E8 => revert i; decide

/-- **The marks are a null vector of the generalized Cartan matrix**: `Cδ = 0`. Together with
`TauCeti.AffineDynkinType.marks_pos` and `TauCeti.AffineDynkinType.marks_affineNode` this exhibits
the radical direction of an affine simply-laced diagram, normalized at the affine node. -/
theorem cartanMatrix_mulVec_marks {t : AffineDynkinType} (ht : t.Valid) :
    t.cartanMatrix *ᵥ t.marks = 0 := by
  by_cases h : t = A 1
  · subst h; decide
  · have hg : t.IsGraphical := IsGraphical.of_valid ht h
    funext i
    have hbal := sum_marks_neighborFinset hg i
    simp only [cartanMatrix_eq_two_smul_one_sub_adjMatrix hg, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Pi.smul_apply, Matrix.one_mulVec, smul_eq_mul,
      SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply]
    omega

end AffineDynkinType

end TauCeti
