/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.Combinatorics.SimpleGraph.Connected
public import TauCeti.LinearAlgebra.RootSystem.DynkinType
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Diagram

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

`TauCeti.DynkinType` has no affine constructors, and Mathlib's `CartanMatrix` family names no
affine type either, with one exception: the generalized `CartanMatrix.E n` continues the `E`
diagram past the finite range, and `CartanMatrix.E 9` is the affine `E₈` matrix under a different
numbering (`TauCeti.AffineDynkinType.cartanMatrix_E8_eq_submatrix_cartanMatrix_E`). Tau Ceti also
already carries affine matrices as *obstructions* inside the finite-type classification:
`TauCeti.doubleForkCartanMatrix n` is the affine `Dₘ` matrix for `m = n + 5`, and
`TauCeti.starCartanMatrix` at `![2, 2, 2]`, `![1, 3, 3]` and `![1, 2, 5]` is the affine `E₆`, `E₇`
and `E₈` matrix. Those live on the sum and sigma
index types that make the classification argument uniform rather than on `Fin`, and their marks are
rational and unnormalized -- `TauCeti.starMark ![2, 2, 2]` is `9` times the marks below -- so
identifying them with the diagrams of this file is a relabelling problem of its own, of a piece
with the Bourbaki relabelling that the roadmap asks for and that is not proved here either. This
file is the affine complement, and it is deliberately *graph* first, because its consumers --
zigzag and preprojective algebras, and the McKay correspondence -- start from the diagram rather
than from a root system.

## Conventions

Except for `A₁`, an affine simply-laced diagram is a simple graph, and its generalized Cartan
matrix is `2I - A` for the adjacency matrix `A`. The exception is genuine: `A₁` has the
multiplicity-two matrix `!![2, -2; -2, 2]`, which is not `2I - A` for any simple graph
(`TauCeti.AffineDynkinType.cartanMatrix_A_one_ne_two_smul_one_sub_adjMatrix`). It is carved out by
`TauCeti.AffineDynkinType.IsGraphical`, which every statement reading an entry of the Cartan matrix
off the graph assumes; the underlying graph of `A₁` is still defined, as the single edge obtained
by forgetting the multiplicity, but it does not determine the matrix. The statements that survive
at `A₁` -- the diagonal, the symmetry, the diagram of the matrix and the null vector -- carry no
such hypothesis.

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

* `TauCeti.AffineDynkinType.graph_connected`: every affine simply-laced diagram is connected.
* `TauCeti.AffineDynkinType.graph_D_adj`, `.graph_E6_adj`, `.graph_E7_adj`, `.graph_E8_adj`:
  adjacency in each diagram, as a condition on node numbers.
* `TauCeti.AffineDynkinType.cartanMatrix_eq_two_smul_one_sub_adjMatrix`: outside `A₁` the Cartan
  matrix is `2I - A`.
* `TauCeti.AffineDynkinType.graph_eq_diagramGraph_cartanMatrix`: the graph is the diagram of the
  Cartan matrix in the sense of `TauCeti.diagramGraph`, at `A₁` too.
* `TauCeti.AffineDynkinType.cartanMatrix_E8_eq_submatrix_cartanMatrix_E`: affine `E₈` is Mathlib's
  `CartanMatrix.E 9`, relabelled.
* `TauCeti.AffineDynkinType.sum_marks_neighborFinset_eq_two_mul`: twice the mark of a node is the
  sum of the marks of its neighbours.
* `TauCeti.AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero`: the marks are a null vector,
  `Cδ = 0`.
* `TauCeti.AffineDynkinType.marks_affineNode`: the mark at the affine node is `1`.

## References

This is the affine simply-laced family of Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`; the `E₈` numbering below is the one that roadmap's
`Suggested.lean` fixes in `affineE8ArmRel`. See V. Kac, *Infinite dimensional Lie algebras*,
3rd ed., Chapter 4 and Table Aff 1, for the diagrams, their marks and the null root.
-/

public section

namespace TauCeti

open _root_.Matrix SimpleGraph

/-- The simply-laced affine Dynkin diagrams: the families `Aₙ` and `Dₙ`, whose constructors accept
every natural number, together with the three exceptional diagrams. The ranges on which these are
the affine simply-laced diagrams of the classification are carried by
`TauCeti.AffineDynkinType.Valid`, not by the constructors. -/
inductive AffineDynkinType where
  /-- The affine diagram `Aₙ`: the cycle on `n + 1` nodes for `n ≥ 2`, and for `n = 1` the two
  nodes joined by a double edge. -/
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

/-- A graphical affine simply-laced diagram is not `A₁`. -/
lemma IsGraphical.ne_A_one {t : AffineDynkinType} (ht : t.IsGraphical) : t ≠ A 1 := by
  rintro rfl
  simp only [isGraphical_A] at ht
  omega

/-- Every valid affine simply-laced diagram other than `A₁` is graphical. -/
lemma IsGraphical.of_valid_of_ne_A_one {t : AffineDynkinType} (ht : t.Valid) (h : t ≠ A 1) :
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
`TauCeti.AffineDynkinType.graph_D_adj` reads the resulting adjacency back off. -/
def dRel (n : ℕ) (i j : Fin (n + 1)) : Prop :=
  ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨
    ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((i : ℕ) = n - 3 ∧ (j : ℕ) = n)

instance (n : ℕ) : DecidableRel (dRel n) := fun i j ↦
  inferInstanceAs (Decidable (((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨
    ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((i : ℕ) = n - 3 ∧ (j : ℕ) = n)))

/-- The edges of `E₆ = T₃,₃,₃`: the trivalent node is `0`, and the three arms are `1, 2`, `3, 4`
and `5, 6`, numbered outwards. -/
def e6Edges : List (Fin 7 × Fin 7) := [(0, 1), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)]

/-- The edges of `E₇ = T₂,₄,₄`: the trivalent node is `0`, and the three arms are `1`, `2, 3, 4`
and `5, 6, 7`, numbered outwards. -/
def e7Edges : List (Fin 8 × Fin 8) :=
  [(0, 1), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7)]

/-- The edges of `E₈ = T₂,₃,₆`: the trivalent node is `0`, and the three arms are `1`, `2, 3` and
`4, 5, 6, 7, 8`, numbered outwards. -/
def e8Edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)]

/-- The underlying simple graph of an affine simply-laced diagram, on the node set `Fin t.nodes`.

Only `A₁` is not determined by this graph: its generalized Cartan matrix has the off-diagonal
entry `-2`, recording a double edge, and the graph below is the single edge left after forgetting
that multiplicity. Every statement reading an entry of the Cartan matrix off the graph therefore
assumes `TauCeti.AffineDynkinType.IsGraphical`. -/
def graph : (t : AffineDynkinType) → SimpleGraph (Fin t.nodes)
  | .A n => SimpleGraph.cycleGraph (n + 1)
  | .D n => SimpleGraph.fromRel (dRel n)
  | .E6 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e6Edges
  | .E7 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e7Edges
  | .E8 => SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e8Edges

@[simp] lemma graph_A (n : ℕ) : (A n).graph = SimpleGraph.cycleGraph (n + 1) := (rfl)

-- The edge data of the remaining diagrams is implementation detail: it is left unexposed, only
-- this private unfolding of `Dₙ` reads it back, and `graph_D_adj`, `graph_E6_adj`, `graph_E7_adj`
-- and `graph_E8_adj` are the adjacency handles a consumer needs. `dRel` and the edge lists
-- themselves stay public only because the exposed `DecidableRel` instances below mention them,
-- and an exposed declaration may not mention a private one.
private lemma graph_D (n : ℕ) : (D n).graph = SimpleGraph.fromRel (dRel n) := (rfl)

instance : (t : AffineDynkinType) → DecidableRel t.graph.Adj
  | .A n => inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph (n + 1)).Adj)
  | .D n => inferInstanceAs (DecidableRel (SimpleGraph.fromRel (dRel n)).Adj)
  | .E6 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e6Edges).Adj)
  | .E7 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e7Edges).Adj)
  | .E8 => inferInstanceAs (DecidableRel (SimpleGraph.fromRel fun i j ↦ (i, j) ∈ e8Edges).Adj)

/-- **Adjacency in `Dₙ`**, as a condition on node numbers: consecutive numbers along the path
`0 - 1 - ⋯ - (n-2)`, the leaf `n - 1` at node `1`, and the leaf `n` at node `n - 3`, each in both
orientations. -/
lemma graph_D_adj {n : ℕ} (hn : 4 ≤ n) {i j : Fin (n + 1)} :
    (D n).graph.Adj i j ↔
      ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n - 1) ∨
          ((i : ℕ) = n - 3 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = n - 3 ∧ (i : ℕ) = n) := by
  rw [graph_D, SimpleGraph.fromRel_adj]
  simp only [dRel]
  constructor
  · rintro ⟨-, h⟩
    omega
  · intro h
    exact ⟨by rintro rfl; omega, by omega⟩

/-- **Adjacency in `E₆ = T₃,₃,₃`**: the six edges, listed as the pairs of node numbers they join,
smaller number first. -/
lemma graph_E6_adj (i j : Fin E6.nodes) : E6.graph.Adj i j ↔
    (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
      [((0 : ℕ), (1 : ℕ)), (1, 2), (0, 3), (3, 4), (0, 5), (5, 6)] := by
  revert i j
  decide

/-- **Adjacency in `E₇ = T₂,₄,₄`**: the seven edges, listed as the pairs of node numbers they join,
smaller number first. -/
lemma graph_E7_adj (i j : Fin E7.nodes) : E7.graph.Adj i j ↔
    (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
      [((0 : ℕ), (1 : ℕ)), (0, 2), (2, 3), (3, 4), (0, 5), (5, 6), (6, 7)] := by
  revert i j
  decide

/-- **Adjacency in `E₈ = T₂,₃,₆`**: the eight edges, listed as the pairs of node numbers they join,
smaller number first. -/
lemma graph_E8_adj (i j : Fin E8.nodes) : E8.graph.Adj i j ↔
    (min (i : ℕ) (j : ℕ), max (i : ℕ) (j : ℕ)) ∈
      [((0 : ℕ), (1 : ℕ)), (0, 2), (2, 3), (0, 4), (4, 5), (5, 6), (6, 7), (7, 8)] := by
  revert i j
  decide

/-! ## Connectedness -/

/-- Connectedness of `Dₙ`. Node `k` with `1 ≤ k ≤ n - 2` is joined to `k - 1` along the path, node
`n - 1` is joined to node `1`, and node `n` is joined to node `n - 3`, so every node other than `0`
has a neighbour with a smaller number. -/
private theorem graph_D_connected {n : ℕ} (hn : 4 ≤ n) : (D n).graph.Connected := by
  refine connected_fin_of_exists_adj_lt (D n).nodes_pos fun i hi ↦ ?_
  have hi' : (i : ℕ) < n + 1 := i.isLt
  -- In each branch the neighbour is named by its node number. The `hval` equations are `rfl`, and
  -- are stated only so that the `omega` calls after them can read that number off the `Fin.mk`.
  by_cases h1 : (i : ℕ) ≤ n - 2
  · have hlt : (i : ℕ) - 1 < n + 1 := by omega
    have hval : ((⟨(i : ℕ) - 1, hlt⟩ : Fin (n + 1)) : ℕ) = (i : ℕ) - 1 := rfl
    exact ⟨⟨(i : ℕ) - 1, hlt⟩, by omega, (graph_D_adj hn).2 (by omega)⟩
  · have hlt : (1 : ℕ) < n + 1 := by omega
    have hval : ((⟨1, hlt⟩ : Fin (n + 1)) : ℕ) = 1 := rfl
    have hlt3 : n - 3 < n + 1 := by omega
    have hval3 : ((⟨n - 3, hlt3⟩ : Fin (n + 1)) : ℕ) = n - 3 := rfl
    by_cases h2 : (i : ℕ) = n - 1
    · exact ⟨⟨1, hlt⟩, by omega, (graph_D_adj hn).2 (by omega)⟩
    · exact ⟨⟨n - 3, hlt3⟩, by omega, (graph_D_adj hn).2 (by omega)⟩

/-- **Every affine simply-laced diagram is connected.** -/
theorem graph_connected {t : AffineDynkinType} (ht : t.Valid) : t.graph.Connected := by
  cases t with
  | A n => exact (graph_A n) ▸ SimpleGraph.cycleGraph_connected
  | D n => exact graph_D_connected ht
  | E6 => exact connected_fin_of_exists_adj_lt E6.nodes_pos (by decide)
  | E7 => exact connected_fin_of_exists_adj_lt E7.nodes_pos (by decide)
  | E8 => exact connected_fin_of_exists_adj_lt E8.nodes_pos (by decide)

/-! ## The generalized Cartan matrix -/

/-- The generalized Cartan matrix of an affine simply-laced diagram: `2I - A` for the adjacency
matrix `A` of the underlying graph, except at `A₁`, whose two nodes carry a double edge and whose
matrix is `!![2, -2; -2, 2]`. -/
def cartanMatrix (t : AffineDynkinType) : Matrix (Fin t.nodes) (Fin t.nodes) ℤ :=
  match t with
  | .A 1 => !![2, -2; -2, 2]
  | x => (2 : ℤ) • (1 : Matrix (Fin x.nodes) (Fin x.nodes) ℤ) - x.graph.adjMatrix ℤ

@[simp] lemma cartanMatrix_A_one : (A 1).cartanMatrix = !![2, -2; -2, 2] := (rfl)

/-- `A₁` is the only diagram whose matrix is not `2I - A`, so the formula holds at every other
diagram, the degenerate ones outside `TauCeti.AffineDynkinType.Valid` included. The public form
just below restricts it to a graphical diagram, which is the hypothesis a consumer carries; this
one is what the statements that survive at `A₁` are proved from. -/
private lemma cartanMatrix_eq_two_smul_one_sub_adjMatrix_of_ne_A_one {t : AffineDynkinType}
    (h : t ≠ A 1) : t.cartanMatrix = (2 : ℤ) • 1 - t.graph.adjMatrix ℤ := by
  cases t with
  | A n =>
      match n with
      | 0 => rfl
      | 1 => exact absurd rfl h
      | (m + 2) => rfl
  | D n => rfl
  | E6 => rfl
  | E7 => rfl
  | E8 => rfl

/-- Away from `A₁`, the generalized Cartan matrix is `2I - A`. -/
lemma cartanMatrix_eq_two_smul_one_sub_adjMatrix {t : AffineDynkinType} (ht : t.IsGraphical) :
    t.cartanMatrix = (2 : ℤ) • 1 - t.graph.adjMatrix ℤ :=
  cartanMatrix_eq_two_smul_one_sub_adjMatrix_of_ne_A_one ht.ne_A_one

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

/-- The diagonal entries of the generalized Cartan matrix are `2`, `A₁` included. -/
lemma cartanMatrix_apply_same (t : AffineDynkinType) (i : Fin t.nodes) :
    t.cartanMatrix i i = 2 := by
  by_cases h : t = A 1
  · subst h
    revert i
    decide
  · rw [cartanMatrix_eq_two_smul_one_sub_adjMatrix_of_ne_A_one h, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply_eq, SimpleGraph.adjMatrix_apply]
    simp

/-- Away from `A₁`, an edge of the diagram contributes the entry `-1`. At `A₁` the single edge
contributes `-2`. -/
lemma cartanMatrix_apply_of_adj {t : AffineDynkinType} (ht : t.IsGraphical) {i j : Fin t.nodes}
    (h : t.graph.Adj i j) : t.cartanMatrix i j = -1 := by
  simp [cartanMatrix_apply ht, h, h.ne]

/-- Away from `A₁`, two distinct non-adjacent nodes contribute the entry `0`. -/
lemma cartanMatrix_apply_of_not_adj {t : AffineDynkinType} (ht : t.IsGraphical) {i j : Fin t.nodes}
    (hij : i ≠ j) (h : ¬ t.graph.Adj i j) : t.cartanMatrix i j = 0 := by
  simp [cartanMatrix_apply ht, hij, h]

/-- The generalized Cartan matrix of an affine simply-laced diagram is symmetric, `A₁` included:
the diagram is simply laced, so no entry records a length ratio. -/
lemma cartanMatrix_isSymm (t : AffineDynkinType) : t.cartanMatrix.IsSymm := by
  by_cases h : t = A 1
  · subst h
    refine Matrix.IsSymm.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> decide
  · rw [cartanMatrix_eq_two_smul_one_sub_adjMatrix_of_ne_A_one h]
    exact (Matrix.isSymm_one.smul (2 : ℤ)).sub (SimpleGraph.isSymm_adjMatrix _)

/-- **The graph of an affine simply-laced diagram is the diagram of its generalized Cartan
matrix**, `A₁` included: the double edge there still shows up as a pair of nonzero entries. This is
what carries the general results about `TauCeti.diagramGraph` over to `graph`. -/
theorem graph_eq_diagramGraph_cartanMatrix {t : AffineDynkinType} (ht : t.Valid) :
    t.graph = diagramGraph t.cartanMatrix := by
  by_cases h : t = A 1
  · subst h
    ext i j
    revert i j
    decide
  · have hg : t.IsGraphical := IsGraphical.of_valid_of_ne_A_one ht h
    ext i j
    rw [diagramGraph_adj]
    refine ⟨fun hadj ↦ ⟨hadj.ne, ?_, ?_⟩, fun ⟨hne, h1, _⟩ ↦ ?_⟩
    · rw [cartanMatrix_apply_of_adj hg hadj]; norm_num
    · rw [cartanMatrix_apply_of_adj hg hadj.symm]; norm_num
    · by_contra hadj
      rw [cartanMatrix_apply_of_not_adj hg hne hadj] at h1
      exact h1 rfl

/-- **`A₁` is not the diagram of a simple graph.** Its off-diagonal entry is `-2`, while `2I - A`
has off-diagonal entries `0` and `-1` for the adjacency matrix `A` of any simple graph. This is why
every statement above reading an entry of `cartanMatrix` off `graph` assumes
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

/-- **Affine `E₈` is Mathlib's `CartanMatrix.E 9`**, whose generalized `E`-family continues the
`E` diagram past the finite range. The relabelling is the transposition exchanging the trivalent
node, numbered `0` here and `3` there; the arms of `1`, `2` and `5` nodes then match up. -/
theorem cartanMatrix_E8_eq_submatrix_cartanMatrix_E :
    E8.cartanMatrix = (CartanMatrix.E 9).submatrix (Equiv.swap 0 3) (Equiv.swap 0 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-! ## The marks and the null vector -/

/-- The marks of `Dₙ`: `2` at each interior path node `1, …, n - 3` and `1` at each of the four
leaves `0`, `n - 2`, `n - 1` and `n`. -/
private def dMarks (n : ℕ) (i : Fin (n + 1)) : ℤ :=
  if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ n - 3 then 2 else 1

/-- The **marks** of an affine simply-laced diagram: the positive integer vector `δ` killed by the
generalized Cartan matrix (`TauCeti.AffineDynkinType.cartanMatrix_mulVec_marks_eq_zero`),
normalized so that `δ` is `1` at `TauCeti.AffineDynkinType.affineNode`. Away from `A₁` this is the
local balance condition `2 δᵢ = ∑_{j ∼ i} δⱼ` at every node. -/
def marks : (t : AffineDynkinType) → Fin t.nodes → ℤ
  | .A _ => fun _ ↦ 1
  | .D n => dMarks n
  | .E6 => ![3, 2, 1, 2, 1, 2, 1]
  | .E7 => ![4, 2, 3, 2, 1, 3, 2, 1]
  | .E8 => ![6, 3, 4, 2, 5, 4, 3, 2, 1]

@[simp] lemma marks_A_apply (n : ℕ) (i : Fin (A n).nodes) : (A n).marks i = 1 := (rfl)

/-- The marks of `Dₙ` node by node: `2` on the interior of the path, `1` on the four leaves. -/
@[simp] lemma marks_D_apply (n : ℕ) (i : Fin (D n).nodes) :
    (D n).marks i = if 1 ≤ (i : ℕ) ∧ (i : ℕ) ≤ n - 3 then 2 else 1 := (rfl)

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
  | D n => rw [marks_D_apply]; split_ifs <;> norm_num
  | E6 => revert i; decide
  | E7 => revert i; decide
  | E8 => revert i; decide

/-- The marks are normalized to be `1` at the affine node. -/
@[simp] lemma marks_affineNode (t : AffineDynkinType) : t.marks t.affineNode = 1 := by
  cases t with
  | A n => rfl
  | D n => simp
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
`TauCeti.AffineDynkinType.graph_D_adj`, transported to the relation the graph is built from. -/
private lemma adj_dRel_iff {n : ℕ} (hn : 4 ≤ n) (i j : Fin (n + 1)) :
    (SimpleGraph.fromRel (dRel n)).Adj i j ↔
      ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) ≤ n - 2) ∨ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) ≤ n - 2) ∨
        ((i : ℕ) = 1 ∧ (j : ℕ) = n - 1) ∨ ((j : ℕ) = 1 ∧ (i : ℕ) = n - 1) ∨
          ((i : ℕ) = n - 3 ∧ (j : ℕ) = n) ∨ ((j : ℕ) = n - 3 ∧ (i : ℕ) = n) := by
  have h := graph_D_adj (n := n) hn (i := i) (j := j)
  rwa [graph_D] at h

/-- The sum of the marks of `Dₙ` over the neighbours of a node, once those neighbours have been
listed. Each of the seven node roles below supplies its own list and reads the resulting sum off
with `omega`; this is the step they share. -/
private lemma sum_dMarks_of_adj_iff {n : ℕ} (i : Fin (n + 1)) (l : List (Fin (n + 1)))
    (hl : l.Nodup) (hs : ∀ j, (SimpleGraph.fromRel (dRel n)).Adj i j ↔ j ∈ l) :
    ∑ j ∈ (SimpleGraph.fromRel (dRel n)).neighborFinset i, dMarks n j = (l.map (dMarks n)).sum := by
  rw [sum_neighborFinset_eq _ i l.toFinset (by simpa using hs), List.sum_toFinset _ hl]

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
  · rw [sum_dMarks_of_adj_iff i [⟨1, by omega⟩] (by simp) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  by_cases c1 : (i : ℕ) = 1
  · rw [sum_dMarks_of_adj_iff i [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n - 1, by omega⟩]
      (by simp [Fin.ext_iff]; omega) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  by_cases c2 : (i : ℕ) ≤ n - 4
  · rw [sum_dMarks_of_adj_iff i [⟨(i : ℕ) - 1, by omega⟩, ⟨(i : ℕ) + 1, by omega⟩]
      (by simp [Fin.ext_iff]) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  by_cases c3 : (i : ℕ) = n - 3
  · rw [sum_dMarks_of_adj_iff i [⟨n - 4, by omega⟩, ⟨n - 2, by omega⟩, ⟨n, by omega⟩]
      (by simp [Fin.ext_iff]; omega) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  by_cases c4 : (i : ℕ) = n - 2
  · rw [sum_dMarks_of_adj_iff i [⟨n - 3, by omega⟩] (by simp) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  by_cases c5 : (i : ℕ) = n - 1
  · rw [sum_dMarks_of_adj_iff i [⟨1, by omega⟩] (by simp) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
    split_ifs <;> omega
  · rw [sum_dMarks_of_adj_iff i [⟨n - 3, by omega⟩] (by simp) fun j ↦ by
      rw [adj_dRel_iff hn]; simp only [List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
      omega]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dMarks]
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
theorem sum_marks_neighborFinset_eq_two_mul {t : AffineDynkinType} (ht : t.IsGraphical)
    (i : Fin t.nodes) : ∑ j ∈ t.graph.neighborFinset i, t.marks j = 2 * t.marks i := by
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
theorem cartanMatrix_mulVec_marks_eq_zero {t : AffineDynkinType} (ht : t.Valid) :
    t.cartanMatrix *ᵥ t.marks = 0 := by
  by_cases h : t = A 1
  · subst h; decide
  · have hg : t.IsGraphical := IsGraphical.of_valid_of_ne_A_one ht h
    funext i
    have hbal := sum_marks_neighborFinset_eq_two_mul hg i
    simp only [cartanMatrix_eq_two_smul_one_sub_adjMatrix hg, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Pi.smul_apply, Matrix.one_mulVec, smul_eq_mul,
      SimpleGraph.adjMatrix_mulVec_apply, Pi.zero_apply]
    omega

end AffineDynkinType

end TauCeti
