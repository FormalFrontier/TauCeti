/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Covering
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Doubled quivers of simple graphs

The doubled quiver of a simple graph has the graph's vertices and one arrow in each direction over
every edge. Since adjacency in a simple graph is a proposition, this quiver is thin: it has no
loops or parallel arrows. Its canonical arrow reversal comes from symmetry of adjacency.

This file relates the quiver API to Mathlib's graph API. Total arrows are identified with graph
darts, stars and costars are identified with neighbor sets, and their cardinalities recover the
adjacency matrix, vertex degrees, and twice the number of edges. A graph homomorphism acts on
doubled quivers by a reversal-preserving prefunctor, and a graph isomorphism gives mutually inverse
prefunctors.

## Main definitions

* `TauCeti.DoubledQuiver`: the doubled quiver attached to a simple graph.
* `TauCeti.DoubledQuiver.totalArrowEquivDart`: its arrows are the graph's darts.
* `TauCeti.DoubledQuiver.map`: the prefunctor induced by a graph homomorphism.

## Main results

* `TauCeti.DoubledQuiver.card_hom_eq_adjMatrix`: arrow counts are adjacency-matrix entries.
* `TauCeti.DoubledQuiver.card_totalArrow_eq_twice_card_edges`: every edge gives two arrows.
* `TauCeti.DoubledQuiver.map_iso_comp_symm` and
  `TauCeti.DoubledQuiver.map_symm_comp_iso`: graph isomorphisms induce inverse prefunctors.

## References

This is the doubled-graph construction in Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

/-- The doubled quiver of a simple graph. Its vertices are the graph's vertices, and there is one
arrow `i ⟶ j` for every proof that `i` and `j` are adjacent. -/
@[expose]
def DoubledQuiver {V : Type u} (_G : SimpleGraph V) := V

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-- Include a graph vertex into the vertex type of its doubled quiver. -/
def vertex (v : V) : DoubledQuiver G := v

/-- The graph vertices and the doubled-quiver vertices are canonically equivalent. -/
def vertexEquiv : V ≃ DoubledQuiver G where
  toFun := vertex G
  invFun := fun v => v
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem vertexEquiv_apply (v : V) : vertexEquiv G v = vertex G v := (rfl)

@[simp]
theorem vertexEquiv_symm_apply (v : DoubledQuiver G) :
    vertex G ((vertexEquiv G).symm v) = v := (rfl)

@[simp]
theorem vertexEquiv_symm_vertex (v : V) : (vertexEquiv G).symm (vertex G v) = v := by
  rw [← vertexEquiv_apply]
  exact (vertexEquiv G).symm_apply_apply v

instance : _root_.Quiver (DoubledQuiver G) where
  Hom i j := PLift (G.Adj ((vertexEquiv G).symm i) ((vertexEquiv G).symm j))

instance : Quiver.IsThin (DoubledQuiver G) := fun i j => by
  change Subsingleton (PLift (G.Adj ((vertexEquiv G).symm i) ((vertexEquiv G).symm j)))
  infer_instance

instance [Finite V] : Finite (DoubledQuiver G) :=
  Finite.of_equiv V (vertexEquiv G)

instance [Fintype V] : Fintype (DoubledQuiver G) :=
  Fintype.ofEquiv V (vertexEquiv G)

instance (i j : DoubledQuiver G) : Finite (i ⟶ j) := by
  change Finite (PLift (G.Adj ((vertexEquiv G).symm i) ((vertexEquiv G).symm j)))
  infer_instance

instance [DecidableRel G.Adj] (i j : DoubledQuiver G) : Fintype (i ⟶ j) := by
  change Fintype (PLift (G.Adj ((vertexEquiv G).symm i) ((vertexEquiv G).symm j)))
  infer_instance

instance : HasReverse (DoubledQuiver G) where
  reverse' e := ⟨e.down.symm⟩

instance : HasInvolutiveReverse (DoubledQuiver G) where
  toHasReverse := inferInstance
  inv' _ := Subsingleton.elim _ _

/-- The arrow of the doubled quiver corresponding to an adjacency. -/
def arrow {i j : V} (h : G.Adj i j) : vertex G i ⟶ vertex G j :=
  ⟨by simpa only [vertexEquiv_symm_vertex] using h⟩

theorem arrow_down {i j : V} (h : G.Adj i j) :
    (arrow G h).down = (by simpa only [vertexEquiv_symm_vertex] using h) :=
  Subsingleton.elim _ _

@[simp] theorem reverse_arrow {i j : V} (h : G.Adj i j) :
    Quiver.reverse (arrow G h) = arrow G h.symm := by
  apply Subsingleton.elim

/-- There is an arrow from `i` to `j` exactly when the vertices are adjacent. -/
theorem nonempty_hom_iff {i j : V} :
    Nonempty (vertex G i ⟶ vertex G j) ↔ G.Adj i j := by
  constructor
  · rintro ⟨e⟩
    exact e.down
  · exact fun h => ⟨arrow G h⟩

/-- The arrow type from `i` to `j` is empty exactly when the vertices are not adjacent. -/
theorem isEmpty_hom_iff {i j : V} :
    IsEmpty (vertex G i ⟶ vertex G j) ↔ ¬G.Adj i j := by
  rw [← not_nonempty_iff]
  exact not_congr (nonempty_hom_iff G)

/-- All arrows in the doubled quiver, with their source and target. -/
abbrev TotalArrow := Σ i j : DoubledQuiver G, i ⟶ j

/-- The total arrows of the doubled quiver are the oriented edges, or darts, of the graph. -/
def totalArrowEquivDart : TotalArrow G ≃ G.Dart where
  toFun e := ⟨((vertexEquiv G).symm e.1, (vertexEquiv G).symm e.2.1), e.2.2.down⟩
  invFun d := ⟨vertex G d.fst, vertex G d.snd, arrow G d.adj⟩
  left_inv e := by
    obtain ⟨i, j, e⟩ := e
    rfl
  right_inv d := by
    obtain ⟨⟨i, j⟩, h⟩ := d
    rfl

@[simp]
theorem totalArrowEquivDart_apply (e : TotalArrow G) :
    totalArrowEquivDart G e =
      ⟨((vertexEquiv G).symm e.1, (vertexEquiv G).symm e.2.1), e.2.2.down⟩ := (rfl)

@[simp]
theorem totalArrowEquivDart_symm_apply (d : G.Dart) :
    (totalArrowEquivDart G).symm d =
      ⟨vertex G d.fst, vertex G d.snd, arrow G d.adj⟩ := (rfl)

/-- Reverse a total arrow, exchanging its source and target. -/
def reverseTotalArrow (e : TotalArrow G) : TotalArrow G :=
  ⟨e.2.1, e.1, Quiver.reverse e.2.2⟩

@[simp]
theorem totalArrowEquivDart_reverse (e : TotalArrow G) :
    totalArrowEquivDart G (reverseTotalArrow G e) = (totalArrowEquivDart G e).symm := by
  obtain ⟨i, j, e⟩ := e
  rfl

@[simp]
theorem reverseTotalArrow_reverseTotalArrow (e : TotalArrow G) :
    reverseTotalArrow G (reverseTotalArrow G e) = e := by
  obtain ⟨i, j, e⟩ := e
  simp [reverseTotalArrow]

/-- The arrows leaving a vertex are its neighbors in the graph. -/
def starEquivNeighborSet (v : V) :
    Quiver.Star (vertex G v) ≃ G.neighborSet v where
  toFun e := ⟨(vertexEquiv G).symm e.1,
    G.mem_neighborSet _ _ |>.mpr (by
      simpa only [vertexEquiv_symm_vertex] using e.2.down)⟩
  invFun w := ⟨vertex G w, arrow G w.property⟩
  left_inv e := by
    obtain ⟨w, e⟩ := e
    rfl
  right_inv w := by
    ext
    rfl

@[simp]
theorem starEquivNeighborSet_apply (v : V) (e : Quiver.Star (vertex G v)) :
    starEquivNeighborSet G v e =
      ⟨(vertexEquiv G).symm e.1,
        G.mem_neighborSet _ _ |>.mpr (by
          simpa only [vertexEquiv_symm_vertex] using e.2.down)⟩ := (rfl)

@[simp]
theorem starEquivNeighborSet_symm_apply (v : V) (w : G.neighborSet v) :
    (starEquivNeighborSet G v).symm w = ⟨vertex G w, arrow G w.property⟩ := (rfl)

/-- The arrows entering a vertex are also its neighbors in the graph. -/
def costarEquivNeighborSet (v : V) :
    Quiver.Costar (vertex G v) ≃ G.neighborSet v where
  toFun e := ⟨(vertexEquiv G).symm e.1,
    G.mem_neighborSet _ _ |>.mpr (by
      simpa only [vertexEquiv_symm_vertex] using e.2.down.symm)⟩
  invFun w := ⟨vertex G w, arrow G w.property.symm⟩
  left_inv e := by
    obtain ⟨w, e⟩ := e
    rfl
  right_inv w := by
    ext
    rfl

@[simp]
theorem costarEquivNeighborSet_apply (v : V) (e : Quiver.Costar (vertex G v)) :
    costarEquivNeighborSet G v e =
      ⟨(vertexEquiv G).symm e.1,
        G.mem_neighborSet _ _ |>.mpr (by
          simpa only [vertexEquiv_symm_vertex] using e.2.down.symm)⟩ := (rfl)

@[simp]
theorem costarEquivNeighborSet_symm_apply (v : V) (w : G.neighborSet v) :
    (costarEquivNeighborSet G v).symm w =
      ⟨vertex G w, arrow G w.property.symm⟩ := (rfl)

/-- The number of doubled-quiver arrows from `i` to `j` is the corresponding adjacency-matrix
entry. -/
@[simp]
theorem card_hom_eq_adjMatrix [DecidableRel G.Adj] (i j : V) :
    Fintype.card (vertex G i ⟶ vertex G j) = G.adjMatrix ℕ i j := by
  rw [SimpleGraph.adjMatrix_apply]
  by_cases h : G.Adj i j
  · simp only [h, ite_true]
    exact Fintype.card_eq_one_iff.mpr ⟨arrow G h, fun _ => Subsingleton.elim _ _⟩
  · simp only [h, ite_false]
    exact Fintype.card_eq_zero_iff.mpr (isEmpty_hom_iff G |>.mpr h)

/-- The number of doubled-quiver arrows leaving a vertex is its degree in the graph. -/
theorem card_star_eq_degree [Fintype V] [DecidableRel G.Adj] (v : V) :
    Fintype.card (Quiver.Star (vertex G v)) = G.degree v := by
  rw [Fintype.card_congr (starEquivNeighborSet G v)]
  exact G.card_neighborSet_eq_degree v

/-- The number of doubled-quiver arrows entering a vertex is its degree in the graph. -/
theorem card_costar_eq_degree [Fintype V] [DecidableRel G.Adj] (v : V) :
    Fintype.card (Quiver.Costar (vertex G v)) = G.degree v := by
  rw [Fintype.card_congr (costarEquivNeighborSet G v)]
  exact G.card_neighborSet_eq_degree v

/-- The total number of doubled-quiver arrows is twice the number of graph edges. -/
theorem card_totalArrow_eq_twice_card_edges [Fintype V] [DecidableRel G.Adj] :
    Fintype.card (TotalArrow G) = 2 * G.edgeFinset.card := by
  rw [Fintype.card_congr (totalArrowEquivDart G)]
  exact G.dart_card_eq_twice_card_edges

variable {G}

/-- A graph homomorphism induces a prefunctor of doubled quivers. -/
def map {W : Type v} {H : SimpleGraph W} (f : G →g H) :
    Prefunctor (DoubledQuiver G) (DoubledQuiver H) where
  obj i := vertex H (f ((vertexEquiv G).symm i))
  map e := arrow H (f.map_rel e.down)

@[simp]
theorem map_obj {W : Type v} {H : SimpleGraph W} (f : G →g H) (i : V) :
    (map f).obj (vertex G i) = vertex H (f i) := (rfl)

@[simp]
theorem map_arrow {W : Type v} {H : SimpleGraph W} (f : G →g H)
    {i j : V} (h : G.Adj i j) :
    (map f).map (arrow G h) = Quiver.homOfEq (arrow H (f.map_rel h))
      (map_obj f i).symm (map_obj f j).symm := by
  apply Subsingleton.elim

instance mapMapReverse {W : Type v} {H : SimpleGraph W} (f : G →g H) :
    Prefunctor.MapReverse (map f) where
  map_reverse' _ := Subsingleton.elim _ _

@[simp]
theorem map_id : map (.id : G →g G) = Prefunctor.id (DoubledQuiver G) := by
  refine Prefunctor.ext (fun _ => rfl) ?_
  intro i j e
  apply Subsingleton.elim

theorem map_comp {W : Type v} {X : Type*} {H : SimpleGraph W} {K : SimpleGraph X}
    (f : G →g H) (g : H →g K) :
    map (g.comp f) = map f ⋙q map g := by
  refine Prefunctor.ext (fun _ => rfl) ?_
  intro i j e
  apply Subsingleton.elim

/-- Relabelling a graph and then undoing the relabelling is the identity doubled-quiver map. -/
@[simp]
theorem map_iso_comp_symm {W : Type v} {H : SimpleGraph W} (f : G ≃g H) :
    map f.toHom ⋙q map f.symm.toHom = Prefunctor.id (DoubledQuiver G) := by
  rw [← map_comp, SimpleGraph.Iso.symm_toHom_comp_toHom, map_id]

/-- Undoing a graph relabelling and then applying it is the identity doubled-quiver map. -/
@[simp]
theorem map_symm_comp_iso {W : Type v} {H : SimpleGraph W} (f : G ≃g H) :
    map f.symm.toHom ⋙q map f.toHom = Prefunctor.id (DoubledQuiver H) := by
  rw [← map_comp, SimpleGraph.Iso.toHom_comp_symm_toHom, map_id]

end DoubledQuiver
end TauCeti
