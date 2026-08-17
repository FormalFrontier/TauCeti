/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basic
public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected components of doubled graph quivers

Graph walks become directed paths in the doubled quiver by replacing each traversed edge with its
corresponding arrow. Conversely, a doubled-quiver path gives a graph walk by forgetting the lifted
adjacency proofs. These constructions identify graph reachability with directed reachability in the
doubled quiver and with zigzag reachability in its symmetrification.

It follows that the connected components of a graph are canonically equivalent to the weakly
connected components of its doubled quiver. This is the component bridge used by the componentwise
definition and decomposition of zigzag algebras.

## Main definitions

* `TauCeti.DoubledQuiver.walkToPath`: turn a graph walk into a doubled-quiver path.
* `TauCeti.DoubledQuiver.pathToWalk`: turn a doubled-quiver path into a graph walk.
* `TauCeti.DoubledQuiver.connectedComponentEquiv`: identify the two component types.

## Main results

* `TauCeti.DoubledQuiver.reachable_iff`: graph and doubled-quiver reachability agree.
* `TauCeti.DoubledQuiver.preconnected_iff_isStronglyConnected`: graph preconnectedness is strong
  connectivity of the doubled quiver.
* `TauCeti.DoubledQuiver.connected_iff`: graph connectedness is nonemptiness together with strong
  connectivity of the doubled quiver.

## References

This is the connected-component compatibility required in Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. See Huerfano--Khovanov,
*A category for the adjoint representation*, Section 3.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-- Convert a graph walk to the path through the corresponding arrows of the doubled quiver. -/
def walkToPath {i j : V} : G.Walk i j → Quiver.Path (vertex G i) (vertex G j)
  | .nil => .nil
  | .cons h p => (arrow G h).toPath.comp (walkToPath p)

/-- Convert a path in the doubled quiver to the graph walk with the same successive vertices. -/
private def pathToWalkAux {i j : DoubledQuiver G} : Quiver.Path i j →
    G.Walk ((vertexEquiv G).symm i) ((vertexEquiv G).symm j)
  | .nil => .nil
  | .cons p e => (pathToWalkAux p).append e.down.toWalk

/-- Convert a path in the doubled quiver between graph-labelled vertices to a graph walk. -/
def pathToWalk {i j : V} (p : Quiver.Path (vertex G i) (vertex G j)) : G.Walk i j := by
  exact (pathToWalkAux G p).copy
    (vertexEquiv_symm_vertex G i) (vertexEquiv_symm_vertex G j)

@[simp]
theorem walkToPath_nil (i : V) :
    walkToPath G (SimpleGraph.Walk.nil : G.Walk i i) = Quiver.Path.nil := (rfl)

@[simp]
theorem walkToPath_cons {i j k : V} (h : G.Adj i j) (p : G.Walk j k) :
    walkToPath G (.cons h p) = (arrow G h).toPath.comp (walkToPath G p) := (rfl)

/-- Converting appended graph walks gives the composite doubled-quiver paths. -/
@[simp]
theorem walkToPath_append {i j k : V} (p : G.Walk i j) (q : G.Walk j k) :
    walkToPath G (p.append q) = (walkToPath G p).comp (walkToPath G q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, Quiver.Path.comp_assoc]

@[simp]
theorem walkToPath_toWalk {i j : V} (h : G.Adj i j) :
    walkToPath G h.toWalk = (arrow G h).toPath := by
  simp [SimpleGraph.Adj.toWalk]

/-- Turning a graph walk into a doubled-quiver path preserves its length. -/
@[simp]
theorem length_walkToPath {i j : V} (p : G.Walk i j) :
    (walkToPath G p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ih, Nat.add_comm]

private theorem length_pathToWalkAux {i j : DoubledQuiver G} (p : Quiver.Path i j) :
    (pathToWalkAux G p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [pathToWalkAux, ih]

/-- Turning a doubled-quiver path into a graph walk preserves its length. -/
@[simp]
theorem length_pathToWalk {i j : V} (p : Quiver.Path (vertex G i) (vertex G j)) :
    (pathToWalk G p).length = p.length := by
  unfold pathToWalk
  rw [SimpleGraph.Walk.length_copy, length_pathToWalkAux]

/-- Graph reachability is directed reachability in the doubled quiver. -/
@[simp]
theorem reachable_iff {i j : V} :
    G.Reachable i j ↔ Quiver.Reachable (vertex G i) (vertex G j) := by
  constructor
  · rintro ⟨p⟩
    exact ⟨walkToPath G p⟩
  · rintro ⟨p⟩
    exact ⟨pathToWalk G p⟩

/-- Graph reachability is zigzag reachability in the doubled quiver. -/
@[simp]
theorem reachable_iff_nonempty_symmetrify_path {i j : V} :
    G.Reachable i j ↔
      Nonempty (@Quiver.Path (Quiver.Symmetrify (DoubledQuiver G)) _
        (vertex G i) (vertex G j)) := by
  rw [reachable_iff G]
  constructor
  · rintro ⟨p⟩
    exact ⟨Quiver.Symmetrify.of.mapPath p⟩
  · rintro ⟨p⟩
    exact ⟨(Quiver.Symmetrify.lift (Prefunctor.id (DoubledQuiver G))).mapPath p⟩

/-- The connected components of a graph are the weakly connected components of its doubled
quiver. -/
def connectedComponentEquiv :
    G.ConnectedComponent ≃ Quiver.WeaklyConnectedComponent (DoubledQuiver G) where
  toFun := Quot.lift (fun i => (vertex G i : Quiver.WeaklyConnectedComponent (DoubledQuiver G)))
    fun _ _ h => (Quiver.WeaklyConnectedComponent.eq _ _).2
      ((reachable_iff_nonempty_symmetrify_path G).1 h)
  invFun := Quotient.lift
    (fun i => G.connectedComponentMk ((vertexEquiv G).symm i))
    fun i j h => SimpleGraph.ConnectedComponent.sound <|
      (reachable_iff_nonempty_symmetrify_path G).2 <| by
        change Nonempty (@Quiver.Path (Quiver.Symmetrify (DoubledQuiver G)) _ i j) at h
        simpa only [vertexEquiv_symm_apply] using h
  left_inv := by
    apply SimpleGraph.ConnectedComponent.ind
    intro i
    exact congr_arg G.connectedComponentMk (vertexEquiv_symm_vertex G i)
  right_inv := by
    apply Quotient.ind'
    intro i
    apply (Quiver.WeaklyConnectedComponent.eq _ _).2
    simpa only [vertexEquiv_symm_apply] using
      (Nonempty.intro (Quiver.Path.nil :
        @Quiver.Path (Quiver.Symmetrify (DoubledQuiver G)) _ i i))

@[simp]
theorem connectedComponentEquiv_mk (i : V) :
    connectedComponentEquiv G (G.connectedComponentMk i) =
      (vertex G i : Quiver.WeaklyConnectedComponent (DoubledQuiver G)) := (rfl)

@[simp]
theorem connectedComponentEquiv_symm_mk (i : DoubledQuiver G) :
    (connectedComponentEquiv G).symm (i : Quiver.WeaklyConnectedComponent (DoubledQuiver G)) =
      G.connectedComponentMk ((vertexEquiv G).symm i) := (rfl)

/-- A graph is preconnected exactly when its doubled quiver is strongly connected. -/
theorem preconnected_iff_isStronglyConnected :
    G.Preconnected ↔ Quiver.IsStronglyConnected (DoubledQuiver G) := by
  constructor
  · intro h i j
    change Quiver.Reachable i j
    simpa only [vertexEquiv_symm_apply] using
      (reachable_iff G).1 (h ((vertexEquiv G).symm i) ((vertexEquiv G).symm j))
  · intro h i j
    exact (reachable_iff G).2 (h (vertex G i) (vertex G j))

/-- A graph is connected exactly when its doubled quiver is nonempty and strongly connected. -/
theorem connected_iff :
    G.Connected ↔ Nonempty (DoubledQuiver G) ∧ Quiver.IsStronglyConnected (DoubledQuiver G) := by
  rw [SimpleGraph.connected_iff, preconnected_iff_isStronglyConnected]
  exact and_comm

end DoubledQuiver
end TauCeti
