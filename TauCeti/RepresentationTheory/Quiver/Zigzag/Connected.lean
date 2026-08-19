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

* `TauCeti.DoubledQuiver.pathToWalk_walkToPath` and `TauCeti.DoubledQuiver.walkToPath_pathToWalk`:
  the two conversions are mutually inverse.
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

/-- Converting the one-edge walk gives the corresponding doubled-quiver arrow. -/
theorem walkToPath_toWalk {i j : V} (h : G.Adj i j) :
    walkToPath G h.toWalk = (arrow G h).toPath := by
  simp [SimpleGraph.Adj.toWalk]

/-- Converting the empty doubled-quiver path gives the empty graph walk. -/
@[simp]
theorem pathToWalk_nil (i : V) :
    pathToWalk G (Quiver.Path.nil : Quiver.Path (vertex G i) (vertex G i)) =
      (SimpleGraph.Walk.nil : G.Walk i i) := by
  unfold pathToWalk
  simp [pathToWalkAux]

private theorem pathToWalkAux_comp {i j k : DoubledQuiver G} (p : Quiver.Path i j)
    (q : Quiver.Path j k) :
    pathToWalkAux G (p.comp q) = (pathToWalkAux G p).append (pathToWalkAux G q) := by
  induction q with
  | nil => simp [pathToWalkAux]
  | cons q e ih => simp [pathToWalkAux, ih, SimpleGraph.Walk.append_assoc]

/-- Converting composite doubled-quiver paths gives the appended graph walks. -/
@[simp]
theorem pathToWalk_comp {i j k : V} (p : Quiver.Path (vertex G i) (vertex G j))
    (q : Quiver.Path (vertex G j) (vertex G k)) :
    pathToWalk G (p.comp q) = (pathToWalk G p).append (pathToWalk G q) := by
  unfold pathToWalk
  rw [pathToWalkAux_comp, ← SimpleGraph.Walk.append_copy_copy]

private theorem copy_toWalk {a b a' b' : V} (h : G.Adj a b) (h' : G.Adj a' b') (ha : a = a')
    (hb : b = b') : h.toWalk.copy ha hb = h'.toWalk := by
  subst ha
  subst hb
  rfl

private theorem pathToWalkAux_toPath {i j : DoubledQuiver G} (e : i ⟶ j) :
    pathToWalkAux G e.toPath = e.down.toWalk := by
  simp [pathToWalkAux, Quiver.Hom.toPath]

/-- Converting the one-arrow doubled-quiver path gives the one-edge graph walk. -/
@[simp]
theorem pathToWalk_toPath {i j : V} (h : G.Adj i j) :
    pathToWalk G (arrow G h).toPath = h.toWalk := by
  unfold pathToWalk
  rw [pathToWalkAux_toPath]
  exact copy_toWalk G _ h _ _

/-- Turning a graph walk into a doubled-quiver path and back gives the original walk. -/
@[simp]
theorem pathToWalk_walkToPath {i j : V} (p : G.Walk i j) : pathToWalk G (walkToPath G p) = p := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, SimpleGraph.Adj.toWalk]

private theorem toList_walkToPath_copy {a b a' b' : V} (p : G.Walk a b) (ha : a = a')
    (hb : b = b') : (walkToPath G (p.copy ha hb)).toList = (walkToPath G p).toList := by
  subst ha
  subst hb
  rfl

private theorem toList_walkToPath_pathToWalkAux {i j : DoubledQuiver G} (p : Quiver.Path i j) :
    (walkToPath G (pathToWalkAux G p)).toList = p.toList := by
  induction p with
  | nil => rfl
  | cons p e ih => simp [pathToWalkAux, ih, Quiver.Hom.toPath]

/-- Turning a doubled-quiver path into a graph walk and back gives the original path. -/
@[simp]
theorem walkToPath_pathToWalk {i j : V} (p : Quiver.Path (vertex G i) (vertex G j)) :
    walkToPath G (pathToWalk G p) = p :=
  Quiver.Path.toList_injective _ _ <| by
    unfold pathToWalk
    rw [toList_walkToPath_copy, toList_walkToPath_pathToWalkAux]

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

/-- Reachability of two doubled-quiver vertices is graph reachability of the vertices they come
from. -/
theorem reachable_vertexEquiv_symm_iff (i j : DoubledQuiver G) :
    G.Reachable ((vertexEquiv G).symm i) ((vertexEquiv G).symm j) ↔ Quiver.Reachable i j := by
  simpa only [vertexEquiv_symm_apply] using
    reachable_iff G (i := (vertexEquiv G).symm i) (j := (vertexEquiv G).symm j)

/-- Two doubled-quiver vertices have the same weakly connected component exactly when the graph
vertices they come from are reachable. -/
theorem weaklyConnectedComponent_eq_iff (i j : DoubledQuiver G) :
    (i : Quiver.WeaklyConnectedComponent (DoubledQuiver G)) = j ↔
      G.Reachable ((vertexEquiv G).symm i) ((vertexEquiv G).symm j) := by
  rw [Quiver.WeaklyConnectedComponent.eq]
  simpa only [vertexEquiv_symm_apply] using
    (reachable_iff_nonempty_symmetrify_path G (i := (vertexEquiv G).symm i)
      (j := (vertexEquiv G).symm j)).symm

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
      (weaklyConnectedComponent_eq_iff G i j).1 (Quotient.sound h)
  left_inv := by
    apply SimpleGraph.ConnectedComponent.ind
    intro i
    exact congr_arg G.connectedComponentMk (vertexEquiv_symm_vertex G i)
  right_inv := by
    apply Quotient.ind'
    intro i
    refine (weaklyConnectedComponent_eq_iff G _ i).2 ?_
    simpa only [vertexEquiv_symm_vertex] using SimpleGraph.Reachable.refl _

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
    exact ((reachable_vertexEquiv_symm_iff G i j).1 (h _ _)).elim fun p => ⟨p⟩
  · intro h i j
    exact (reachable_iff G).2 ((h (vertex G i) (vertex G j)).elim Quiver.Path.reachable)

/-- A graph is connected exactly when its doubled quiver is nonempty and strongly connected. -/
theorem connected_iff :
    G.Connected ↔ Nonempty (DoubledQuiver G) ∧ Quiver.IsStronglyConnected (DoubledQuiver G) := by
  rw [SimpleGraph.connected_iff, preconnected_iff_isStronglyConnected]
  exact and_comm

end DoubledQuiver
end TauCeti
