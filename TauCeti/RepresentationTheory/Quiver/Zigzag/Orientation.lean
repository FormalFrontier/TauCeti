/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Basic

/-!
# Orienting a simple graph and recovering its doubled quiver

An orientation of a simple graph chooses exactly one dart over every edge. The chosen darts form a
quiver with one arrow over each edge, and symmetrifying that quiver recovers the doubled quiver of
the graph. This file constructs mutually inverse, reversal-preserving prefunctors which implement
that identification.

The definition keeps the choice of orientation separate from the doubled quiver. In particular,
the comparison does not impose an ordering on the graph's vertices: a linear order merely supplies
one convenient witness that every graph admits an orientation.

## Main definitions

* `TauCeti.DoubledQuiver.Orientation`: a choice of one dart from each reversed pair.
* `TauCeti.DoubledQuiver.Orientation.ofLinearOrder`: orient every edge from its smaller endpoint
  to its larger endpoint.
* `TauCeti.DoubledQuiver.OrientedQuiver`: the quiver of the chosen darts.
* `TauCeti.DoubledQuiver.OrientedQuiver.homEquiv`: its arrows over a pair of graph vertices are
  exactly the adjacency proofs whose dart the orientation selects.
* `TauCeti.DoubledQuiver.symmetrifyMap`: the canonical prefunctor from the symmetrification of an
  oriented graph to its doubled quiver.
* `TauCeti.DoubledQuiver.unsymmetrifyMap`: its inverse prefunctor.

## References

This is the orientation comparison required in Layer 0 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`. It uses Mathlib's universal property
`Quiver.Symmetrify.lift`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u

namespace DoubledQuiver

variable {V : Type u} (G : SimpleGraph V)

/-- An orientation of a simple graph is a set of darts containing exactly one dart over each
edge. The displayed condition says that a reversed dart is chosen exactly when the original dart
is not chosen. -/
structure Orientation where
  /-- The set of darts belonging to the orientation. -/
  carrier : Set G.Dart
  symm_mem_iff_not_mem : ∀ d, d.symm ∈ carrier ↔ d ∉ carrier

namespace Orientation

instance : SetLike (Orientation G) G.Dart where
  coe := Orientation.carrier
  coe_injective := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩ h
    congr

@[ext]
theorem ext {o₁ o₂ : Orientation G} (h : ∀ d, d ∈ o₁ ↔ d ∈ o₂) : o₁ = o₂ := by
  apply SetLike.ext
  exact h

attribute [simp] Orientation.symm_mem_iff_not_mem

/-- A reversed dart is not chosen exactly when the original dart is chosen. -/
@[simp]
theorem symm_notMem_iff_mem (o : Orientation G) (d : G.Dart) : d.symm ∉ o ↔ d ∈ o := by
  constructor
  · intro h
    by_contra hd
    exact h ((o.symm_mem_iff_not_mem d).2 hd)
  · intro hd hs
    exact ((o.symm_mem_iff_not_mem d).1 hs) hd

/-- The orientation induced by a linear order, with each edge directed from its smaller endpoint
to its larger endpoint. -/
def ofLinearOrder [LinearOrder V] : Orientation G where
  carrier := {d | d.fst < d.snd}
  symm_mem_iff_not_mem d := by
    -- `Dart.symm` stores the swapped endpoint pair, which reduces the orientation law to
    -- asymmetry and totality of the chosen linear order.
    change d.snd < d.fst ↔ ¬d.fst < d.snd
    constructor
    · exact fun h h' => (asymm h h')
    · intro h
      exact lt_of_le_of_ne (le_of_not_gt h) d.snd_ne_fst

/-- A dart belongs to the linear-order orientation exactly when its source is smaller than its
target. -/
@[simp]
theorem mem_ofLinearOrder_iff [LinearOrder V] (d : G.Dart) :
    d ∈ ofLinearOrder G ↔ d.fst < d.snd :=
  Iff.rfl

end Orientation

/-- The quiver obtained by retaining only the darts selected by an orientation. -/
@[expose]
def OrientedQuiver (_o : Orientation G) := V

namespace OrientedQuiver

variable (o : Orientation G)

/-- Include a graph vertex into the oriented quiver. -/
def vertex (v : V) : OrientedQuiver G o := v

/-- The graph vertices and the vertices of an oriented quiver are canonically equivalent. -/
def vertexEquiv : V ≃ OrientedQuiver G o where
  toFun := vertex G o
  invFun := fun v => v
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem vertexEquiv_apply (v : V) : vertexEquiv G o v = vertex G o v :=
  (rfl)

@[simp]
theorem vertexEquiv_symm_vertex (v : V) :
    (vertexEquiv G o).symm (vertex G o v) = v := by
  rw [← vertexEquiv_apply]
  exact (vertexEquiv G o).symm_apply_apply v

instance : _root_.Quiver (OrientedQuiver G o) where
  Hom i j := {h : G.Adj ((vertexEquiv G o).symm i) ((vertexEquiv G o).symm j) //
    ⟨((vertexEquiv G o).symm i, (vertexEquiv G o).symm j), h⟩ ∈ o}

instance : Quiver.IsThin (OrientedQuiver G o) := fun _ _ =>
  ⟨fun e f => Subtype.ext (Subsingleton.elim e.1 f.1)⟩

instance [Finite V] : Finite (OrientedQuiver G o) :=
  Finite.of_equiv V (vertexEquiv G o)

instance (i j : OrientedQuiver G o) : Finite (i ⟶ j) :=
  Finite.of_subsingleton

/-- The oriented-quiver arrow corresponding to a chosen dart. -/
def arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    vertex G o i ⟶ vertex G o j :=
  ⟨by simpa only [vertexEquiv_symm_vertex] using h,
    by simpa only [vertexEquiv_symm_vertex] using ho⟩

/-- The arrows of the oriented quiver between two graph vertices are exactly the adjacency proofs
whose dart is selected by the orientation. This is the characteristic description of the quiver
structure, so consumers never need to unfold the `Quiver` instance. -/
def homEquiv (i j : V) :
    (vertex G o i ⟶ vertex G o j) ≃ {h : G.Adj i j // (⟨(i, j), h⟩ : G.Dart) ∈ o} where
  toFun e := ⟨e.1, e.2⟩
  invFun p := arrow G o p.1 p.2
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subtype.ext rfl

/-- The characteristic description of the oriented-quiver arrows reads off the adjacency proof
underlying the arrow of a selected dart. -/
@[simp]
theorem homEquiv_arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    homEquiv G o i j (arrow G o h ho) = ⟨h, ho⟩ :=
  Subtype.ext rfl

/-- The characteristic description of the oriented-quiver arrows sends a selected dart back to its
arrow. -/
@[simp]
theorem homEquiv_symm_apply {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (homEquiv G o i j).symm ⟨h, ho⟩ = arrow G o h ho :=
  Subsingleton.elim _ _

/-- Every arrow of the oriented quiver comes from a dart selected by the orientation. -/
theorem exists_eq_arrow {i j : V} (e : vertex G o i ⟶ vertex G o j) :
    ∃ (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o), e = arrow G o h ho :=
  ⟨(homEquiv G o i j e).1, (homEquiv G o i j e).2, Subsingleton.elim _ _⟩

/-- Forgetting the choice of orientation includes the oriented quiver into the doubled quiver. -/
def forget : OrientedQuiver G o ⥤q DoubledQuiver G where
  obj i := DoubledQuiver.vertexEquiv G ((vertexEquiv G o).symm i)
  map e := Quiver.homOfEq (DoubledQuiver.arrow G e.1)
    (DoubledQuiver.vertexEquiv_apply G _).symm
    (DoubledQuiver.vertexEquiv_apply G _).symm

private theorem forget_obj_eq (i : OrientedQuiver G o) :
    (forget G o).obj i = DoubledQuiver.vertexEquiv G ((vertexEquiv G o).symm i) :=
  (rfl)

@[simp]
theorem forget_obj (i : V) :
    (forget G o).obj (vertex G o i) = DoubledQuiver.vertex G i := by
  simp only [forget_obj_eq, vertexEquiv_symm_vertex, DoubledQuiver.vertexEquiv_apply]

@[simp]
theorem forget_arrow {i j : V} (h : G.Adj i j) (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (forget G o).map (arrow G o h ho) =
      Quiver.homOfEq (DoubledQuiver.arrow G h)
        (forget_obj G o i).symm (forget_obj G o j).symm := by
  apply Subsingleton.elim

end OrientedQuiver

variable (o : Orientation G)

/-- Symmetrifying an oriented graph and forgetting the orientation maps to the doubled quiver. -/
def symmetrifyMap : Symmetrify (OrientedQuiver G o) ⥤q DoubledQuiver G :=
  Symmetrify.lift (OrientedQuiver.forget G o)

@[simp]
theorem symmetrifyMap_obj (i : V) :
    (symmetrifyMap G o).obj (OrientedQuiver.vertex G o i) = DoubledQuiver.vertex G i := by
  exact OrientedQuiver.forget_obj G o i

/-- The comparison sends the positive copy of an oriented arrow to the doubled-quiver arrow of
the selected dart. -/
@[simp]
theorem symmetrifyMap_toPos {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (symmetrifyMap G o).map (Sum.inl (OrientedQuiver.arrow G o h ho)) =
      Quiver.homOfEq (DoubledQuiver.arrow G h)
        (symmetrifyMap_obj G o i).symm (symmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- The comparison sends the negative copy of an oriented arrow to the doubled-quiver arrow of
the reversed dart. -/
@[simp]
theorem symmetrifyMap_toNeg {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (symmetrifyMap G o).map (Sum.inr (OrientedQuiver.arrow G o h ho)) =
      Quiver.homOfEq (DoubledQuiver.arrow G h.symm)
        (symmetrifyMap_obj G o j).symm (symmetrifyMap_obj G o i).symm := by
  apply Subsingleton.elim

/-- The comparison from a symmetrified orientation to the doubled quiver preserves reversal. -/
instance symmetrifyMapMapReverse : Prefunctor.MapReverse (symmetrifyMap G o) where
  map_reverse' e := Symmetrify.lift_reverse _ e

/-- The inverse comparison sends a doubled arrow to the positive copy when its dart was chosen,
and to the negative copy of the oppositely oriented arrow otherwise. -/
noncomputable def unsymmetrifyMap : DoubledQuiver G ⥤q Symmetrify (OrientedQuiver G o) where
  obj i := OrientedQuiver.vertexEquiv G o ((DoubledQuiver.vertexEquiv G).symm i)
  map {i j} e := by
    let d : G.Dart :=
      ⟨((DoubledQuiver.vertexEquiv G).symm i, (DoubledQuiver.vertexEquiv G).symm j), e.down⟩
    by_cases hd : d ∈ o
    · exact Quiver.homOfEq (Sum.inl (OrientedQuiver.arrow G o d.adj hd))
        (OrientedQuiver.vertexEquiv_apply G o _).symm
        (OrientedQuiver.vertexEquiv_apply G o _).symm
    · exact Quiver.homOfEq (Sum.inr (OrientedQuiver.arrow G o d.adj.symm
          ((o.symm_mem_iff_not_mem d).2 hd)))
        (OrientedQuiver.vertexEquiv_apply G o _).symm
        (OrientedQuiver.vertexEquiv_apply G o _).symm

private theorem unsymmetrifyMap_obj_eq (i : DoubledQuiver G) :
    (unsymmetrifyMap G o).obj i =
      OrientedQuiver.vertexEquiv G o ((DoubledQuiver.vertexEquiv G).symm i) :=
  (rfl)

@[simp]
theorem unsymmetrifyMap_obj (i : V) :
    (unsymmetrifyMap G o).obj (DoubledQuiver.vertex G i) =
      OrientedQuiver.vertex G o i := by
  simp only [unsymmetrifyMap_obj_eq, DoubledQuiver.vertexEquiv_symm_vertex,
    OrientedQuiver.vertexEquiv_apply]
  rfl

/-- The symmetrification of an oriented simple graph is thin, as it has exactly one arrow in each
direction over every graph edge. -/
instance instIsThinSymmetrifyOrientedQuiver :
    Quiver.IsThin (Symmetrify (OrientedQuiver G o)) := fun i j => by
  constructor
  intro e f
  cases e with
  | inl e =>
      cases f with
      | inl f => exact congrArg Sum.inl (Subtype.ext (Subsingleton.elim e.1 f.1))
      | inr f =>
          exfalso
          exact ((o.symm_mem_iff_not_mem
            ⟨((OrientedQuiver.vertexEquiv G o).symm i,
              (OrientedQuiver.vertexEquiv G o).symm j), e.1⟩).1 f.2) e.2
  | inr e =>
      cases f with
      | inl f =>
          exfalso
          exact ((o.symm_mem_iff_not_mem
            ⟨((OrientedQuiver.vertexEquiv G o).symm i,
              (OrientedQuiver.vertexEquiv G o).symm j), f.1⟩).1 e.2) f.2
      | inr f => exact congrArg Sum.inr (Subtype.ext (Subsingleton.elim e.1 f.1))

/-- On a chosen dart, the inverse comparison returns the positive copy of the corresponding
oriented-quiver arrow. -/
@[simp]
theorem unsymmetrifyMap_arrow_of_mem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∈ o) :
    (unsymmetrifyMap G o).map (DoubledQuiver.arrow G h) =
      Quiver.homOfEq (Sum.inl (OrientedQuiver.arrow G o h ho))
        (unsymmetrifyMap_obj G o i).symm (unsymmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- On a dart not selected by the orientation, the inverse comparison returns the negative copy
of the oppositely oriented arrow. -/
@[simp]
theorem unsymmetrifyMap_arrow_of_not_mem {i j : V} (h : G.Adj i j)
    (ho : (⟨(i, j), h⟩ : G.Dart) ∉ o) :
    (unsymmetrifyMap G o).map (DoubledQuiver.arrow G h) =
      Quiver.homOfEq
        (Sum.inr (OrientedQuiver.arrow G o h.symm
          ((o.symm_mem_iff_not_mem ⟨(i, j), h⟩).2 ho)))
        (unsymmetrifyMap_obj G o i).symm (unsymmetrifyMap_obj G o j).symm := by
  apply Subsingleton.elim

/-- Forgetting after restoring an orientation is the identity doubled-quiver prefunctor. -/
@[simp]
theorem unsymmetrifyMap_comp_symmetrifyMap :
    unsymmetrifyMap G o ⋙q symmetrifyMap G o = Prefunctor.id (DoubledQuiver G) := by
  refine Prefunctor.ext (fun i => ?_) ?_
  · simp only [Prefunctor.comp_obj, unsymmetrifyMap, symmetrifyMap, Symmetrify.lift,
      OrientedQuiver.forget, Prefunctor.id_obj, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
  intro i j e
  apply Subsingleton.elim

/-- Restoring the orientation after forgetting it is the identity on the symmetrified oriented
quiver. -/
@[simp]
theorem symmetrifyMap_comp_unsymmetrifyMap :
    symmetrifyMap G o ⋙q unsymmetrifyMap G o =
      Prefunctor.id (Symmetrify (OrientedQuiver G o)) := by
  refine Prefunctor.ext (fun i => ?_) ?_
  · simp only [Prefunctor.comp_obj, unsymmetrifyMap, symmetrifyMap, Symmetrify.lift,
      OrientedQuiver.forget, Prefunctor.id_obj, Equiv.symm_apply_apply]
    exact (OrientedQuiver.vertexEquiv G o).apply_symm_apply i
  intro i j e
  apply Subsingleton.elim

/-- The inverse comparison also preserves arrow reversal. -/
instance unsymmetrifyMapMapReverse : Prefunctor.MapReverse (unsymmetrifyMap G o) where
  map_reverse' _ := Subsingleton.elim _ _

end DoubledQuiver
end TauCeti
