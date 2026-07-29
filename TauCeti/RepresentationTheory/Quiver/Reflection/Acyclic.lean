/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths
public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic

/-!
# Acyclic reflected quivers

This file develops the interaction between acyclicity and reflection at a sink or source. A
nonempty finite acyclic quiver has a sink and a source, and reflecting at a sink preserves
acyclicity.

## Main results

* `TauCeti.Quiver.IsAcyclic.exists_isSink`: a nonempty finite acyclic quiver has a sink.
* `TauCeti.Quiver.IsAcyclic.exists_isSource`: a nonempty finite acyclic quiver has a source.
* `TauCeti.Quiver.IsAcyclic.reflect_of_isSink`: reflecting an acyclic quiver at a sink leaves it
  acyclic.

## References

These results support the sink-admissible reflection-functor constructions in Layers 4 and 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V]

namespace Quiver

/-- A nonempty finite acyclic quiver has a sink: were every vertex to carry an outgoing arrow,
paths could be extended indefinitely, past the bound of
`TauCeti.Quiver.IsAcyclic.length_lt_card`. -/
theorem IsAcyclic.exists_isSink [Finite V] [Nonempty V] (h : IsAcyclic V) :
    ∃ i : V, IsSink i := by
  letI : Fintype V := Fintype.ofFinite V
  by_contra hcon
  have hout : ∀ i : V, ∃ b : V, Nonempty (i ⟶ b) := fun i ↦ by
    by_contra hi
    exact hcon ⟨i, IsSink_def i |>.mpr fun b ↦ not_nonempty_iff.mp fun hb ↦ hi ⟨b, hb⟩⟩
  have hlong : ∀ n : ℕ, ∃ (a b : V) (p : Path a b), p.length = n := by
    intro n
    induction n with
    | zero => exact ⟨Classical.arbitrary V, _, Path.nil, Path.length_nil⟩
    | succ n ih =>
      obtain ⟨a, b, p, hp⟩ := ih
      obtain ⟨c, ⟨e⟩⟩ := hout b
      exact ⟨a, c, p.cons e, by rw [Path.length_cons, hp]⟩
  obtain ⟨a, b, p, hp⟩ := hlong (Fintype.card V)
  have := h.length_lt_card p
  omega

/-- A nonempty finite acyclic quiver has a source. -/
theorem IsAcyclic.exists_isSource [Finite V] [Nonempty V] (h : IsAcyclic V) :
    ∃ i : V, IsSource i := by
  letI : Fintype V := Fintype.ofFinite V
  by_contra hcon
  have hin : ∀ i : V, ∃ a : V, Nonempty (a ⟶ i) := fun i ↦ by
    by_contra hi
    exact hcon ⟨i, IsSource_def i |>.mpr fun a ↦ not_nonempty_iff.mp fun ha ↦ hi ⟨a, ha⟩⟩
  have hlong : ∀ n : ℕ, ∃ (a b : V) (p : Path a b), p.length = n := by
    intro n
    induction n with
    | zero => exact ⟨Classical.arbitrary V, _, Path.nil, Path.length_nil⟩
    | succ n ih =>
      obtain ⟨a, b, p, hp⟩ := ih
      obtain ⟨c, ⟨e⟩⟩ := hin a
      refine ⟨c, b, e.toPath.comp p, ?_⟩
      rw [Path.length_comp, Path.length_toPath, hp]
      omega
  obtain ⟨a, b, p, hp⟩ := hlong (Fintype.card V)
  have := h.length_lt_card p
  omega

/-- Away from a sink, a path of the reflected quiver comes from a path of the original quiver of
the same length; in particular it cannot reach the sink. -/
private theorem exists_path_of_isSink {i : V} (h : IsSink i) {a b : Reflect V i} (ha : a ≠ i)
    (p : Path a b) : b ≠ i ∧ ∃ q : @Path V _ a b, q.length = p.length := by
  induction p with
  | nil => exact ⟨ha, Path.nil, rfl⟩
  | @cons c d p e ih =>
    obtain ⟨hc, q, hq⟩ := ih
    by_cases hd : d = i
    · exact (h.isSource_reflect.isEmpty_hom c).elim (hd ▸ e)
    · refine ⟨hd, q.cons (cast (reflectHom_of_ne_of_ne hc hd) (cast (hom_reflect i c d) e)), ?_⟩
      rw [Path.length_cons, Path.length_cons, hq]

/-- Reflecting an acyclic quiver at a sink leaves it acyclic. -/
theorem IsAcyclic.reflect_of_isSink {i : V} (hV : IsAcyclic V) (h : IsSink i) :
    IsAcyclic (Reflect V i) := by
  rw [isAcyclic_def]
  intro a p
  refine p.eq_nil_of_length_zero ?_
  by_cases ha : a = i
  · cases p with
    | nil => exact Path.length_nil
    | cons _ e => exact (h.isSource_reflect.isEmpty_hom _).elim (ha ▸ e)
  · obtain ⟨-, q, hq⟩ := exists_path_of_isSink h ha p
    rw [← hq, hV.length_eq_zero q]

end Quiver

end TauCeti
