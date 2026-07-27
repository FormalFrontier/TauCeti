/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum

/-!
# Finite paths in acyclic quivers

This file proves that a finite quiver with finitely many arrows between any two vertices has only
finitely many paths when it is acyclic. The result supplies the finiteness hypothesis needed for
the finite-dimensionality of its path algebra.

## References

This file implements the `finite_paths_of_isAcyclic` part of Layer 0, “Acyclicity, as a
predicate”, in `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

noncomputable section

/-- Paths of a fixed bounded length are finite when vertices and arrow types are finite. -/
private theorem finite_boundedPaths [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) (a b : V) :
    Finite (_root_.Quiver.Path.BoundedPaths a b n) := by
  induction n generalizing a b with
  | zero => exact Finite.of_subsingleton
  | succ n ih =>
    letI : Fintype V := Fintype.ofFinite V
    letI arrowFintype (x y : V) : Fintype (x ⟶ y) := Fintype.ofFinite _
    letI pathFinite (x y : V) : Finite (_root_.Quiver.Path.BoundedPaths x y n) := ih _ _
    letI pathFintype (x y : V) : Fintype (_root_.Quiver.Path.BoundedPaths x y n) :=
      Fintype.ofFinite _
    letI zeroFintype : Fintype (_root_.Quiver.Path.BoundedPaths a b 0) := Fintype.ofFinite _
    let f : (_root_.Quiver.Path.BoundedPaths a b 0 ⊕
        (Σ c : V, (a ⟶ c) × _root_.Quiver.Path.BoundedPaths c b n)) →
        _root_.Quiver.Path.BoundedPaths a b (n + 1) := fun x ↦
      match x with
      | .inl p => ⟨p.1, p.2.trans (Nat.zero_le _)⟩
      | .inr ⟨c, e, q⟩ =>
        ⟨e.toPath.comp q.1, by simpa [Nat.add_comm] using Nat.add_le_add_right q.2 1⟩
    letI : Finite (_root_.Quiver.Path.BoundedPaths a b 0 ⊕
        (Σ c : V, (a ⟶ c) × _root_.Quiver.Path.BoundedPaths c b n)) :=
      Finite.of_fintype _
    apply Finite.of_surjective f
    intro p
    by_cases hp : p.1.length = 0
    · exact ⟨.inl ⟨p.1, by omega⟩, Subtype.ext rfl⟩
    · obtain ⟨c, e, q, hq, hpq⟩ :=
        p.1.eq_toPath_comp_of_length_eq_succ (n := p.1.length - 1) (by omega)
      have hq_le : q.length ≤ n := by
        have hp_le : p.1.length ≤ n + 1 := p.2
        rw [hq]
        omega
      exact ⟨.inr ⟨c, e, ⟨q, hq_le⟩⟩, Subtype.ext hpq.symm⟩

namespace Quiver.IsAcyclic

/-- Every path in an acyclic finite quiver has length strictly below the number of vertices. -/
theorem length_lt_card (h : Quiver.IsAcyclic V) [Fintype V] {a b : V}
    (p : _root_.Quiver.Path a b) :
    p.length < Fintype.card V := by
  simpa [Nat.lt_iff_add_one_le] using List.Nodup.length_le_card (h.vertices_nodup p)

private theorem finite_paths [Finite V] [∀ a b : V, Finite (a ⟶ b)] (h : Quiver.IsAcyclic V) :
    Finite (Σ a b : V, _root_.Quiver.Path a b) := by
  letI : Fintype V := Fintype.ofFinite V
  letI pathFinite (a b : V) : Finite (_root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    finite_boundedPaths _ _ _
  letI pathFintype (a b : V) : Fintype (_root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    Fintype.ofFinite _
  let f : (Σ a b : V, _root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) →
      Σ a b : V, _root_.Quiver.Path a b :=
    fun p ↦ ⟨p.1, p.2.1, p.2.2.1⟩
  letI : Finite (Σ a b : V, _root_.Quiver.Path.BoundedPaths a b (Fintype.card V - 1)) :=
    Finite.of_fintype _
  apply Finite.of_surjective f
  rintro ⟨a, b, p⟩
  refine ⟨⟨a, b, p, ?_⟩, rfl⟩
  have hp := h.length_lt_card p
  omega

end Quiver.IsAcyclic

/-- A finite acyclic quiver with finite arrow types has finitely many paths. -/
theorem finite_paths_of_isAcyclic [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (h : Quiver.IsAcyclic V) : Finite (Σ a b : V, _root_.Quiver.Path a b) :=
  h.finite_paths

end

end TauCeti
