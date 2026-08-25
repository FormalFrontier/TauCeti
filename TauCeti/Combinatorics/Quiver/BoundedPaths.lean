/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finitely many paths of bounded length

A quiver with finitely many vertices and finitely many arrows between any two of them has only
finitely many paths of any given length, because a path of length at most `n` is a list of at most
`n` arrows. No acyclicity is involved: the bound on the length is what makes the count finite,
and an acyclic quiver is exactly one where such a bound is automatic.

## Main results

* `TauCeti.Quiver.finite_boundedPaths`: `Quiver.Path.BoundedPaths a b n`, the paths from `a` to `b`
  of length at most `n`, is a finite type.
* `TauCeti.Quiver.finite_setOf_length_le` and `TauCeti.Quiver.finite_setOf_length_lt`: the paths of
  bounded length form a finite set of the total path space `Σ a b, Quiver.Path a b`.

## References

The unbounded consequence for an acyclic quiver, `TauCeti.finite_paths_of_isAcyclic`, is in
`TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths`; it is the `finite_paths_of_isAcyclic`
target of Layer 0 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`. The bounded count here is
what the finite dimensionality of a bound quiver algebra rests on
(`TauCeti.RepresentationTheory.Quiver.AdmissibleIdeal`), where no such bound is automatic.
-/

public section

namespace TauCeti

universe u v

namespace Quiver

variable {V : Type u} [_root_.Quiver.{v} V]

/-- **Paths of bounded length are finite** when there are finitely many vertices and finitely many
arrows between any two of them: a path of length at most `n + 1` is either trivial or an arrow
followed by a path of length at most `n`. -/
theorem finite_boundedPaths [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) (a b : V) :
    Finite (_root_.Quiver.Path.BoundedPaths a b n) := by
  induction n generalizing a b with
  | zero => exact Finite.of_subsingleton
  | succ n ih =>
    let : Fintype V := Fintype.ofFinite V
    let arrowFintype (x y : V) : Fintype (x ⟶ y) := Fintype.ofFinite _
    let pathFinite (x y : V) : Finite (_root_.Quiver.Path.BoundedPaths x y n) := ih _ _
    let pathFintype (x y : V) : Fintype (_root_.Quiver.Path.BoundedPaths x y n) :=
      Fintype.ofFinite _
    let zeroFintype : Fintype (_root_.Quiver.Path.BoundedPaths a b 0) := Fintype.ofFinite _
    let f : (_root_.Quiver.Path.BoundedPaths a b 0 ⊕
        (Σ c : V, (a ⟶ c) × _root_.Quiver.Path.BoundedPaths c b n)) →
        _root_.Quiver.Path.BoundedPaths a b (n + 1) := fun x ↦
      match x with
      | .inl p => ⟨p.1, p.2.trans (Nat.zero_le _)⟩
      | .inr ⟨c, e, q⟩ =>
        ⟨e.toPath.comp q.1, by simpa [Nat.add_comm] using Nat.add_le_add_right q.2 1⟩
    let : Finite (_root_.Quiver.Path.BoundedPaths a b 0 ⊕
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

/-- **The paths of length at most `n` are a finite subset of the total path space.** -/
theorem finite_setOf_length_le [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) :
    {x : Σ a b : V, _root_.Quiver.Path a b | x.2.2.length ≤ n}.Finite := by
  let : Fintype V := Fintype.ofFinite V
  let pathFinite (a b : V) : Finite (_root_.Quiver.Path.BoundedPaths a b n) :=
    finite_boundedPaths n a b
  let pathFintype (a b : V) : Fintype (_root_.Quiver.Path.BoundedPaths a b n) :=
    Fintype.ofFinite _
  let : Finite (Σ a b : V, _root_.Quiver.Path.BoundedPaths a b n) := Finite.of_fintype _
  rw [← Set.finite_coe_iff]
  refine Finite.of_surjective
    (fun p : Σ a b : V, _root_.Quiver.Path.BoundedPaths a b n =>
      (⟨⟨p.1, p.2.1, p.2.2.1⟩, p.2.2.2⟩ :
        {x : Σ a b : V, _root_.Quiver.Path a b | x.2.2.length ≤ n})) ?_
  rintro ⟨⟨a, b, p⟩, hp⟩
  exact ⟨⟨a, b, ⟨p, hp⟩⟩, rfl⟩

/-- **The paths of length less than `n` are a finite subset of the total path space.** -/
theorem finite_setOf_length_lt [Finite V] [∀ a b : V, Finite (a ⟶ b)] (n : ℕ) :
    {x : Σ a b : V, _root_.Quiver.Path a b | x.2.2.length < n}.Finite :=
  (finite_setOf_length_le n).subset fun _ hx => Nat.le_of_lt hx

end Quiver

end TauCeti
