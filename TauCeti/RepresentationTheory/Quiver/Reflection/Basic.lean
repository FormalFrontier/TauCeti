/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fintype.Card

/-!
# Sinks, sources, and the reflection of a quiver at a vertex

Reflecting a quiver `V` at a vertex `i` reverses every arrow incident to `i` and leaves the
remaining arrows alone. This is the change of orientation underlying the
Bernstein-Gelfand-Ponomarev reflection functors, which carry representations of `V` to
representations of the reflected quiver.

The reflected quiver is `TauCeti.Quiver.Reflect V i`, a type synonym for the vertex type `V`
carrying the reversed arrows; its arrow types are computed by `TauCeti.Quiver.reflectHom`.
Reflection is applied at a **sink** (a vertex with no outgoing arrow) or, dually, at a **source**,
and it exchanges the two: reflecting at a sink turns it into a source
(`TauCeti.Quiver.IsSink.isSource_reflect`). Preservation of acyclicity and the existence of sinks
and sources in finite acyclic quivers are proved in
`TauCeti.RepresentationTheory.Quiver.Reflection.Acyclic`.

## Main definitions

* `TauCeti.Quiver.IsSink`, `TauCeti.Quiver.IsSource`: a vertex with no outgoing, respectively no
  incoming, arrow.
* `TauCeti.Quiver.reflectHom`: the arrow types of the quiver obtained by reversing every arrow
  incident to a given vertex.
* `TauCeti.Quiver.Reflect`: that quiver, on the same vertex type.

## Main results

* `TauCeti.Quiver.IsSink.isSource_reflect`: reflecting at a sink turns it into a source.
* `TauCeti.Quiver.hom_reflect_reflect`: reflecting twice at the same vertex restores the original
  arrows, so reflection at a vertex is an involution.

## References

This file supplies the reflected quiver `Q.reflect i` that the reflection functors of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` map into. See
Derksen--Weyman, *An Introduction to Quiver Representations*, and
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u} [_root_.Quiver.{v} V]

/-! ### Sinks and sources -/

/-- A vertex of a quiver is a *sink* if no arrow leaves it. -/
def Quiver.IsSink (i : V) : Prop :=
  ∀ b : V, IsEmpty (i ⟶ b)

/-- A vertex of a quiver is a *source* if no arrow enters it. -/
def Quiver.IsSource (i : V) : Prop :=
  ∀ a : V, IsEmpty (a ⟶ i)

namespace Quiver

/-- The defining condition for a sink. -/
theorem IsSink_def (i : V) : IsSink i ↔ ∀ b : V, IsEmpty (i ⟶ b) :=
  Iff.rfl

/-- The defining condition for a source. -/
theorem IsSource_def (i : V) : IsSource i ↔ ∀ a : V, IsEmpty (a ⟶ i) :=
  Iff.rfl

/-- No arrow leaves a sink. -/
theorem IsSink.isEmpty_hom {i : V} (h : IsSink i) (b : V) : IsEmpty (i ⟶ b) :=
  (IsSink_def i).mp h b

/-- No arrow enters a source. -/
theorem IsSource.isEmpty_hom {i : V} (h : IsSource i) (a : V) : IsEmpty (a ⟶ i) :=
  (IsSource_def i).mp h a

/-- A sink carries no loop. -/
theorem IsSink.isEmpty_hom_self {i : V} (h : IsSink i) : IsEmpty (i ⟶ i) :=
  h.isEmpty_hom i

/-- A source carries no loop. -/
theorem IsSource.isEmpty_hom_self {i : V} (h : IsSource i) : IsEmpty (i ⟶ i) :=
  h.isEmpty_hom i

/-- A path out of a sink is trivial, so it ends where it started. -/
theorem IsSink.eq_of_path {i b : V} (h : IsSink i) (p : Path i b) : i = b := by
  induction p with
  | nil => rfl
  | cons _ e ih => subst ih; exact (h.isEmpty_hom _).elim e

/-- A path into a source is trivial, so it starts where it ends. -/
theorem IsSource.eq_of_path {i a : V} (h : IsSource i) (p : Path a i) : a = i := by
  cases p with
  | nil => rfl
  | cons _ e => exact (h.isEmpty_hom _).elim e

/-! ### The arrows of the reflected quiver -/

/-- The arrows from `a` to `b` in the quiver obtained from `V` by reversing every arrow incident
to the vertex `i`. Arrows between two vertices other than `i` are untouched, an arrow `b ⟶ i`
becomes an arrow `i ⟶ b`, and the loops at `i` are reversed among themselves. -/
noncomputable def reflectHom (i a b : V) : Type v :=
  letI := Classical.decEq V
  if a = i then (if b = i then (i ⟶ i) else (b ⟶ i))
  else (if b = i then (i ⟶ a) else (a ⟶ b))

/-- The arrows out of `i` in the reflected quiver are the arrows into `i` in the original one. -/
@[simp]
theorem reflectHom_left (i b : V) : reflectHom i i b = (b ⟶ i) := by
  rcases eq_or_ne b i with rfl | hb
  · simp [reflectHom]
  · simp [reflectHom, hb]

/-- The arrows into `i` in the reflected quiver are the arrows out of `i` in the original one. -/
@[simp]
theorem reflectHom_right (i a : V) : reflectHom i a i = (i ⟶ a) := by
  rcases eq_or_ne a i with rfl | ha
  · simp [reflectHom]
  · simp [reflectHom, ha]

/-- Away from `i` the reflected quiver has the arrows of the original one. -/
@[simp]
theorem reflectHom_of_ne_of_ne {i a b : V} (ha : a ≠ i) (hb : b ≠ i) :
    reflectHom i a b = (a ⟶ b) := by
  simp [reflectHom, ha, hb]

noncomputable instance instFintypeReflectHom [∀ a b : V, Fintype (a ⟶ b)] (i a b : V) :
    Fintype (reflectHom i a b) := by
  by_cases ha : a = i
  · subst a
    rw [reflectHom_left]
    infer_instance
  · by_cases hb : b = i
    · subst b
      rw [reflectHom_right]
      infer_instance
    · rw [reflectHom_of_ne_of_ne ha hb]
      infer_instance

/-! ### The reflected quiver -/

/-- The reflection of a quiver at a vertex `i`: a type synonym for the vertex type, carrying the
quiver in which every arrow incident to `i` is reversed. -/
@[expose] def Reflect (V : Type u) (_i : V) : Type u := V

noncomputable instance reflectQuiver (i : V) : _root_.Quiver.{v} (Reflect V i) :=
  ⟨fun a b : V ↦ reflectHom i a b⟩

instance (i : V) [DecidableEq V] : DecidableEq (Reflect V i) :=
  inferInstanceAs (DecidableEq V)

instance (i : V) [Fintype V] : Fintype (Reflect V i) :=
  inferInstanceAs (Fintype V)

instance (i : V) [Nonempty V] : Nonempty (Reflect V i) :=
  inferInstanceAs (Nonempty V)

noncomputable instance (i : V) [∀ a b : V, Fintype (a ⟶ b)] (a b : Reflect V i) :
    Fintype (a ⟶ b) :=
  instFintypeReflectHom i a b

/-- The arrow types of the reflected quiver are the ones computed by
`TauCeti.Quiver.reflectHom`. -/
@[simp]
theorem hom_reflect (i : V) (a b : Reflect V i) : (a ⟶ b) = reflectHom i a b :=
  rfl

/-- Reflecting at a sink turns it into a source: no arrow of the reflected quiver enters `i`. -/
theorem IsSink.isSource_reflect {i : V} (h : IsSink i) : @IsSource (Reflect V i) _ i :=
  (@IsSource_def (Reflect V i) _ i).mpr fun a ↦
    ⟨fun e ↦ (h.isEmpty_hom a).elim (cast ((hom_reflect i a i).trans (reflectHom_right i a)) e)⟩

/-- Reflecting at a source turns it into a sink: no arrow of the reflected quiver leaves `i`. -/
theorem IsSource.isSink_reflect {i : V} (h : IsSource i) : @IsSink (Reflect V i) _ i :=
  (@IsSink_def (Reflect V i) _ i).mpr fun b ↦
    ⟨fun e ↦ (h.isEmpty_hom b).elim (cast ((hom_reflect i i b).trans (reflectHom_left i b)) e)⟩

/-- Reflecting twice at the same vertex restores the original arrow types: reflection at a vertex
is an involution on quivers. -/
theorem hom_reflect_reflect (i a b : V) :
    @_root_.Quiver.Hom (Reflect (Reflect V i) i) _ a b = (a ⟶ b) := by
  rw [@hom_reflect (Reflect V i) _ i a b]
  rcases eq_or_ne a i with rfl | ha
  · simp
  · rcases eq_or_ne b i with rfl | hb
    · simp
    · rw [@reflectHom_of_ne_of_ne (Reflect V i) _ i a b ha hb, hom_reflect,
        reflectHom_of_ne_of_ne ha hb]

/-! ### Arrow counts in the reflected quiver -/

variable [∀ a b : V, Fintype (a ⟶ b)]

/-- The reflected quiver has as many arrows `i ⟶ b` as the original has arrows `b ⟶ i`. -/
theorem card_reflectHom_left (i b : V) :
    Fintype.card (reflectHom i i b) = Fintype.card (b ⟶ i) :=
  Fintype.card_congr' (reflectHom_left i b)

/-- The reflected quiver has as many arrows `a ⟶ i` as the original has arrows `i ⟶ a`. -/
theorem card_reflectHom_right (i a : V) :
    Fintype.card (reflectHom i a i) = Fintype.card (i ⟶ a) :=
  Fintype.card_congr' (reflectHom_right i a)

/-- Away from `i` the reflected quiver has the same arrow counts as the original. -/
theorem card_reflectHom_of_ne_of_ne {i a b : V} (ha : a ≠ i) (hb : b ≠ i) :
    Fintype.card (reflectHom i a b) = Fintype.card (a ⟶ b) :=
  Fintype.card_congr' (reflectHom_of_ne_of_ne ha hb)

/-- Reflection at a vertex preserves the number of arrows joining any two vertices in either
direction: it changes the orientation of the quiver, not its underlying graph. -/
theorem card_reflectHom_add_swap (i a b : V) :
    Fintype.card (reflectHom i a b) + Fintype.card (reflectHom i b a)
      = Fintype.card (a ⟶ b) + Fintype.card (b ⟶ a) := by
  by_cases ha : a = i
  · rw [ha, card_reflectHom_left, card_reflectHom_right]
    omega
  · by_cases hb : b = i
    · rw [hb, card_reflectHom_right, card_reflectHom_left]
      omega
    · rw [card_reflectHom_of_ne_of_ne ha hb, card_reflectHom_of_ne_of_ne hb ha]

/-- Reflecting at a sink leaves no arrow into `i`. -/
theorem card_reflectHom_right_of_isSink {i : V} (h : IsSink i) (a : V) :
    Fintype.card (reflectHom i a i) = 0 := by
  rw [card_reflectHom_right, Fintype.card_eq_zero_iff]
  exact h.isEmpty_hom a

end Quiver

end TauCeti
