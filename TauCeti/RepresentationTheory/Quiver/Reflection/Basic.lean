/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.FinitePaths

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
(`TauCeti.Quiver.IsSink.isSource_reflect`) and preserves acyclicity
(`TauCeti.Quiver.IsAcyclic.reflect_of_isSink`). A nonempty finite acyclic quiver always has a
sink and a source to reflect at (`TauCeti.Quiver.IsAcyclic.exists_isSink`,
`TauCeti.Quiver.IsAcyclic.exists_isSource`).

## Main definitions

* `TauCeti.Quiver.IsSink`, `TauCeti.Quiver.IsSource`: a vertex with no outgoing, respectively no
  incoming, arrow.
* `TauCeti.Quiver.reflectHom`: the arrow types of the quiver obtained by reversing every arrow
  incident to a given vertex.
* `TauCeti.Quiver.Reflect`: that quiver, on the same vertex type.

## Main results

* `TauCeti.Quiver.IsAcyclic.exists_isSink`: a nonempty finite acyclic quiver has a sink.
* `TauCeti.Quiver.IsSink.isSource_reflect`: reflecting at a sink turns it into a source.
* `TauCeti.Quiver.IsAcyclic.reflect_of_isSink`: reflecting an acyclic quiver at a sink leaves it
  acyclic.
* `TauCeti.Quiver.hom_reflect_reflect`: reflecting twice at the same vertex restores the original
  arrows, so reflection at a vertex is an involution.

## References

This file supplies the reflected quiver `Q.reflect i` that the reflection functors of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md` map into. See
Derksen--Weyman, *An Introduction to Quiver Representations*, and
Bernstein--Gelfand--Ponomarev, *Coxeter functors and Gabriel's theorem*.
-/

@[expose] public section

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

/-- No arrow leaves a sink. -/
theorem IsSink.isEmpty_hom {i : V} (h : IsSink i) (b : V) : IsEmpty (i ⟶ b) :=
  h b

/-- No arrow enters a source. -/
theorem IsSource.isEmpty_hom {i : V} (h : IsSource i) (a : V) : IsEmpty (a ⟶ i) :=
  h a

/-- A sink carries no loop. -/
theorem IsSink.isEmpty_hom_self {i : V} (h : IsSink i) : IsEmpty (i ⟶ i) :=
  h i

/-- A source carries no loop. -/
theorem IsSource.isEmpty_hom_self {i : V} (h : IsSource i) : IsEmpty (i ⟶ i) :=
  h i

/-- A path out of a sink is trivial, so it ends where it started. -/
theorem IsSink.eq_of_path {i b : V} (h : IsSink i) (p : Path i b) : i = b := by
  induction p with
  | nil => rfl
  | cons _ e ih => subst ih; exact (h _).elim e

/-- A path into a source is trivial, so it starts where it ends. -/
theorem IsSource.eq_of_path {i a : V} (h : IsSource i) (p : Path a i) : a = i := by
  cases p with
  | nil => rfl
  | cons _ e => exact (h _).elim e

/-- A nonempty finite acyclic quiver has a sink: were every vertex to carry an outgoing arrow,
paths could be extended indefinitely, past the bound of
`TauCeti.Quiver.IsAcyclic.length_lt_card`. -/
theorem IsAcyclic.exists_isSink [Finite V] [Nonempty V] (h : IsAcyclic V) :
    ∃ i : V, IsSink i := by
  letI : Fintype V := Fintype.ofFinite V
  by_contra hcon
  have hout : ∀ i : V, ∃ b : V, Nonempty (i ⟶ b) := fun i ↦ by
    by_contra hi
    exact hcon ⟨i, fun b ↦ not_nonempty_iff.mp fun hb ↦ hi ⟨b, hb⟩⟩
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
    exact hcon ⟨i, fun a ↦ not_nonempty_iff.mp fun ha ↦ hi ⟨a, ha⟩⟩
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

/-! ### The arrows of the reflected quiver -/

variable [DecidableEq V]

/-- The arrows from `a` to `b` in the quiver obtained from `V` by reversing every arrow incident
to the vertex `i`. Arrows between two vertices other than `i` are untouched, an arrow `b ⟶ i`
becomes an arrow `i ⟶ b`, and the loops at `i` are reversed among themselves. -/
def reflectHom (i a b : V) : Type v :=
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

instance instFintypeReflectHom [∀ a b : V, Fintype (a ⟶ b)] (i a b : V) :
    Fintype (reflectHom i a b) := by
  unfold reflectHom
  split <;> split <;> infer_instance

/-! ### The reflected quiver -/

/-- The reflection of a quiver at a vertex `i`: a type synonym for the vertex type, carrying the
quiver in which every arrow incident to `i` is reversed. -/
def Reflect (V : Type u) (_i : V) : Type u := V

instance reflectQuiver (i : V) : _root_.Quiver.{v} (Reflect V i) :=
  ⟨fun a b : V ↦ reflectHom i a b⟩

instance (i : V) : DecidableEq (Reflect V i) :=
  inferInstanceAs (DecidableEq V)

instance (i : V) [Fintype V] : Fintype (Reflect V i) :=
  inferInstanceAs (Fintype V)

instance (i : V) [Nonempty V] : Nonempty (Reflect V i) :=
  inferInstanceAs (Nonempty V)

instance (i : V) [∀ a b : V, Fintype (a ⟶ b)] (a b : Reflect V i) : Fintype (a ⟶ b) :=
  instFintypeReflectHom i a b

/-- The arrow types of the reflected quiver are the ones computed by
`TauCeti.Quiver.reflectHom`. -/
@[simp]
theorem hom_reflect (i : V) (a b : Reflect V i) : (a ⟶ b) = reflectHom i a b :=
  rfl

/-- Reflecting at a sink turns it into a source: no arrow of the reflected quiver enters `i`. -/
theorem IsSink.isSource_reflect {i : V} (h : IsSink i) : @IsSource (Reflect V i) _ i :=
  fun a ↦ ⟨fun e ↦ (h a).elim (cast (reflectHom_right i a) e)⟩

/-- Reflecting at a source turns it into a sink: no arrow of the reflected quiver leaves `i`. -/
theorem IsSource.isSink_reflect {i : V} (h : IsSource i) : @IsSink (Reflect V i) _ i :=
  fun b ↦ ⟨fun e ↦ (h b).elim (cast (reflectHom_left i b) e)⟩

/-- Reflecting twice at the same vertex restores the original arrow types: reflection at a vertex
is an involution on quivers. -/
theorem hom_reflect_reflect (i a b : V) :
    @_root_.Quiver.Hom (Reflect (Reflect V i) i) _ a b = (a ⟶ b) := by
  change @reflectHom (Reflect V i) _ _ i a b = _
  rcases eq_or_ne a i with rfl | ha
  · simp
  · rcases eq_or_ne b i with rfl | hb
    · simp
    · rw [@reflectHom_of_ne_of_ne (Reflect V i) _ _ i a b ha hb, hom_reflect,
        reflectHom_of_ne_of_ne ha hb]

/-- Away from a sink, a path of the reflected quiver comes from a path of the original quiver of
the same length; in particular it cannot reach the sink. -/
private theorem exists_path_of_isSink {i : V} (h : IsSink i) {a b : Reflect V i} (ha : a ≠ i)
    (p : Path a b) : b ≠ i ∧ ∃ q : @Path V _ a b, q.length = p.length := by
  induction p with
  | nil => exact ⟨ha, Path.nil, rfl⟩
  | @cons c d p e ih =>
    obtain ⟨hc, q, hq⟩ := ih
    by_cases hd : d = i
    · exact (h.isSource_reflect c).elim (hd ▸ e)
    · refine ⟨hd, q.cons (cast (reflectHom_of_ne_of_ne hc hd) e), ?_⟩
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
    | cons _ e => exact (h.isSource_reflect _).elim (ha ▸ e)
  · obtain ⟨-, q, hq⟩ := exists_path_of_isSink h ha p
    rw [← hq, hV.length_eq_zero q]

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
  exact h a

end Quiver

end TauCeti
