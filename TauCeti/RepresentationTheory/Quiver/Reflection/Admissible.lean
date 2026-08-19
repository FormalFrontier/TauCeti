/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Preorder.Finite
public import TauCeti.RepresentationTheory.Quiver.Acyclic.Basic
public import TauCeti.RepresentationTheory.Quiver.Reflection.Iterate

/-!
# Sink-admissible orderings of the vertices of a quiver

Reflecting a quiver at a sink reverses the arrows meeting that vertex. Composing several such
reflections calls for a list of vertices that is *sink-admissible*: each entry must be a sink of
the quiver obtained by reflecting at all the entries preceding it, the iterated reflection
`TauCeti.Quiver.reflectList` of
`TauCeti.RepresentationTheory.Quiver.Reflection.Iterate`. This file constructs such an ordering
for every finite acyclic quiver.

## Main definitions

* `TauCeti.Quiver.IsSinkAdmissible`: a list of vertices each of which is a sink of the quiver
  reflected at its predecessors.

## Main results

* `TauCeti.Quiver.IsAcyclic.exists_isSinkAdmissible`: a finite acyclic quiver has a
  repetition-free sink-admissible ordering of all of its vertices.
* `TauCeti.Quiver.isSinkAdmissible_of_pairwise`: a repetition-free list along which no arrow runs
  forwards, whose entries carry no loop and emit no arrow off the list, is sink-admissible, with
  `TauCeti.Quiver.isSinkAdmissible_of_pairwise_of_forall_mem` the case of a list of all the
  vertices, where the last hypothesis — that no arrow leaves the list — is automatic.
* `TauCeti.Quiver.IsSinkAdmissible.isEmpty_hom_self`: no vertex of a repetition-free
  sink-admissible list carries a loop.

## References

This is the admissible-ordering milestone opening Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`, the input the Coxeter
functor of Layer 4 is assembled from. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and
Gabriel's theorem*, and Assem--Simson--Skowroński, *Elements of the Representation Theory of
Associative Algebras* I, VII.5.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u}

namespace Quiver

/-! ### Sink-admissible lists -/

/-- A list of vertices is **sink-admissible** for the quiver structure `q` when each of its
entries is a sink of the quiver obtained by reflecting `q` at all the entries preceding it. This
is the hypothesis under which the reflection functors at the successive entries can be composed at
all; the composite is the Coxeter functor when the list is in addition repetition-free and
contains every vertex, in which case the reflections carry `q` back to itself by
`TauCeti.Quiver.reflectList_eq_self`. -/
def IsSinkAdmissible (q : _root_.Quiver.{v} V) (l : List V) : Prop :=
  ∀ t u : List V, ∀ i : V, l = t ++ i :: u → @IsSink V (reflectList q t) i

/-- The defining condition for a sink-admissible list. -/
theorem isSinkAdmissible_def (q : _root_.Quiver.{v} V) (l : List V) :
    IsSinkAdmissible q l ↔ ∀ t u : List V, ∀ i : V, l = t ++ i :: u →
      @IsSink V (reflectList q t) i :=
  (Iff.rfl)

@[simp]
theorem isSinkAdmissible_nil (q : _root_.Quiver.{v} V) : IsSinkAdmissible q [] := by
  rw [isSinkAdmissible_def]
  intro t u i h
  simp at h

/-- A list is sink-admissible exactly when its head is a sink and its tail is sink-admissible for
the quiver reflected at that head. -/
@[simp]
theorem isSinkAdmissible_cons {q : _root_.Quiver.{v} V} {i : V} {l : List V} :
    IsSinkAdmissible q (i :: l) ↔ @IsSink V q i ∧ IsSinkAdmissible (reflectAt q i) l := by
  simp only [isSinkAdmissible_def]
  constructor
  · intro h
    refine ⟨?_, fun t u j ht ↦ ?_⟩
    · have := h [] l i rfl
      rwa [reflectList_nil] at this
    · have := h (i :: t) u j (by rw [List.cons_append, ht])
      rwa [reflectList_cons] at this
  · rintro ⟨hi, h⟩ t u j hj
    rcases t with _ | ⟨a, t⟩
    · rw [List.nil_append, List.cons.injEq] at hj
      rw [reflectList_nil, ← hj.1]
      exact hi
    · rw [List.cons_append, List.cons.injEq] at hj
      rw [← hj.1, reflectList_cons]
      exact h t u j hj.2

/-! ### Recognising a sink-admissible ordering -/

/-- The induction behind `TauCeti.Quiver.isSinkAdmissible_of_pairwise`. The last hypothesis, that
no arrow leaves the list, is what survives the passage from a list to its tail: reflecting at the
head turns the arrows out of the head into arrows into it. -/
private theorem isSinkAdmissible_of_pairwise_aux :
    ∀ (l : List V) (q : _root_.Quiver.{v} V), l.Nodup →
      (∀ x ∈ l, IsEmpty (@_root_.Quiver.Hom V q x x)) →
      (l.Pairwise fun x y ↦ IsEmpty (@_root_.Quiver.Hom V q x y)) →
      (∀ x ∈ l, ∀ b : V, b ∉ l → IsEmpty (@_root_.Quiver.Hom V q x b)) →
      IsSinkAdmissible q l := by
  intro l
  induction l with
  | nil => exact fun q _ _ _ _ ↦ isSinkAdmissible_nil q
  | cons i t ih =>
    intro q hnd hloop hp hout
    rw [List.nodup_cons] at hnd
    obtain ⟨hit, hnd⟩ := hnd
    rw [List.pairwise_cons] at hp
    obtain ⟨hhead, hp⟩ := hp
    have hii : i ∈ i :: t := by simp
    have hsink : @IsSink V q i := (@IsSink_def V q i).mpr fun b ↦ by
      by_cases hbi : b = i
      · rw [hbi]
        exact hloop i hii
      · by_cases hbt : b ∈ t
        · exact hhead b hbt
        · exact hout i hii b (by simp [hbi, hbt])
    have hloop' : ∀ x ∈ t, IsEmpty (@_root_.Quiver.Hom V (reflectAt q i) x x) := fun x hx ↦ by
      rw [hom_reflectAt, @reflectHom_of_ne_of_ne V q i x x (fun hc ↦ hit (hc ▸ hx))
        (fun hc ↦ hit (hc ▸ hx))]
      exact hloop x (List.mem_cons_of_mem _ hx)
    have hp' : t.Pairwise fun x y ↦ IsEmpty (@_root_.Quiver.Hom V (reflectAt q i) x y) := by
      refine (List.Pairwise.and_mem.mp hp).imp fun {x y} h ↦ ?_
      obtain ⟨hx, hy, hxy⟩ := h
      rw [hom_reflectAt, @reflectHom_of_ne_of_ne V q i x y (fun hc ↦ hit (hc ▸ hx))
        (fun hc ↦ hit (hc ▸ hy))]
      exact hxy
    have hout' : ∀ x ∈ t, ∀ b : V, b ∉ t →
        IsEmpty (@_root_.Quiver.Hom V (reflectAt q i) x b) := by
      intro x hx b hb
      rw [hom_reflectAt]
      by_cases hbi : b = i
      · rw [hbi, @reflectHom_right V q i x]
        exact hhead x hx
      · rw [@reflectHom_of_ne_of_ne V q i x b (fun hc ↦ hit (hc ▸ hx)) hbi]
        exact hout x (List.mem_cons_of_mem _ hx) b (by simp [hbi, hb])
    exact isSinkAdmissible_cons.mpr ⟨hsink, ih (reflectAt q i) hnd hloop' hp' hout'⟩

/-- **A topological ordering is sink-admissible.** If `l` repeats no vertex, no entry of `l`
carries a loop, no arrow runs from an earlier entry of `l` to a later one — equivalently, the
target of such an arrow precedes its source — and no arrow leaves `l` for a vertex outside it,
then each entry is a sink once its predecessors have been reflected. The list need not exhaust the
vertices; `TauCeti.Quiver.isSinkAdmissible_of_pairwise_of_forall_mem` is the case where it does,
in which the last hypothesis is vacuous. -/
theorem isSinkAdmissible_of_pairwise (q : _root_.Quiver.{v} V) {l : List V} (hnd : l.Nodup)
    (hloop : ∀ x ∈ l, IsEmpty (@_root_.Quiver.Hom V q x x))
    (hp : l.Pairwise fun x y ↦ IsEmpty (@_root_.Quiver.Hom V q x y))
    (hout : ∀ x ∈ l, ∀ b : V, b ∉ l → IsEmpty (@_root_.Quiver.Hom V q x b)) :
    IsSinkAdmissible q l :=
  isSinkAdmissible_of_pairwise_aux l q hnd hloop hp hout

/-- A repetition-free list of all the vertices along which no arrow runs forwards, no vertex
carrying a loop, is sink-admissible: this is the case of
`TauCeti.Quiver.isSinkAdmissible_of_pairwise` in which nothing lies outside the list, so no arrow
can leave it. Such a list is a sink-admissible *ordering*, the input the Coxeter functor is
assembled from. -/
theorem isSinkAdmissible_of_pairwise_of_forall_mem (q : _root_.Quiver.{v} V) {l : List V}
    (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l)
    (hloop : ∀ v : V, IsEmpty (@_root_.Quiver.Hom V q v v))
    (hp : l.Pairwise fun x y ↦ IsEmpty (@_root_.Quiver.Hom V q x y)) :
    IsSinkAdmissible q l :=
  isSinkAdmissible_of_pairwise q hnd (fun x _ ↦ hloop x) hp fun _ _ b hb ↦ absurd (hall b) hb

/-! ### Loops along a sink-admissible ordering -/

/-- **No vertex of a repetition-free sink-admissible list carries a loop.** At its own stage the
vertex is a sink of the reflected quiver, so it carries no loop there; and reflecting along a
repetition-free prefix leaves the loops at any vertex alone
(`TauCeti.Quiver.hom_reflectList`), because both ends of a loop lie on the same side of the
prefix. This is the looplessness hypothesis under which the composite of the simple reflections
along the list preserves the Tits form. -/
theorem IsSinkAdmissible.isEmpty_hom_self {q : _root_.Quiver.{v} V} {l : List V} (hnd : l.Nodup)
    (hl : IsSinkAdmissible q l) {i : V} (hi : i ∈ l) :
    IsEmpty (@_root_.Quiver.Hom V q i i) := by
  obtain ⟨t, u, rfl⟩ := List.append_of_mem hi
  rw [← hom_reflectList q (List.Nodup.of_append_left hnd) (a := i) (b := i) Iff.rfl]
  exact @IsSink.isEmpty_hom_self V (reflectList q t) i (hl t u i rfl)

/-! ### Existence for a finite acyclic quiver -/

variable [q : _root_.Quiver.{v} V]

/-- A nonempty finite set of vertices of an acyclic quiver contains a vertex emitting no arrow
into the set: a maximal vertex for the reachability preorder cannot, since an arrow out of it
would have to be matched by a path back. -/
private theorem exists_isEmpty_hom_mem (h : IsAcyclic V) {s : Finset V} (hs : s.Nonempty) :
    ∃ i ∈ s, ∀ b ∈ s, IsEmpty (i ⟶ b) := by
  let : LE V := ⟨fun a b ↦ Nonempty (Path a b)⟩
  have : IsTrans V (· ≤ · : V → V → Prop) := ⟨fun a b c hab hbc ↦ by
    obtain ⟨p⟩ : Nonempty (Path a b) := hab
    obtain ⟨r⟩ : Nonempty (Path b c) := hbc
    exact ⟨p.comp r⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_maximal hs
  refine ⟨i, hi, fun b hb ↦ ⟨fun e ↦ ?_⟩⟩
  obtain ⟨p⟩ : Nonempty (Path b i) := hmax hb (⟨e.toPath⟩ : Nonempty (Path i b))
  obtain rfl : i = b := h.eq_of_paths e.toPath p
  exact (h.isEmpty_hom_self i).elim e

/-- Every finite set of vertices of an acyclic quiver can be listed so that no arrow runs from an
earlier entry to a later one: peel off a vertex emitting no arrow inside the set, and recurse. -/
private theorem exists_pairwise_isEmpty_hom (h : IsAcyclic V) (s : Finset V) :
    ∃ l : List V, l.Nodup ∧ (∀ v : V, v ∈ l ↔ v ∈ s) ∧
      l.Pairwise fun x y ↦ IsEmpty (x ⟶ y) := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨[], List.nodup_nil, by simp, List.Pairwise.nil⟩
    · obtain ⟨i, his, hsink⟩ := exists_isEmpty_hom_mem h hs
      obtain ⟨t, htnd, htmem, htp⟩ := ih (s.erase i) (Finset.erase_ssubset his)
      have hit : i ∉ t := fun hc ↦ by simpa using (htmem i).mp hc
      refine ⟨i :: t, List.nodup_cons.mpr ⟨hit, htnd⟩, fun v ↦ ?_,
        List.pairwise_cons.mpr ⟨fun y hy ↦ hsink y (Finset.mem_of_mem_erase ((htmem y).mp hy)),
          htp⟩⟩
      rw [List.mem_cons, htmem v, Finset.mem_erase]
      constructor
      · rintro (rfl | ⟨-, hv⟩)
        · exact his
        · exact hv
      · intro hv
        by_cases hvi : v = i
        · exact Or.inl hvi
        · exact Or.inr ⟨hvi, hv⟩

/-- **Every finite acyclic quiver has a sink-admissible ordering of its vertices**: a list without
repetitions containing every vertex, each entry of which is a sink once its predecessors have been
reflected. This is what lets the reflection functors at the successive vertices be composed into
the Coxeter functor, and by `TauCeti.Quiver.reflectList_eq_self` the composite returns to the
original quiver. -/
theorem IsAcyclic.exists_isSinkAdmissible [Finite V] (h : IsAcyclic V) :
    ∃ l : List V, l.Nodup ∧ (∀ v : V, v ∈ l) ∧ IsSinkAdmissible q l := by
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨l, hnd, hmem, hp⟩ := exists_pairwise_isEmpty_hom h Finset.univ
  have hall : ∀ v : V, v ∈ l := fun v ↦ (hmem v).mpr (Finset.mem_univ v)
  exact ⟨l, hnd, hall,
    isSinkAdmissible_of_pairwise_of_forall_mem q hnd hall (fun v ↦ h.isEmpty_hom_self v) hp⟩

end Quiver

end TauCeti
