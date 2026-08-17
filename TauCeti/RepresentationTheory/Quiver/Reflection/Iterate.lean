/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Reflection.Basic

/-!
# Iterating the reflection of a quiver along a list of vertices

Reflecting a quiver at a vertex reverses the arrows meeting that vertex. Iterating a reflection
changes the quiver, not the vertex type, so the carrier here is the quiver *structure* rather than
the type synonym `TauCeti.Quiver.Reflect`: the reflection at the second vertex has to be taken with
respect to the structure produced by the first. Accordingly `TauCeti.Quiver.reflectAt` repackages
`TauCeti.Quiver.reflectHom` as an operation on `Quiver` structures on a fixed vertex type — it has
the arrows of `Reflect V i`, by `TauCeti.Quiver.hom_reflectAt_eq_hom_reflect` — and
`TauCeti.Quiver.reflectList` folds it along a list.

## Main definitions

* `TauCeti.Quiver.reflectAt`: reflection at a vertex, as an operation on quiver structures.
* `TauCeti.Quiver.reflectList`: reflection at each vertex of a list, in order.

## Main results

* `TauCeti.Quiver.reflectAt_reflectAt`: reflecting twice at the same vertex returns the quiver
  structure it started from.
* `TauCeti.Quiver.hom_reflectList` and `TauCeti.Quiver.hom_reflectList_of_not_iff`: reflecting
  along a repetition-free list reverses exactly the arrows joining a vertex of the list to a
  vertex outside it.
* `TauCeti.Quiver.reflectList_eq_self`: reflecting once at every vertex restores the original
  quiver structure, with `TauCeti.Quiver.hom_reflectList_of_forall_mem` the same statement on
  arrow types.

## References

The lists along which this iteration is sink-admissible are studied in
`TauCeti.RepresentationTheory.Quiver.Reflection.Admissible`. A sink-admissible list may be empty,
may repeat a vertex and need not exhaust the vertices; it is along a sink-admissible ordering — a
sink-admissible list that is repetition-free and contains every vertex — that the reflection
functors of Layer 4 of `TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`
compose into the Coxeter functor. See Bernstein--Gelfand--Ponomarev, *Coxeter functors and
Gabriel's theorem*.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u}

namespace Quiver

/-! ### Reflection as an operation on quiver structures -/

/-- Reflection at the vertex `i`, as an operation on the quiver structures carried by a fixed
vertex type: `reflectAt q i` has the arrows of `q` with every arrow incident to `i` reversed.
Unlike the type synonym `TauCeti.Quiver.Reflect`, this form iterates, which is what a sequence of
reflections needs. -/
@[instance_reducible]
noncomputable def reflectAt (q : _root_.Quiver.{v} V) (i : V) : _root_.Quiver.{v} V :=
  ⟨@reflectHom V q i⟩

/-- The arrows of `reflectAt q i` are the ones computed by `TauCeti.Quiver.reflectHom`. -/
@[simp]
theorem hom_reflectAt (q : _root_.Quiver.{v} V) (i a b : V) :
    @_root_.Quiver.Hom V (reflectAt q i) a b = @reflectHom V q i a b :=
  (rfl)

/-- `reflectAt` reproduces the quiver carried by the type synonym `TauCeti.Quiver.Reflect`. -/
theorem hom_reflectAt_eq_hom_reflect [q : _root_.Quiver.{v} V] (i a b : V) :
    @_root_.Quiver.Hom V (reflectAt q i) a b = @_root_.Quiver.Hom (Reflect V i) _ a b :=
  (hom_reflectAt q i a b).trans (hom_reflect i a b).symm

/-- **Reflection at a vertex is an involution.** Reflecting twice at the same vertex reverses the
arrows meeting it twice, returning the quiver structure it started from. Since `reflectAt` carries
the arrows of the type synonym `TauCeti.Quiver.Reflect`, the arrow types agree by
`TauCeti.Quiver.hom_reflect_reflect`. -/
@[simp]
theorem reflectAt_reflectAt (q : _root_.Quiver.{v} V) (i : V) :
    reflectAt (reflectAt q i) i = q :=
  congrArg _root_.Quiver.mk (funext fun a ↦ funext fun b ↦ @hom_reflect_reflect V q i a b)

/-! ### Reflecting along a list of vertices -/

/-- Reflection at each vertex of a list in turn, starting from the head. -/
@[instance_reducible]
noncomputable def reflectList (q : _root_.Quiver.{v} V) (l : List V) : _root_.Quiver.{v} V :=
  l.foldl reflectAt q

@[simp]
theorem reflectList_nil (q : _root_.Quiver.{v} V) : reflectList q [] = q :=
  (rfl)

@[simp]
theorem reflectList_cons (q : _root_.Quiver.{v} V) (i : V) (l : List V) :
    reflectList q (i :: l) = reflectList (reflectAt q i) l :=
  (rfl)

/-- Reflecting along a concatenation is reflecting along the two segments in turn, which is how an
ordering is split into an already reflected initial segment and the entries still to come. -/
@[simp]
theorem reflectList_append (q : _root_.Quiver.{v} V) (l₁ l₂ : List V) :
    reflectList q (l₁ ++ l₂) = reflectList (reflectList q l₁) l₂ :=
  (List.foldl_append)

/-! ### Reflecting along a repetition-free list -/

/-- The induction behind `TauCeti.Quiver.hom_reflectList`. Both directions are proved at once
because peeling off the head of the list exchanges them: the head lies on the list and every
vertex it is joined to changes side. -/
private theorem hom_reflectList_aux :
    ∀ l : List V, l.Nodup → ∀ (q : _root_.Quiver.{v} V) (a b : V),
      ((a ∈ l ↔ b ∈ l) →
          @_root_.Quiver.Hom V (reflectList q l) a b = @_root_.Quiver.Hom V q a b) ∧
        (¬(a ∈ l ↔ b ∈ l) →
          @_root_.Quiver.Hom V (reflectList q l) a b = @_root_.Quiver.Hom V q b a) := by
  intro l
  induction l with
  | nil => exact fun _ q a b ↦ ⟨fun _ ↦ rfl, fun h ↦ absurd (by simp) h⟩
  | cons i t ih =>
    intro hnd q a b
    rw [List.nodup_cons] at hnd
    obtain ⟨hit, hnd⟩ := hnd
    have hii : i ∈ i :: t := by simp
    have hmem : ∀ v : V, v ≠ i → (v ∈ i :: t ↔ v ∈ t) := fun v hv ↦ by simp [hv]
    rw [reflectList_cons]
    by_cases hai : a = i
    · by_cases hbi : b = i
      · rw [hai, hbi]
        refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩ <;>
          rw [(ih hnd (reflectAt q i) i i).1 Iff.rfl, hom_reflectAt, @reflectHom_left V q i i]
      · rw [hai]
        by_cases hbt : b ∈ t
        · refine ⟨fun _ ↦ ?_, fun h ↦ absurd (iff_of_true hii (by simp [hbt])) h⟩
          rw [(ih hnd (reflectAt q i) i b).2 (by simp [hit, hbt]), hom_reflectAt,
            @reflectHom_right V q i b]
        · refine ⟨fun h ↦ absurd (h.mp hii) (by simp [hbi, hbt]), fun _ ↦ ?_⟩
          rw [(ih hnd (reflectAt q i) i b).1 (iff_of_false hit hbt), hom_reflectAt,
            @reflectHom_left V q i b]
    · by_cases hbi : b = i
      · rw [hbi]
        by_cases hat : a ∈ t
        · refine ⟨fun _ ↦ ?_, fun h ↦ absurd (iff_of_true (by simp [hat]) hii) h⟩
          rw [(ih hnd (reflectAt q i) a i).2 (by simp [hit, hat]), hom_reflectAt,
            @reflectHom_left V q i a]
        · refine ⟨fun h ↦ absurd (h.mpr hii) (by simp [hai, hat]), fun _ ↦ ?_⟩
          rw [(ih hnd (reflectAt q i) a i).1 (iff_of_false hat hit), hom_reflectAt,
            @reflectHom_right V q i a]
      · rw [hmem a hai, hmem b hbi]
        refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · rw [(ih hnd (reflectAt q i) a b).1 h, hom_reflectAt,
            @reflectHom_of_ne_of_ne V q i a b hai hbi]
        · rw [(ih hnd (reflectAt q i) a b).2 h, hom_reflectAt,
            @reflectHom_of_ne_of_ne V q i b a hbi hai]

/-- **Reflecting along a repetition-free list.** An arrow joining two vertices that are both on
the list, or both off it, survives: each of its ends is reversed the same number of times. -/
theorem hom_reflectList (q : _root_.Quiver.{v} V) {l : List V} (hl : l.Nodup) {a b : V}
    (h : a ∈ l ↔ b ∈ l) :
    @_root_.Quiver.Hom V (reflectList q l) a b = @_root_.Quiver.Hom V q a b :=
  (hom_reflectList_aux l hl q a b).1 h

/-- Reflecting along a repetition-free list reverses the arrows joining a vertex of the list to a
vertex outside it: exactly one of the two ends is met by a reflection. -/
theorem hom_reflectList_of_not_iff (q : _root_.Quiver.{v} V) {l : List V} (hl : l.Nodup)
    {a b : V} (h : ¬(a ∈ l ↔ b ∈ l)) :
    @_root_.Quiver.Hom V (reflectList q l) a b = @_root_.Quiver.Hom V q b a :=
  (hom_reflectList_aux l hl q a b).2 h

/-- **Reflecting once at every vertex restores the quiver.** Both ends of every arrow are met by a
reflection, so every arrow is reversed twice. This is the arrow-type form; the equality of quiver
structures itself is `TauCeti.Quiver.reflectList_eq_self`. -/
theorem hom_reflectList_of_forall_mem (q : _root_.Quiver.{v} V) {l : List V} (hl : l.Nodup)
    (hall : ∀ v : V, v ∈ l) (a b : V) :
    @_root_.Quiver.Hom V (reflectList q l) a b = @_root_.Quiver.Hom V q a b :=
  hom_reflectList q hl (iff_of_true (hall a) (hall b))

/-- **Reflecting once at every vertex returns the quiver structure it started from.** In
particular the composite of the reflections along a full sink-admissible ordering — the
combinatorial shadow of the Coxeter functor — is an operation from the quiver to itself, not to
some other orientation. -/
theorem reflectList_eq_self (q : _root_.Quiver.{v} V) {l : List V} (hl : l.Nodup)
    (hall : ∀ v : V, v ∈ l) : reflectList q l = q :=
  congrArg _root_.Quiver.mk
    (funext fun a ↦ funext fun b ↦ hom_reflectList_of_forall_mem q hl hall a b)

end Quiver

end TauCeti
