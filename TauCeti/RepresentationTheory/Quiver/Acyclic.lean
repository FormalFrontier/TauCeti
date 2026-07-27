import Mathlib.Combinatorics.Quiver.Path

/-!
# Acyclic quivers

This file defines an acyclic quiver to be one whose closed paths are all trivial. It develops
the elementary path API for excluding directed cycles, including the fact that paths cannot run
in both directions between distinct vertices.

This is the orientation-sensitive notion of acyclicity used for path algebras and quiver
representations. It is distinct from acyclicity of the underlying undirected graph.
-/

namespace TauCeti

open Quiver

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- A quiver is acyclic if every closed path is trivial. -/
def Quiver.IsAcyclic (V : Type u) [Quiver.{v} V] : Prop :=
  ∀ ⦃a : V⦄ (p : Path a a), p = Path.nil

namespace Quiver.IsAcyclic

/-- A quiver is acyclic exactly when every closed path has length zero. -/
theorem iff_forall_length_eq_zero :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), p.length = 0 := by
  constructor
  · intro h a p
    rw [h p]
    exact Path.length_nil
  · intro h a p
    exact p.eq_nil_of_length_zero (h p)

/-- In an acyclic quiver, every closed path has length zero. -/
theorem length_eq_zero (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    p.length = 0 :=
  iff_forall_length_eq_zero.mp h p

/-- An acyclic quiver has no closed path of positive length. -/
theorem not_length_pos (h : Quiver.IsAcyclic V) {a : V} (p : Path a a) :
    ¬0 < p.length := by
  rw [h.length_eq_zero p]
  exact Nat.lt_irrefl 0

/-- A quiver is acyclic exactly when it has no closed path of positive length. -/
theorem iff_forall_not_length_pos :
    Quiver.IsAcyclic V ↔ ∀ ⦃a : V⦄ (p : Path a a), ¬0 < p.length := by
  constructor
  · exact fun h a p ↦ h.not_length_pos p
  · intro h a p
    apply p.eq_nil_of_length_zero
    have hp := h p
    omega

/-- A quiver is acyclic exactly when it has no nontrivial closed path. -/
theorem iff_not_exists_ne_nil :
    Quiver.IsAcyclic V ↔ ¬∃ (a : V) (p : Path a a), p ≠ Path.nil := by
  constructor
  · intro h hex
    obtain ⟨a, p, hp⟩ := hex
    exact hp (h p)
  · intro h a p
    by_contra hp
    exact h ⟨a, p, hp⟩

/-- The composition of paths in opposite directions is trivial in an acyclic quiver. -/
@[simp]
theorem comp_eq_nil (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    p.comp q = Path.nil :=
  h (p.comp q)

/-- If paths run in both directions in an acyclic quiver, the forward path has length zero. -/
theorem length_eq_zero_of_paths_left (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    p.length = 0 := by
  have hpq : (p.comp q).length = 0 := h.length_eq_zero (p.comp q)
  rw [Path.length_comp] at hpq
  omega

/-- If paths run in both directions in an acyclic quiver, the reverse path has length zero. -/
theorem length_eq_zero_of_paths_right (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    q.length = 0 := by
  have hpq : (p.comp q).length = 0 := h.length_eq_zero (p.comp q)
  rw [Path.length_comp] at hpq
  omega

/-- Vertices joined by paths in both directions in an acyclic quiver are equal. -/
theorem eq_of_paths (h : Quiver.IsAcyclic V) {a b : V}
    (p : Path a b) (q : Path b a) :
    a = b :=
  p.eq_of_length_zero (h.length_eq_zero_of_paths_left p q)

/-- Between distinct vertices of an acyclic quiver, paths cannot exist in both directions. -/
theorem not_nonempty_path_and_nonempty_path (h : Quiver.IsAcyclic V) {a b : V}
    (hab : a ≠ b) :
    ¬(Nonempty (Path a b) ∧ Nonempty (Path b a)) := by
  rintro ⟨⟨p⟩, ⟨q⟩⟩
  exact hab (h.eq_of_paths p q)

/-- A path between distinct vertices of an acyclic quiver excludes every reverse path. -/
theorem isEmpty_path_of_path (h : Quiver.IsAcyclic V) {a b : V}
    (hab : a ≠ b) (p : Path a b) :
    IsEmpty (Path b a) :=
  ⟨fun q ↦ hab (h.eq_of_paths p q)⟩

/-- An acyclic quiver has no loops. -/
theorem isEmpty_hom_self (h : Quiver.IsAcyclic V) (a : V) :
    IsEmpty (a ⟶ a) :=
  ⟨fun e ↦ Path.cons_ne_nil Path.nil e (h e.toPath)⟩

/-- In an acyclic quiver, an arrow between distinct vertices excludes a reverse arrow. -/
theorem isEmpty_hom_of_hom (h : Quiver.IsAcyclic V) {a b : V}
    (hab : a ≠ b) (e : a ⟶ b) :
    IsEmpty (b ⟶ a) :=
  ⟨fun f ↦ hab (h.eq_of_paths e.toPath f.toPath)⟩

/-- Closed paths in an acyclic quiver form a subsingleton. -/
theorem subsingleton_path_self (h : Quiver.IsAcyclic V) (a : V) :
    Subsingleton (Path a a) :=
  ⟨fun p q ↦ (h p).trans (h q).symm⟩

/-- A quiver with no arrows is acyclic. -/
theorem of_isEmpty_hom [∀ a b : V, IsEmpty (a ⟶ b)] :
    Quiver.IsAcyclic V := by
  intro a p
  cases p with
  | nil => rfl
  | cons _ e => exact isEmptyElim e

/-- A quiver embedded faithfully into an acyclic quiver is acyclic. -/
theorem of_injective_mapPath {W : Type*} [Quiver W] (F : V ⥤q W)
    (hW : Quiver.IsAcyclic W)
    (hinj : ∀ ⦃a : V⦄, Function.Injective (F.mapPath : Path a a → Path (F.obj a) (F.obj a))) :
    Quiver.IsAcyclic V := by
  intro a p
  apply hinj
  rw [hW (F.mapPath p)]
  exact F.mapPath_nil a

/-- A quiver is acyclic if its paths embed in the paths of an acyclic quiver. -/
theorem of_injective_prefunctor {W : Type*} [Quiver W] (F : V ⥤q W)
    (hW : Quiver.IsAcyclic W)
    (hinj : ∀ ⦃a b : V⦄, Function.Injective (F.mapPath : Path a b → Path (F.obj a) (F.obj b))) :
    Quiver.IsAcyclic V :=
  of_injective_mapPath F hW fun {_} ↦ @hinj _ _

end Quiver.IsAcyclic

end TauCeti
