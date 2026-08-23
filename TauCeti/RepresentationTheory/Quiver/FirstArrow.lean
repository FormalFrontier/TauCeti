/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The first arrow of a path

A path `a → j` in a quiver is either trivial, which forces `a = j`, or a first arrow `a ⟶ b`
followed by a path `b → j`. This file records that dichotomy as an equivalence and reads off the
resulting recursion for the number of paths into a fixed vertex.

It is the mirror image of `TauCeti.RepresentationTheory.Quiver.LastArrow`, which decomposes a path
by its *last* arrow instead, and the two feed the two sides of the Euler form of a finite quiver.

## Main definitions

* `TauCeti.pathFirstArrowEquiv`: the first-arrow decomposition
  `Path a j ≃ PLift (a = j) ⊕ Σ b, (a ⟶ b) × Path b j`.

## Main results

* `TauCeti.card_path_eq_ite_add_sum_firstArrow`: the path count `#(a → j)` equals
  `∑_b #(a ⟶ b) · #(b → j)`, plus `1` when `a = j` for the trivial path.

## Implementation notes

`Quiver.Path` recurses on its *target* vertex, so — unlike the last arrow, which is the head of the
`Quiver.Path.cons` constructor — the first arrow of a path is not visible to a match. The forward
map `pathFirstArrowSplit` is therefore an honest recursion over the path: on `p.cons e` it splits
`p` and, if `p` turned out to be trivial, promotes `e` to the first arrow, transporting it along the
equality of vertices with `Quiver.Hom.cast`; otherwise it appends `e` to the tail. The inverse
`pathOfFirstArrow` is the direct construction `e.toPath.comp p`, and the two round trips are
inductions over the same recursion. Both maps are `private`: the four characteristic lemmas
`TauCeti.pathFirstArrowEquiv_nil`, `TauCeti.pathFirstArrowEquiv_toPath_comp`,
`TauCeti.pathFirstArrowEquiv_symm_inl` and `TauCeti.pathFirstArrowEquiv_symm_inr` are the whole
public interface, and consumers never unfold the equivalence.

The proposition `a = j` is wrapped in `PLift` only to make the summand a type, so that `Nat.card`
applies, exactly as in the last-arrow decomposition.

## References

The path count is the combinatorial input to the Euler-form identity for the injective
representation at a vertex, Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- The forward map of the first-arrow decomposition, by recursion on the path: a path
`p.cons e` whose initial segment `p` is trivial has `e` for its first arrow and nothing left over,
and otherwise it has the first arrow of `p`, followed by the tail of `p` extended by `e`. -/
private def pathFirstArrowSplit {a : V} : ∀ {j : V}, Quiver.Path a j →
    (PLift (a = j) ⊕ Σ b : V, (a ⟶ b) × Quiver.Path b j)
  | _, .nil => Sum.inl ⟨rfl⟩
  | j, .cons p e =>
      match pathFirstArrowSplit p with
      | Sum.inl h => Sum.inr ⟨j, e.cast h.down.symm rfl, Quiver.Path.nil⟩
      | Sum.inr ⟨b, f, q⟩ => Sum.inr ⟨b, f, q.cons e⟩

/-- The inverse map of the first-arrow decomposition: the trivial path on the left summand, and the
first arrow prepended to the remaining path on the right. -/
private def pathOfFirstArrow {a j : V} :
    (PLift (a = j) ⊕ Σ b : V, (a ⟶ b) × Quiver.Path b j) → Quiver.Path a j
  | Sum.inl ⟨rfl⟩ => Quiver.Path.nil
  | Sum.inr ⟨_, e, p⟩ => e.toPath.comp p

private theorem pathFirstArrowSplit_cons {a c j : V} (p : Quiver.Path a c) (e : c ⟶ j) :
    pathFirstArrowSplit (p.cons e) =
      (match pathFirstArrowSplit p with
        | Sum.inl h => Sum.inr ⟨j, e.cast h.down.symm rfl, Quiver.Path.nil⟩
        | Sum.inr ⟨b, f, q⟩ => Sum.inr ⟨b, f, q.cons e⟩) :=
  (rfl)

private theorem pathOfFirstArrow_pathFirstArrowSplit {a j : V} (p : Quiver.Path a j) :
    pathOfFirstArrow (pathFirstArrowSplit p) = p := by
  induction p with
  | nil => rfl
  | @cons c j p e ih =>
    rw [pathFirstArrowSplit_cons]
    cases hs : pathFirstArrowSplit p with
    | inl h =>
      obtain ⟨rfl⟩ := h
      rw [hs] at ih
      simp only [pathOfFirstArrow] at ih ⊢
      subst ih
      rfl
    | inr y =>
      obtain ⟨b, f, q⟩ := y
      rw [hs] at ih
      simp only [pathOfFirstArrow] at ih ⊢
      rw [Quiver.Path.comp_cons, ih]

private theorem pathFirstArrowSplit_toPath_comp {a b j : V} (e : a ⟶ b) (q : Quiver.Path b j) :
    pathFirstArrowSplit (e.toPath.comp q) = Sum.inr ⟨b, e, q⟩ := by
  induction q with
  | nil => rfl
  | @cons c j q f ih => rw [Quiver.Path.comp_cons, pathFirstArrowSplit_cons, ih]

/-- **The first-arrow decomposition of a path.** A path `a → j` is either trivial, and then `a = j`,
or a first arrow `a ⟶ b` followed by a path `b → j`, uniquely so. -/
def pathFirstArrowEquiv (a j : V) :
    Quiver.Path a j ≃ (PLift (a = j) ⊕ Σ b : V, (a ⟶ b) × Quiver.Path b j) where
  toFun := pathFirstArrowSplit
  invFun := pathOfFirstArrow
  left_inv := pathOfFirstArrow_pathFirstArrowSplit
  right_inv x := by
    cases x with
    | inl h => obtain ⟨rfl⟩ := h; rfl
    | inr y => obtain ⟨b, e, q⟩ := y; exact pathFirstArrowSplit_toPath_comp e q

/-- The trivial path is the left summand of the first-arrow decomposition. -/
@[simp]
theorem pathFirstArrowEquiv_nil (a : V) :
    pathFirstArrowEquiv a a Quiver.Path.nil = Sum.inl ⟨rfl⟩ :=
  (rfl)

/-- A path with a first arrow is the right summand of the first-arrow decomposition. -/
@[simp]
theorem pathFirstArrowEquiv_toPath_comp {a b j : V} (e : a ⟶ b) (q : Quiver.Path b j) :
    pathFirstArrowEquiv a j (e.toPath.comp q) = Sum.inr ⟨b, e, q⟩ :=
  pathFirstArrowSplit_toPath_comp e q

/-- The left summand of the first-arrow decomposition recomposes to the trivial path. -/
@[simp]
theorem pathFirstArrowEquiv_symm_inl (a : V) :
    (pathFirstArrowEquiv a a).symm (Sum.inl ⟨rfl⟩) = Quiver.Path.nil :=
  (rfl)

/-- The right summand of the first-arrow decomposition recomposes by prepending the first arrow. -/
@[simp]
theorem pathFirstArrowEquiv_symm_inr {a j : V} (b : V) (e : a ⟶ b) (q : Quiver.Path b j) :
    (pathFirstArrowEquiv a j).symm (Sum.inr ⟨b, e, q⟩) = e.toPath.comp q :=
  (rfl)

/-- **The first-arrow recursion for path counts.** The paths `a → j` are the trivial one, present
exactly when `a = j`, together with an arrow `a ⟶ b` and a path `b → j`. All three cardinalities
are honest counts only when the paths into `j` are finite, which is what the hypothesis
`[∀ b, Finite (Quiver.Path b j)]` provides. The only arrows counted are those out of `a`, so
`[∀ b, Finite (a ⟶ b)]` suffices for the arrow factors.

This is the mirror image of `TauCeti.card_path_eq_ite_add_sum_lastArrow`. -/
theorem card_path_eq_ite_add_sum_firstArrow [DecidableEq V] [Fintype V] (a : V)
    [∀ b : V, Finite (a ⟶ b)] (j : V) [∀ b : V, Finite (Quiver.Path b j)] :
    Nat.card (Quiver.Path a j)
      = (if a = j then 1 else 0)
        + ∑ b : V, Nat.card (a ⟶ b) * Nat.card (Quiver.Path b j) := by
  have hsub : Subsingleton (PLift (a = j)) := ⟨fun x y ↦ by cases x; cases y; rfl⟩
  have : Finite (PLift (a = j)) := Finite.of_subsingleton
  have hcard : Nat.card (PLift (a = j)) = if a = j then 1 else 0 := by
    by_cases h : a = j
    · rw [ite_eq_left h]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨h⟩⟩⟩
    · rw [ite_eq_right h]
      have : IsEmpty (PLift (a = j)) := ⟨fun x ↦ h x.down⟩
      exact Nat.card_of_isEmpty
  rw [Nat.card_congr (pathFirstArrowEquiv a j), Nat.card_sum, hcard, Nat.card_sigma]
  exact congrArg _ (Finset.sum_congr rfl fun b _ ↦ Nat.card_prod _ _)

end TauCeti
