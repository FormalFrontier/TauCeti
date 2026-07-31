/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# The last arrow of a path

A path `i → b` in a quiver is either trivial, which forces `i = b`, or a path `i → a` followed by a
last arrow `a ⟶ b`. This file records that dichotomy as an equivalence and reads off the resulting
recursion for the number of paths out of a fixed vertex.

## Main definitions

* `TauCeti.pathLastArrowEquiv`: the last-arrow decomposition
  `Path i b ≃ PLift (i = b) ⊕ Σ a, Path i a × (a ⟶ b)`.

## Main results

* `TauCeti.card_path_eq_ite_add_sum`: the path count `#(i → b)` equals `∑ₐ #(i → a) · #(a ⟶ b)`,
  plus `1` when `i = b` for the trivial path.

## Implementation notes

The equivalence is the constructor dichotomy of `Quiver.Path`: `Quiver.Path.nil` is the left summand
and `Quiver.Path.cons` the right one, so both directions are definitional matches. The proposition
`i = b` is wrapped in `PLift` only to make the summand a type, so that `Nat.card` applies. The
`simp` lemmas `TauCeti.pathLastArrowEquiv_nil`, `TauCeti.pathLastArrowEquiv_cons`,
`TauCeti.pathLastArrowEquiv_symm_inl` and `TauCeti.pathLastArrowEquiv_symm_inr` record those matches
on both summands, so consumers compute with the equivalence without unfolding it.

The dual decomposition, by the *first* arrow of a path, is not available in this form: the
recursion of `Quiver.Path` is on the target vertex, so the first arrow is not visible to a match.
Mathlib's `Quiver.Path.length_ne_zero_iff_eq_comp` supplies its existence half.

## References

The path count is the combinatorial input to the Euler-form identity for the projective
representation at a vertex, Layer 4 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V]

/-- **The last-arrow decomposition of a path.** A path `i → b` is either trivial, and then `i = b`,
or a path `i → a` followed by a last arrow `a ⟶ b`, uniquely so. -/
@[expose] def pathLastArrowEquiv (i b : V) :
    Quiver.Path i b ≃ (PLift (i = b) ⊕ Σ a : V, Quiver.Path i a × (a ⟶ b)) where
  toFun p := match b, p with
    | _, .nil => Sum.inl ⟨rfl⟩
    | _, .cons q e => Sum.inr ⟨_, q, e⟩
  invFun x := match x with
    | Sum.inl ⟨rfl⟩ => Quiver.Path.nil
    | Sum.inr ⟨_, q, e⟩ => q.cons e
  left_inv p := by cases p <;> rfl
  right_inv x := by
    cases x with
    | inl h => cases h with | up h => subst h; rfl
    | inr y => obtain ⟨a, p, e⟩ := y; rfl

/-- The trivial path is the left summand of the last-arrow decomposition. -/
@[simp]
theorem pathLastArrowEquiv_nil (i : V) :
    pathLastArrowEquiv i i Quiver.Path.nil = Sum.inl ⟨rfl⟩ :=
  rfl

/-- A path with a last arrow is the right summand of the last-arrow decomposition. -/
@[simp]
theorem pathLastArrowEquiv_cons {i a b : V} (p : Quiver.Path i a) (e : a ⟶ b) :
    pathLastArrowEquiv i b (p.cons e) = Sum.inr ⟨a, p, e⟩ :=
  rfl

/-- The left summand of the last-arrow decomposition recomposes to the trivial path. -/
@[simp]
theorem pathLastArrowEquiv_symm_inl (i : V) :
    (pathLastArrowEquiv i i).symm (Sum.inl ⟨rfl⟩) = Quiver.Path.nil :=
  rfl

/-- The right summand of the last-arrow decomposition recomposes by appending the last arrow. -/
@[simp]
theorem pathLastArrowEquiv_symm_inr {i b : V} (a : V) (p : Quiver.Path i a) (e : a ⟶ b) :
    (pathLastArrowEquiv i b).symm (Sum.inr ⟨a, p, e⟩) = p.cons e :=
  rfl

/-- **The last-arrow recursion for path counts.** The paths `i → b` are the trivial one, present
exactly when `i = b`, together with a path `i → a` and an arrow `a ⟶ b`. All three cardinalities
are honest counts only when the paths out of `i` are finite, which is what the hypothesis
`[∀ a, Finite (Quiver.Path i a)]` provides. -/
theorem card_path_eq_ite_add_sum [DecidableEq V] [Fintype V] [∀ a b : V, Finite (a ⟶ b)]
    (i : V) [∀ a : V, Finite (Quiver.Path i a)] (b : V) :
    Nat.card (Quiver.Path i b)
      = (if i = b then 1 else 0)
        + ∑ a : V, Nat.card (Quiver.Path i a) * Nat.card (a ⟶ b) := by
  haveI hsub : Subsingleton (PLift (i = b)) := ⟨fun x y ↦ by cases x; cases y; rfl⟩
  haveI : Finite (PLift (i = b)) := Finite.of_subsingleton
  have hcard : Nat.card (PLift (i = b)) = if i = b then 1 else 0 := by
    by_cases h : i = b
    · rw [if_pos h]
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨h⟩⟩⟩
    · rw [if_neg h]
      haveI : IsEmpty (PLift (i = b)) := ⟨fun x ↦ h x.down⟩
      exact Nat.card_of_isEmpty
  rw [Nat.card_congr (pathLastArrowEquiv i b), Nat.card_sum, hcard, Nat.card_sigma]
  exact congrArg _ (Finset.sum_congr rfl fun a _ ↦ Nat.card_prod _ _)

end TauCeti
