/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Identity
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Group

/-!
# The double cosets of a point stabilizer in a symmetric group

Let `α` be a type with at least two elements and let `x₀ : α`.  The stabilizer of `x₀` in
`Equiv.Perm α` has exactly two double cosets: a permutation either fixes `x₀` or does not, and
each of the two possibilities is a single class.  Fixing `x₀` is membership in the stabilizer, so
that case is the identity double coset; and if `σ` and `τ` both move `x₀` then the transposition
of `σ x₀` and `τ x₀` fixes `x₀` and carries the one onto the other.

## Main statements

* `TauCeti.doubleCoset_rel_stabilizer_of_ne_of_ne`: the permutations moving `x₀` form a single
  double coset.
* `TauCeti.doubleCosetMk_stabilizer_eq_one_iff`: a double coset of the stabilizer of `x₀` is the
  identity one exactly when its permutations fix `x₀`.
* `TauCeti.card_doubleCosetQuotient_stabilizer`: a point stabilizer of a nontrivial `α` has
  exactly two double cosets in `Equiv.Perm α`.

## Implementation notes

`TauCeti.doubleCoset_rel_stabilizer_of_ne_of_ne` is stated on the relation `DoubleCoset.setoid` and
transported to the quotient with `Quotient.sound'`, because `DoubleCoset.Quotient` is a plain
definition that `rw` will not see through.

The count is proved by hand rather than through `TauCeti.doubleCosetEquivOrbitQuotient`, which
reads the same two classes as the two orbits of `Equiv.Perm α` on ordered pairs of points: the
transposition exhibiting the second class is shorter than the transport.
-/

public section

open MulAction

namespace TauCeti

variable {α : Type*} (x₀ : α)

/-- **The permutations moving `x₀` form a single double coset.**  If `σ` and `τ` both move `x₀`
then the transposition of `σ x₀` and `τ x₀` fixes `x₀` and carries the one onto the other. -/
theorem doubleCoset_rel_stabilizer_of_ne_of_ne {σ τ : Equiv.Perm α} (hσ : σ x₀ ≠ x₀)
    (hτ : τ x₀ ≠ x₀) :
    DoubleCoset.setoid (↑(stabilizer (Equiv.Perm α) x₀)) (↑(stabilizer (Equiv.Perm α) x₀)) σ τ :=
    by
  classical
  have hax₀ : Equiv.swap (σ x₀) (τ x₀) x₀ = x₀ :=
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hσ) (Ne.symm hτ)
  rw [DoubleCoset.rel_iff]
  refine ⟨Equiv.swap (σ x₀) (τ x₀), mem_stabilizer_iff.mpr hax₀,
    σ⁻¹ * (Equiv.swap (σ x₀) (τ x₀))⁻¹ * τ, mem_stabilizer_iff.mpr ?_, by group⟩
  simp

/-- A double coset of the stabilizer of `x₀` is the identity one exactly when its permutations fix
`x₀`.  This is `TauCeti.doubleCosetMk_eq_mk_one_iff_mem` for the stabilizer, whose membership
condition is fixing `x₀`.

Not a `simp` lemma: `TauCeti.doubleCosetMk_eq_mk_one_iff_mem` and `MulAction.mem_stabilizer_iff`
are both `simp` lemmas and between them already rewrite this left-hand side to this right-hand
side, so tagging this specialisation fails the `simpNF` linter with "simp can prove this". -/
theorem doubleCosetMk_stabilizer_eq_one_iff {σ : Equiv.Perm α} :
    DoubleCoset.mk (stabilizer (Equiv.Perm α) x₀) (stabilizer (Equiv.Perm α) x₀) σ =
        DoubleCoset.mk (stabilizer (Equiv.Perm α) x₀) (stabilizer (Equiv.Perm α) x₀) 1 ↔
      σ x₀ = x₀ :=
  (doubleCosetMk_eq_mk_one_iff_mem _ σ).trans mem_stabilizer_iff

/-- **A point stabilizer has exactly two double cosets.**  The identity double coset is the
stabilizer itself, and every permutation moving `x₀` lies in the other one; a nontrivial `α`
supplies such a permutation. -/
theorem card_doubleCosetQuotient_stabilizer [Nontrivial α] :
    Nat.card (DoubleCoset.Quotient (↑(stabilizer (Equiv.Perm α) x₀))
      (↑(stabilizer (Equiv.Perm α) x₀) : Set (Equiv.Perm α))) = 2 := by
  classical
  obtain ⟨y, hy⟩ := exists_ne x₀
  have hswap : Equiv.swap x₀ y x₀ ≠ x₀ := by
    rw [Equiv.swap_apply_left]
    exact hy
  rw [Nat.card_eq_two_iff' (DoubleCoset.mk _ _ 1)]
  refine ⟨DoubleCoset.mk _ _ (Equiv.swap x₀ y),
    fun h => hswap ((doubleCosetMk_stabilizer_eq_one_iff x₀).mp h), fun q hq => ?_⟩
  induction q using Quotient.inductionOn with
  | h σ =>
    exact Quotient.sound' (doubleCoset_rel_stabilizer_of_ne_of_ne x₀
      (fun h => hq ((doubleCosetMk_stabilizer_eq_one_iff x₀).mpr h)) hswap)

end TauCeti
