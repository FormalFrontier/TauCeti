/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Abel

/-!
# Summing a product after transposing two indices

`TauCeti.sum_mul_swap` compares `∑ k ∈ s, f k * g (Equiv.swap x y k)` with `∑ k ∈ s, f k * g k`:
away from `x` and `y` the two sums agree termwise, so they differ only in that the terms
`f x * g x` and `f y * g y` are replaced by `f x * g y` and `f y * g x`. The comparison is stated
by adding the two exchanged pairs to the two sides rather than by subtracting them, so that it
holds in a monoid without subtraction -- in particular over `ℕ`, where such a weighted sum is a
convenient numerical measure of an arrangement of labels.
-/

public section

namespace TauCeti

/-- **Transposing two indices of a weighted sum exchanges the two weights.** Every term other than
those at `x` and `y` is unchanged, so adding `f x * g x + f y * g y` to the transposed sum gives
the original sum with `f x * g y + f y * g x` added. -/
theorem sum_mul_swap {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] [Mul M] (f g : ι → M)
    {s : Finset ι} {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (hne : x ≠ y) :
    (∑ k ∈ s, f k * g (Equiv.swap x y k)) + (f x * g x + f y * g y) =
      (∑ k ∈ s, f k * g k) + (f x * g y + f y * g x) := by
  have hsplit : ∀ F : ι → M, ∑ k ∈ s, F k = F x + (F y + ∑ k ∈ (s.erase x).erase y, F k) := by
    intro F
    rw [← Finset.add_sum_erase _ F hx,
      ← Finset.add_sum_erase _ F (Finset.mem_erase.mpr ⟨hne.symm, hy⟩)]
  have htail : ∀ k ∈ (s.erase x).erase y, f k * g (Equiv.swap x y k) = f k * g k := by
    intro k hk
    obtain ⟨hky, hk'⟩ := Finset.mem_erase.mp hk
    rw [Equiv.swap_apply_of_ne_of_ne (Finset.mem_erase.mp hk').1 hky]
  rw [hsplit fun k => f k * g (Equiv.swap x y k), hsplit fun k => f k * g k,
    Finset.sum_congr rfl htail, Equiv.swap_apply_left, Equiv.swap_apply_right]
  abel

end TauCeti
