/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting the elements of a cyclic group whose order is a multiple of `f`

In a finite cyclic group, the number of elements whose order is divisible by `f` is the sum of
`φ d` over the divisors `d` of the group order that `f` divides.

Mathlib counts elements of an *exact* order: `IsCyclic.card_orderOf_eq_totient` says there are
`φ d` of them for each `d` dividing the group order. Summing that over the divisors selected by
`f` is the whole content here.

## Main results

* `IsCyclic.card_filter_dvd_orderOf`, and its additive counterpart: the count is `∑ φ d`
  over the divisors `d` of the group order with `f ∣ d`.
-/

public section

open Finset Nat

variable {α : Type*} [Group α] [Fintype α] [IsCyclic α]

/-- **The elements of a cyclic group whose order is a multiple of `f`, counted by order.**
Each divisor `d` of the group order contributes its `φ d` elements of order exactly `d`, and the
condition `f ∣ orderOf τ` keeps precisely the divisors that `f` divides. -/
@[to_additive
/-- **The elements of a finite additive cyclic group whose order is a multiple of `f`, counted by
order.** Each divisor `d` of the group order contributes its `φ d` elements of `addOrderOf`
exactly `d`, and the condition `f ∣ addOrderOf τ` keeps precisely the divisors that `f`
divides. -/]
theorem IsCyclic.card_filter_dvd_orderOf (f : ℕ) :
    #{τ : α | f ∣ orderOf τ} =
      ∑ d ∈ {d ∈ (Fintype.card α).divisors | f ∣ d}, φ d := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun τ : α ↦ orderOf τ)
    (t := {d ∈ (Fintype.card α).divisors | f ∣ d})]
  · refine sum_congr rfl fun d hd ↦ ?_
    rw [mem_filter, Nat.mem_divisors] at hd
    have hfib : Finset.filter (fun a : α ↦ orderOf a = d)
          (Finset.filter (fun τ : α ↦ f ∣ orderOf τ) Finset.univ)
        = Finset.filter (fun a : α ↦ orderOf a = d) Finset.univ := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hd.2, h⟩⟩
    rw [hfib, IsCyclic.card_orderOf_eq_totient hd.1.1]
  · intro τ hτ
    rw [mem_coe, mem_filter] at hτ
    rw [mem_coe, mem_filter, Nat.mem_divisors]
    exact ⟨⟨orderOf_dvd_card, Fintype.card_ne_zero⟩, hτ.2⟩
