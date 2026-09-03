/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Infima of a lower semicontinuous function over a compact factor

A lower semicontinuous function on a nonempty compact space attains its infimum, and the partial
infimum `y ↦ ⨅ x, f (x, y)` of a jointly lower semicontinuous function over a compact first factor
is again lower semicontinuous.

The first statement is recorded here as an equation rather than as `IsMinOn` because that is the
form the second needs: proving lower semicontinuity means turning a strict lower bound valid at
every point of the compact factor into a strict lower bound for the infimum itself, and attainment
is what performs that step. Only lower semicontinuity of `f` is used, so no continuity,
metrizability or countability hypothesis appears, and the order `β` carries no topology of its own.

Mathlib has `LowerSemicontinuousOn.exists_isMinOn`, the extreme value theorem for lower
semicontinuous functions, but nothing about infima over a compact factor of a product: its
semicontinuity operations combine functions on a fixed domain, and the corresponding
`lowerSemicontinuous_iInf` is false without compactness: arbitrary infima do not preserve lower
semicontinuity. What an infimum does preserve is upper semicontinuity, of upper semicontinuous
and in particular of continuous functions, which is `upperSemicontinuous_iInf`.

## Main results

* `TauCeti.exists_iInf_eq_of_lowerSemicontinuous`: on a nonempty compact space, a lower
  semicontinuous function attains its infimum.
* `TauCeti.lowerSemicontinuous_iInf_of_compactSpace`: the partial infimum of a jointly lower
  semicontinuous function over a compact first factor is lower semicontinuous.
-/

public section

open Set

namespace TauCeti

variable {X Y β : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLinearOrder β]

/-- A lower semicontinuous function on a nonempty compact space attains its infimum. -/
theorem exists_iInf_eq_of_lowerSemicontinuous [CompactSpace X] [Nonempty X] {f : X → β}
    (hf : LowerSemicontinuous f) : ∃ x₀, ⨅ x, f x = f x₀ := by
  obtain ⟨x₀, -, hx₀⟩ :=
    (hf.lowerSemicontinuousOn univ).exists_isMinOn univ_nonempty isCompact_univ
  exact ⟨x₀, le_antisymm (iInf_le _ x₀) (le_iInf fun x => hx₀ (mem_univ x))⟩

/-- Restricting a jointly lower semicontinuous function to a horizontal slice keeps it lower
semicontinuous. -/
private theorem lowerSemicontinuous_slice {f : X × Y → β} (hf : LowerSemicontinuous f) (y : Y) :
    LowerSemicontinuous fun x : X => f (x, y) :=
  hf.comp (continuous_id.prodMk continuous_const)

/-- The infimum of a jointly lower semicontinuous function over a compact first factor is a lower
semicontinuous function of the second variable.

Compactness is what makes this true: an arbitrary infimum of lower semicontinuous functions need
not be lower semicontinuous. -/
theorem lowerSemicontinuous_iInf_of_compactSpace [CompactSpace X] {f : X × Y → β}
    (hf : LowerSemicontinuous f) : LowerSemicontinuous fun y => ⨅ x, f (x, y) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · simpa only [iInf_of_isEmpty] using lowerSemicontinuous_const
  intro y₀ b hb
  -- The strict lower bound `b` holds on the whole compact slice `X × {y₀}`.
  have hsub : (univ : Set X) ×ˢ ({y₀} : Set Y) ⊆ f ⁻¹' Ioi b := by
    rintro ⟨x, y⟩ ⟨-, hy⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact lt_of_lt_of_le hb (iInf_le _ x)
  obtain ⟨u, v, -, hv, hu, hy₀v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton (hf.isOpen_preimage b) hsub
  refine Filter.eventually_of_mem (hv.mem_nhds (hy₀v rfl)) fun y hy => ?_
  -- The bound holds at every point of the slice over `y`, and the infimum there is attained.
  obtain ⟨x₀, hx₀⟩ :=
    exists_iInf_eq_of_lowerSemicontinuous (lowerSemicontinuous_slice hf y)
  exact lt_of_lt_of_le (huv ⟨hu (mem_univ x₀), hy⟩) hx₀.ge

end TauCeti
