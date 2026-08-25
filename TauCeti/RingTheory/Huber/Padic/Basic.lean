/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Ring.Compact
public import TauCeti.RingTheory.Huber.Basic

/-!
# The p-adic integers are a Huber ring, and not a Tate ring

`ℤ_[p]` with its norm topology is a Huber ring, with `(ℤ_[p], (p))` as a pair of definition, and
it is not a Tate ring. It is the roadmap's Layer-0 example after the discrete case, and the first
to separate `TauCeti.Huber.IsHuberRing` from `TauCeti.Huber.IsTateRing`: the units of `ℤ_[p]` are
exactly the elements of norm one, whose powers again have norm one, so no unit is topologically
nilpotent.

## Main definitions

* `TauCeti.Huber.PadicInt.pairOfDefinition`: the pair of definition `(ℤ_[p], (p))`.

## Main results

* `TauCeti.Huber.PadicInt.coe_maximalIdeal_pow`: `(p)ⁿ` is the closed ball of radius `p⁻ⁿ`.
  Openness is Mathlib's `IsLocalRing.isOpen_maximalIdeal_pow`.
* `TauCeti.Huber.PadicInt.isAdic_maximalIdeal`: the norm topology of `ℤ_[p]` is the `(p)`-adic
  topology. Mathlib has `IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p]` but not this comparison of
  topologies, which is what a pair of definition requires.
* `TauCeti.Huber.PadicInt.isHuberRing` and `TauCeti.Huber.PadicInt.not_isTateRing`: the two
  halves of the example.

## Implementation notes

The ring of definition is all of `ℤ_[p]`, so the ideal of definition has to be carried across
`Subring.topEquiv`; `TauCeti.Huber.IsAdic.comap` in `TauCeti/RingTheory/Huber/Basic.lean` is the
general transport that does it.

## Scope

Only `ℤ_[p]` is treated here. The roadmap's remaining Layer-0 examples — `ℚ_[p]` and `F⸨t⸩` are
Tate, and `ℚ_p⟨T₁,…,Tₙ⟩` is complete and strongly noetherian — are not proved in this file.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], §6, where Huber and Tate rings are introduced
  (Proposition and Definition 6.1) and `ℤ_[p]` is the standard example of a Huber ring that
  is not Tate.
-/

public section

open Topology IsLocalRing

namespace TauCeti.Huber

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- The `n`-th power of the maximal ideal of `ℤ_[p]` is the closed ball of radius `p⁻ⁿ`: this is
what ties the norm topology to the `(p)`-adic one. -/
theorem coe_maximalIdeal_pow (n : ℕ) :
    ((maximalIdeal ℤ_[p] ^ n : Ideal ℤ_[p]) : Set ℤ_[p])
      = {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ)} := by
  ext x
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  rw [_root_.PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow,
    ← _root_.PadicInt.norm_le_pow_iff_mem_span_pow]

/-- **The norm topology of `ℤ_[p]` is the `(p)`-adic topology.** -/
theorem isAdic_maximalIdeal : IsAdic (maximalIdeal ℤ_[p]) := by
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ <| mod_cast (Fact.out : p.Prime).one_lt
  rw [isAdic_iff]
  refine ⟨IsLocalRing.isOpen_maximalIdeal_pow ℤ_[p], fun s hs ↦ ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
  refine ⟨n, fun x hx ↦ hball ?_⟩
  rw [coe_maximalIdeal_pow, Set.mem_ofPred_eq] at hx
  refine Metric.mem_ball.mpr (lt_of_le_of_lt ?_ hn)
  simpa [zpow_neg, zpow_natCast, ← inv_pow, dist_eq_norm] using hx

/-- The pair of definition `(ℤ_[p], (p))` exhibiting `ℤ_[p]` as a Huber ring. The ring of
definition is everything, and the ideal of definition is the maximal ideal carried across
`Subring.topEquiv`. -/
noncomputable def pairOfDefinition : PairOfDefinition ℤ_[p] where
  ringOfDefinition := ⊤
  isOpen_ringOfDefinition := by simp
  idealOfDefinition :=
    (maximalIdeal ℤ_[p]).comap (Subring.topEquiv : (⊤ : Subring ℤ_[p]) ≃+* ℤ_[p])
  fg_idealOfDefinition := by
    rw [← Ideal.map_symm]
    exact Ideal.FG.map
      (by rw [_root_.PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _)
      (Subring.topEquiv : (⊤ : Subring ℤ_[p]) ≃+* ℤ_[p]).symm.toRingHom
  isAdic_idealOfDefinition :=
    IsAdic.comap _ Topology.IsInducing.subtypeVal isAdic_maximalIdeal

/-- The ring of definition of `pairOfDefinition` is all of `ℤ_[p]`. -/
@[simp]
theorem pairOfDefinition_ringOfDefinition :
    (pairOfDefinition (p := p)).ringOfDefinition = ⊤ := (rfl)

/-- Membership in the ideal of definition of `pairOfDefinition` is membership in `(p)`.

Stated as a membership characterisation rather than an equation because the type of
`idealOfDefinition` depends on `ringOfDefinition`. -/
@[simp]
theorem mem_pairOfDefinition_idealOfDefinition
    {x : (pairOfDefinition (p := p)).ringOfDefinition} :
    x ∈ (pairOfDefinition (p := p)).idealOfDefinition ↔ (x : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
  simp only [pairOfDefinition]
  exact Ideal.mem_comap

/-- **`ℤ_[p]` is a Huber ring**, with `(ℤ_[p], (p))` as a pair of definition. -/
instance isHuberRing : IsHuberRing ℤ_[p] :=
  ⟨⟨pairOfDefinition⟩⟩

/-- **`ℤ_[p]` is not a Tate ring**: it admits no pseudouniformiser. Together with
`TauCeti.Huber.PadicInt.isHuberRing` this separates `IsHuberRing` from `IsTateRing`. -/
theorem not_isTateRing : ¬ IsTateRing ℤ_[p] := by
  intro h
  obtain ⟨a, ha⟩ := h.exists_isPseudoUniformizer
  have hone : ∀ n : ℕ, ‖a ^ n‖ = 1 := fun n ↦ by
    rw [norm_pow, _root_.PadicInt.isUnit_iff.mp ha.isUnit, one_pow]
  have hnorm : Filter.Tendsto (fun n : ℕ ↦ ‖a ^ n‖) Filter.atTop (nhds ‖(0 : ℤ_[p])‖) :=
    (continuous_norm.tendsto _).comp ha.isTopologicallyNilpotent
  rw [norm_zero, Filter.tendsto_congr hone] at hnorm
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hnorm)

end PadicInt

end TauCeti.Huber
