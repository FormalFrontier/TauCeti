/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Measurable discretization of totally bounded pseudometric spaces

This file provides a finite measurable approximation of a totally bounded pseudometric space whose
open sets are measurable.

## Main statements

* `TauCeti.exists_measurable_dist_lt` — a totally bounded pseudometric space admits a measurable map
  to a finite type whose indexed approximation point is uniformly close to every point.
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

universe u

/-- A totally bounded pseudometric space admits, up to any positive error, an indexed finite family
of approximation points and a measurable map assigning every point to a nearby one. -/
theorem exists_measurable_dist_lt (X : Type u) [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (hX : TotallyBounded (Set.univ : Set X)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (v : Fin n → X) (q : X → Fin n), Measurable q ∧ ∀ x, dist x (v (q x)) < δ := by
  classical
  obtain ⟨s, -, hs, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded (s := (Set.univ : Set X))
      hX δ hδ
  let t := hs.toFinset
  set n := t.card
  set v : Fin n → X := fun i ↦ (t.equivFin.symm i : X) with hv
  have hcover : ∀ x : X, ∃ i : Fin n, dist x (v i) < δ := by
    intro x
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (hcover (Set.mem_univ x))
    have hzt : z ∈ t := by simpa [t] using hz
    exact ⟨t.equivFin ⟨z, hzt⟩, by simpa [hv] using hxz⟩
  set S : X → Finset (Fin n) := fun x ↦ {i | dist x (v i) < δ} with hS
  have hSne : ∀ x, (S x).Nonempty := fun x ↦ by
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨i, by simpa [hS] using hi⟩
  set q : X → Fin n := fun x ↦ (S x).min' (hSne x)
  have hmemq : ∀ x, dist x (v (q x)) < δ := fun x ↦ by
    simpa [hS] using (S x).min'_mem (hSne x)
  refine ⟨n, v, q, ?_, hmemq⟩
  refine measurable_to_countable' fun i ↦ ?_
  have hfib : q ⁻¹' {i} =
      Metric.ball (v i) δ \ ⋃ k ∈ Set.Iio i, Metric.ball (v k) δ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Metric.mem_ball]
    constructor
    · rintro rfl
      refine ⟨hmemq x, fun hmem ↦ ?_⟩
      obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.1 hmem
      have hle : q x ≤ k := (S x).min'_le k (by simpa [hS] using Metric.mem_ball.1 hxk)
      exact absurd (Set.mem_Iio.1 hk) hle.not_gt
    · rintro ⟨hi, hlt⟩
      have hmem : i ∈ S x := by simpa [hS] using hi
      refine le_antisymm ((S x).min'_le i hmem) (not_lt.1 fun hcon ↦ hlt ?_)
      exact Set.mem_iUnion₂.2 ⟨q x, Set.mem_Iio.2 hcon, Metric.mem_ball.2 (hmemq x)⟩
  rw [hfib]
  exact measurableSet_ball.diff
    (MeasurableSet.biUnion (Set.to_countable _) fun _ _ ↦ measurableSet_ball)

end TauCeti
