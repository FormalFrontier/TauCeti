/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
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
  cases isEmpty_or_nonempty X with
  | inl h =>
      let _ := h
      exact ⟨0, isEmptyElim, isEmptyElim, measurable_of_countable _, isEmptyElim⟩
  | inr h =>
      let _ := h
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
      have hn : 0 < n := by
        obtain ⟨i, -⟩ := hcover (Classical.arbitrary X)
        exact Fin.pos_iff_nonempty.2 ⟨i⟩
      let e : ℕ → X := fun k ↦ if hk : k < n then v ⟨k, hk⟩ else Classical.arbitrary X
      let N := n - 1
      have hN : N < n := Nat.sub_one_lt hn.ne'
      let nearest := MeasureTheory.SimpleFunc.nearestPtInd e N
      set q : X → Fin n := fun x ↦
        ⟨nearest x, (MeasureTheory.SimpleFunc.nearestPtInd_le e N x).trans_lt hN⟩ with hq
      refine ⟨n, v, q, ?_, fun x ↦ ?_⟩
      · refine measurable_to_countable' fun i ↦ ?_
        have hfib : q ⁻¹' {i} = nearest ⁻¹' {i.val} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hq]
          constructor
          · exact fun h ↦ congrArg Fin.val h
          · exact fun h ↦ Fin.ext h
        rw [hfib]
        exact nearest.measurable (MeasurableSet.singleton i.val)
      · obtain ⟨i, hi⟩ := hcover x
        have hle : i.val ≤ N := Nat.le_sub_one_of_lt i.isLt
        have hnear := MeasureTheory.SimpleFunc.edist_nearestPt_le e x hle
        have he : e i.val = v i := by simp [e, i.isLt]
        have hqv : v (q x) = MeasureTheory.SimpleFunc.nearestPt e N x := by
          simp [MeasureTheory.SimpleFunc.nearestPt, hq, nearest, e,
            (MeasureTheory.SimpleFunc.nearestPtInd_le e N x).trans_lt hN]
        rw [← edist_lt_ofReal, hqv, edist_comm]
        exact hnear.trans_lt (edist_lt_ofReal.2 (by simpa [he, dist_comm] using hi))

end TauCeti
