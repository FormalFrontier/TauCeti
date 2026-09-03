/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Energy
public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Frieze--Kannan weak regularity for graphons

This file proves the weak regularity lemma for strict graphons.  Starting from the indiscrete
finite partition, a cut-norm witness for the current block-average defect cuts every part along
two measurable sets.  The common refinement has at most four times as many parts, while the
Pythagoras identity for `graphonPartitionEnergy` and Cauchy--Schwarz show that its energy rises by
at least `ε²`.  Since the energy stays in `[0, 1]`, the process stops after at most
`⌈1 / ε²⌉ + 1` steps.

Null parts need no special case: `Finpartition.bipartition` omits empty sets but retains nonempty
null sets, and `stepGraphonAvg` uses Mathlib's zero set-average convention on their rectangles.

## Main results

* `TauCeti.DenseGraphLimits.exists_refinement_energy_add_sq_le` is the quantitative refinement
  step: a bad cut-norm approximation yields an energy gain of at least `ε²` while multiplying the
  number of parts by at most four;
* `TauCeti.DenseGraphLimits.weak_regularity_frieze_kannan` is the roadmap's Layer-2 weak
  regularity theorem, with complexity `4 ^ (Nat.ceil (1 / ε ^ 2) + 1)`.

## References

* A. Frieze and R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999), 175--220.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* Roadmap: `TauCetiRoadmap/DenseGraphLimits/README.md`, Layer 2 —
  `weak_regularity_frieze_kannan` and its null-cell/energy-increment validation gate.  The theorem
  signature and its `4 ^ (Nat.ceil (1 / ε ^ 2) + 1)` bound are taken from
  `TauCetiRoadmap/DenseGraphLimits/Suggested.lean` (Layer 2).
* The refinement-and-energy iteration follows `Graphon/Regularity.lean` in
  `cameronfreer/graphon` (Apache 2.0) at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, adapted here to Mathlib `Finpartition`, strict
  block-average graphons, and the Pythagoras energy API.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A cut-norm defect larger than `ε` produces a measurable common refinement with at most four
times as many parts and graphon partition energy at least `ε²` larger. -/
theorem exists_refinement_energy_add_sq_le (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε)
    (hbad : ε < cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)) :
    ∃ (Q : Finpartition (Set.univ : Set Ω)) (hQ : ∀ q ∈ Q.parts, MeasurableSet q),
      Q ≤ P ∧ Q.parts.card ≤ 4 * P.parts.card ∧
        graphonPartitionEnergy μ P hP W + ε ^ 2 ≤ graphonPartitionEnergy μ Q hQ W := by
  let D := W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
  obtain ⟨S, T, hS, hT, hrect⟩ := exists_lt_abs_rectIntegral μ D hbad
  have hS_ne : S ≠ ∅ := by
    intro h
    subst S
    simp only [SymmKernel.rectIntegral_empty_left, abs_zero] at hrect
    linarith
  have hT_ne : T ≠ ∅ := by
    intro h
    subst T
    simp only [SymmKernel.rectIntegral_empty_right, abs_zero] at hrect
    linarith
  let PS := Finpartition.bipartition S
  let PT := Finpartition.bipartition T
  let Q := (P ⊓ PS) ⊓ PT
  have hPS : ∀ p ∈ PS.parts, MeasurableSet p := fun _ hp =>
    Finpartition.measurableSet_of_mem_bipartition hS hp
  have hPT : ∀ p ∈ PT.parts, MeasurableSet p := fun _ hp =>
    Finpartition.measurableSet_of_mem_bipartition hT hp
  have hPPS : ∀ q ∈ (P ⊓ PS).parts, MeasurableSet q := fun _ hq =>
    Finpartition.measurableSet_of_mem_inf hP hPS hq
  have hQ : ∀ q ∈ Q.parts, MeasurableSet q := fun _ hq =>
    Finpartition.measurableSet_of_mem_inf hPPS hPT hq
  have hQP : Q ≤ P := le_trans inf_le_left inf_le_left
  have hQS : Q ≤ PS := le_trans inf_le_left inf_le_right
  have hQT : Q ≤ PT := inf_le_right
  have hcard : Q.parts.card ≤ 4 * P.parts.card := by
    calc
      Q.parts.card ≤ (P ⊓ PS).parts.card * PT.parts.card :=
        Finpartition.card_parts_inf_le_mul _ _
      _ ≤ (P.parts.card * PS.parts.card) * PT.parts.card :=
        Nat.mul_le_mul_right _ (Finpartition.card_parts_inf_le_mul P PS)
      _ ≤ (P.parts.card * 2) * 2 := Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Finpartition.card_parts_bipartition_le S))
        (Finpartition.card_parts_bipartition_le T)
      _ = 4 * P.parts.card := by omega
  let pS : PS.parts := ⟨S, Finpartition.mem_bipartition_of_ne_bot hS_ne⟩
  let pT : PT.parts := ⟨T, Finpartition.mem_bipartition_of_ne_bot hT_ne⟩
  have havg :
      (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel.rectIntegral μ S T =
        W.toSymmKernel.rectIntegral μ S T := by
    simpa [pS, pT] using stepGraphonAvg_rectIntegral_of_le_of_le μ pS pT hQ
      hQS hQT W
  let L := (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel -
    (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
  have hLrect : L.rectIntegral μ S T = D.rectIntegral μ S T := by
    simp only [L, D, SymmKernel.rectIntegral_sub, havg]
  have hsq : ε ^ 2 ≤ (D.rectIntegral μ S T) ^ 2 := by
    have : ε ^ 2 < |D.rectIntegral μ S T| ^ 2 :=
      sq_lt_sq' (by linarith [abs_nonneg (D.rectIntegral μ S T)]) hrect
    simpa only [sq_abs] using this.le
  have hgain : ε ^ 2 ≤ l2sq μ L := by
    rw [← hLrect] at hsq
    exact hsq.trans (sq_rectIntegral_le_l2sq μ L S T)
  refine ⟨Q, hQ, hQP, hcard, ?_⟩
  rw [graphonPartitionEnergy_increment μ P Q hP hQ hQP W]
  simpa only [L, add_comm] using add_le_add_left hgain (graphonPartitionEnergy μ P hP W)

/-- The iteration invariant behind `weak_regularity_frieze_kannan`: **at most** `n` applications of
`exists_refinement_energy_add_sq_le` to a measurable partition `P` produce a measurable partition
with at most `4 ^ n` times as many parts, whose block averages either approximate `W` to within `ε`
in cut norm, or carry energy at least `n * ε ^ 2` above `P`'s. The count is only an upper bound
because the induction stops as soon as the cut-norm estimate holds, returning `P` itself; the
energy alternative is what records how many steps were actually taken. The conclusion records only
that part-count bound and that dichotomy — it does **not** assert that the partition produced
refines `P`, since nothing downstream needs it; the refinement relation is available one level
down, from `exists_refinement_energy_add_sq_le`. Applying it to the indiscrete partition with `n`
past `1 / ε ^ 2` makes the energy alternative contradict `graphonPartitionEnergy_le_one`, leaving
the approximation. -/
private theorem exists_partition_cutNorm_le_or_energy_add_mul_sq_le
    (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ (n : ℕ) (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p),
      ∃ (Q : Finpartition (Set.univ : Set Ω)) (hQ : ∀ q ∈ Q.parts, MeasurableSet q),
        Q.parts.card ≤ 4 ^ n * P.parts.card ∧
          (cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel) ≤ ε ∨
            graphonPartitionEnergy μ P hP W + (n : ℝ) * ε ^ 2 ≤
              graphonPartitionEnergy μ Q hQ W) := by
  intro n
  induction n with
  | zero =>
      -- Base case: keep the current partition; the required energy gain is zero.
      intro P hP
      exact ⟨P, hP, by simp, Or.inr (by simp)⟩
  | succ n ih =>
      -- Refinement step: stop if already good, otherwise gain `ε ^ 2` and apply the induction
      -- hypothesis to the refined partition, whose part count has grown by at most a factor four.
      intro P hP
      by_cases hgood :
          cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) ≤ ε
      · refine ⟨P, hP, ?_, Or.inl hgood⟩
        exact Nat.le_mul_of_pos_left _ (by positivity)
      · push Not at hgood
        obtain ⟨Q, hQ, _, hQcard_step, hQenergy⟩ :=
          exists_refinement_energy_add_sq_le μ P hP W hε hgood
        obtain ⟨R, hR, hRcard, hRdichotomy⟩ := ih Q hQ
        have hRbound : R.parts.card ≤ 4 ^ (n + 1) * P.parts.card := by
          calc R.parts.card ≤ 4 ^ n * Q.parts.card := hRcard
            _ ≤ 4 ^ n * (4 * P.parts.card) := Nat.mul_le_mul_left _ hQcard_step
            _ = 4 ^ (n + 1) * P.parts.card := by ring
        rcases hRdichotomy with hRgood | hRenergy
        · exact ⟨R, hR, hRbound, Or.inl hRgood⟩
        · refine ⟨R, hR, hRbound, Or.inr ?_⟩
          push_cast
          nlinarith

/-- **Frieze--Kannan weak regularity.** Every graphon has a measurable block-average step graphon
within `ε` in cut norm, on a partition with at most `4 ^ (⌈1 / ε²⌉ + 1)` parts. -/
theorem weak_regularity_frieze_kannan (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p),
      P.parts.card ≤ 4 ^ (Nat.ceil (1 / ε ^ 2) + 1) ∧
      cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) ≤ ε := by
  let N := Nat.ceil (1 / ε ^ 2) + 1
  -- Instantiate the refinement invariant at the indiscrete partition, then rule out the
  -- energy-growth branch: `N` steps would push the energy past its upper bound of one.
  let P₀ : Finpartition (Set.univ : Set Ω) := ⊤
  have hP₀ : ∀ p ∈ P₀.parts, MeasurableSet p := by
    intro p hp
    have : p = Set.univ := Finset.mem_singleton.mp
      (Finpartition.parts_top_subset (Set.univ : Set Ω) hp)
    subst p
    exact MeasurableSet.univ
  have hP₀_card : P₀.parts.card ≤ 1 :=
    Finset.card_le_one.mpr (Finpartition.parts_top_subsingleton _)
  obtain ⟨Q, hQ, hQcard, hgood | henergy⟩ :=
    exists_partition_cutNorm_le_or_energy_add_mul_sq_le μ W hε N P₀ hP₀
  · refine ⟨Q, hQ, ?_, hgood⟩
    have hbound : Q.parts.card ≤ 4 ^ N := by
      calc Q.parts.card ≤ 4 ^ N * P₀.parts.card := hQcard
        _ ≤ 4 ^ N * 1 := Nat.mul_le_mul_left _ hP₀_card
        _ = 4 ^ N := mul_one _
    simpa [N] using hbound
  · have hQenergy := graphonPartitionEnergy_le_one μ Q hQ W
    have hP₀energy := graphonPartitionEnergy_nonneg μ P₀ hP₀ W
    have hN : 1 < (N : ℝ) * ε ^ 2 := by
      have hceil : 1 / ε ^ 2 ≤ (Nat.ceil (1 / ε ^ 2) : ℕ) := Nat.le_ceil _
      dsimp only [N]
      push_cast
      have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
      calc
        1 = (1 / ε ^ 2) * ε ^ 2 := by field_simp
        _ < ((Nat.ceil (1 / ε ^ 2) : ℕ) + 1 : ℝ) * ε ^ 2 := by nlinarith
    linarith

end DenseGraphLimits

end TauCeti
