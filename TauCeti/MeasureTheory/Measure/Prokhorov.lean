/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Weak cluster limits of tight finite measures

This file contains a generic finite-measure extraction lemma based on Mathlib's Prokhorov
compactness theorem for finite measures. It has no real-line support condition and no
normalization step: tightness and a uniform mass bound place the sequence in a compact set of
`FiniteMeasure`s, and compactness gives a weak cluster limit.

## Main declarations

* `TauCeti.finite_measure_cluster_limit`: a tight, mass-bounded sequence of finite measures has a
  weak cluster limit along an ultrafilter below `atTop`.
* `TauCeti.finite_measure_subseq_limit`: the corresponding subsequence form when the weak topology
  on `FiniteMeasure α` is first-countable.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal Topology

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [T2Space α] [BorelSpace α]

omit [T2Space α] [BorelSpace α] in
/-- A tight family of measures admits a **monotone** exhaustion by compact sets whose complements
carry uniformly small mass: given tolerances `u j > 0`, there are compact `K j`, increasing in `j`,
with `σ n (K j)ᶜ ≤ u j` for every `n`. Accumulating the sets supplied by tightness is what turns
the unrelated compact sets into the monotone family Mathlib's Prokhorov criterion expects. -/
private lemma exists_monotone_isCompact_measure_compl_le
    {σ : ℕ → Measure α} (hTight : IsTightMeasureSet (Set.range σ))
    {u : ℕ → ℝ≥0} (hu_pos : ∀ j, 0 < u j) :
    ∃ K : ℕ → Set α, Monotone K ∧ (∀ j, IsCompact (K j)) ∧
      ∀ j n, (σ n) (K j)ᶜ ≤ (u j : ENNReal) := by
  have hchoose : ∀ j, ∃ K : Set α, IsCompact K ∧ ∀ n, (σ n) Kᶜ ≤ (u j : ENNReal) := by
    intro j
    obtain ⟨K, hK, htail⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hTight
        (u j : ENNReal) (by exact_mod_cast hu_pos j)
    exact ⟨K, hK, fun n => htail (σ n) (Set.mem_range_self n)⟩
  choose K hK_comp hK_tail using hchoose
  refine ⟨Set.accumulate K, Set.monotone_accumulate,
    fun j => isCompact_accumulate hK_comp j, fun j n => ?_⟩
  exact (measure_mono (compl_subset_compl.mpr (Set.subset_accumulate (s := K) (x := j)))).trans
    (hK_tail j n)

/-- A tight, uniformly mass-bounded sequence of finite measures has a weak cluster limit.

Given tightness of the sequence and a common total-mass bound, the conclusion is a finite limiting
measure with the same mass bound and weak convergence of all bounded-continuous test-function
integrals along an ultrafilter `U ≤ atTop`; no first-countability assumption on `FiniteMeasure α`
is needed. -/
lemma finite_measure_cluster_limit
    (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal))
    (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (U : Ultrafilter ℕ), (U : Filter ℕ) ≤ atTop ∧ IsFiniteMeasure μ₀ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun n => ∫ x, g x ∂(σ n)) (U : Filter ℕ)
          (nhds (∫ x, g x ∂μ₀)) := by
  -- First coerce the sequence to `FiniteMeasure`; the uniform mass bound supplies finiteness.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  -- Choose a positive sequence decreasing to zero; these values are the tail tolerances in
  -- Prokhorov's compact set criterion.
  obtain ⟨u, -, hu_pos, hu_lim⟩ :
      ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto 0
  obtain ⟨K, hKmono, hK_comp, hK_tail⟩ :=
    exists_monotone_isCompact_measure_compl_le hTight hu_pos
  let S : Set (FiniteMeasure α) := {μ | μ.mass ≤ C ∧ ∀ j, μ (K j)ᶜ ≤ u j}
  have hcompact : IsCompact S := by
    simpa [S] using
      isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le
        (E := α) (C := C) (u := u) (K := K) hu_lim hK_comp (Or.inr hKmono)
  -- The finite-measure sequence lies in the compact Prokhorov set.
  have hσ_mem : ∀ n, σf n ∈ S := by
    refine fun n => ⟨?_, fun j => ?_⟩
    · dsimp [σf, S, FiniteMeasure.mass]
      exact ENNReal.coe_le_coe.mp (by simpa using hmass n)
    · exact ENNReal.coe_le_coe.mp (by simpa [σf] using hK_tail j n)
  -- Compactness gives a cluster point and an ultrafilter below `atTop` along which `σf`
  -- converges weakly.
  have hmap_le : map σf atTop ≤ 𝓟 S :=
    tendsto_principal.mpr (Eventually.of_forall hσ_mem)
  obtain ⟨μf, hμfS, hcluster⟩ := hcompact hmap_le
  have hmapcluster : MapClusterPt μf atTop σf := hcluster
  obtain ⟨U, hUle, hUtend⟩ := mapClusterPt_iff_ultrafilter.mp hmapcluster
  refine ⟨(μf : Measure α), U, hUle, inferInstance, ?_, ?_⟩
  -- Finally unwrap the compact-set membership into the mass bound and weak convergence of
  -- integrals against bounded continuous test functions.
  · have hle : (μf.mass : ENNReal) ≤ (C : ENNReal) := ENNReal.coe_le_coe.mpr hμfS.1
    rw [← FiniteMeasure.ennreal_mass]
    simpa using hle
  · intro g
    have hweak :=
      (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hUtend) g
    simpa [σf] using hweak

/-- Sequential form of `finite_measure_cluster_limit` when `FiniteMeasure α` is first-countable. -/
lemma finite_measure_subseq_limit
    [FirstCountableTopology (FiniteMeasure α)]
    (σ : ℕ → Measure α) (C : ℝ≥0)
    (hmass : ∀ n, (σ n) univ ≤ (C : ENNReal))
    (hTight : IsTightMeasureSet (Set.range σ)) :
    ∃ (μ₀ : Measure α) (φ : ℕ → ℕ), IsFiniteMeasure μ₀ ∧ StrictMono φ ∧
      μ₀ univ ≤ (C : ENNReal) ∧
      ∀ g : BoundedContinuousFunction α ℝ,
        Tendsto (fun k => ∫ x, g x ∂(σ (φ k))) atTop
          (nhds (∫ x, g x ∂μ₀)) := by
  -- Start from the ultrafilter cluster limit supplied by compactness.
  obtain ⟨μ₀, U, hUle, hμ₀_fin, hmass_μ₀, hweakU⟩ :=
    finite_measure_cluster_limit (α := α) σ C hmass hTight
  -- Repackage the sequence and limit as finite measures so that weak convergence can be read
  -- through bounded-continuous integrals.
  have hfin : ∀ n, IsFiniteMeasure (σ n) := fun n =>
    ⟨(hmass n).trans_lt ENNReal.coe_lt_top⟩
  let σf : ℕ → FiniteMeasure α := fun n => ⟨σ n, hfin n⟩
  let μf : FiniteMeasure α := ⟨μ₀, hμ₀_fin⟩
  have hUtend : Tendsto σf (U : Filter ℕ) (nhds μf) := by
    rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa [σf, μf] using hweakU g
  have hclusterU : MapClusterPt μf (U : Filter ℕ) σf := hUtend.mapClusterPt
  have hcluster : MapClusterPt μf atTop σf := hclusterU.mono hUle
  -- First countability turns the cluster point into an ordinary subsequential limit.
  obtain ⟨φ, hφ, hφ_tendsto⟩ := hcluster.tendsto_subseq
  refine ⟨μ₀, φ, hμ₀_fin, hφ, hmass_μ₀, fun g => ?_⟩
  have hweak :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hφ_tendsto) g
  -- `hweak` is stated through the `FiniteMeasure` integral coercion; `change` reads it back as
  -- the plain Bochner integral against the underlying measures, which is the statement wanted.
  change Tendsto (fun k => ∫ x, g x ∂σ (φ k)) atTop (𝓝 (∫ x, g x ∂μ₀)) at hweak
  exact hweak

end TauCeti
