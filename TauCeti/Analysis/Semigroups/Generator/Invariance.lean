/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic

/-!
# Invariance of the generator domain

This file proves that every operator of a strongly continuous semigroup preserves the domain
of its infinitesimal generator and commutes with the generator there.

## References

The argument follows Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Lemma II.1.3(ii): apply the bounded semigroup operator to the defining difference-quotient
limit.
-/

public section

noncomputable section

open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

omit [CompleteSpace X] in
/-- The difference quotient based at `S s x` is `S s` applied to the difference quotient
based at `x`. -/
private theorem tendsto_genQuot_apply (S : StronglyContinuousSemigroup X) (s : ℝ≥0) {x y : X}
    (h : Filter.Tendsto (fun t => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds y)) :
    Filter.Tendsto (fun t => (1 / t) • (S.realOperator t (S s x) - S s x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (S s y)) := by
  refine ((S s).continuous.continuousAt.tendsto.comp h).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 ≤ t := ht.le
  have hcomm : S.realOperator t (S s x) = S s (S.realOperator t x) := by
    rw [← Real.coe_toNNReal t ht0, S.realOperator_coe]
    rw [← S.map_add_apply, add_comm, S.map_add_apply]
  simp only [Function.comp_apply, hcomm, map_smul, map_sub]

omit [CompleteSpace X] in
/-- Every semigroup operator preserves the domain of the infinitesimal generator. -/
theorem map_mem_domain (S : StronglyContinuousSemigroup X) (s : ℝ≥0) {x : X} (hx : x ∈ S.domain) :
    S s x ∈ S.domain := by
  rw [S.mem_domain_iff_tendsto] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  exact ⟨S s y, S.tendsto_genQuot_apply s hy⟩

omit [CompleteSpace X] in
/-- The infinitesimal generator commutes with every semigroup operator on its domain. -/
theorem generator_map (S : StronglyContinuousSemigroup X) (s : ℝ≥0) (x : S.domain) :
    S.generator ⟨S s x, by
      rw [S.generator_domain]
      exact S.map_mem_domain s x.property⟩ =
      S s (S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩) := by
  apply S.generator_eq_of_tendsto (S.map_mem_domain s x.property)
  exact S.tendsto_genQuot_apply s (S.generator_tendsto x)

omit [CompleteSpace X] in
/-- Real-time form of domain invariance at nonnegative times. -/
theorem realOperator_mem_domain (S : StronglyContinuousSemigroup X) {s : ℝ} (hs : 0 ≤ s)
    {x : X} (hx : x ∈ S.domain) :
    S.realOperator s x ∈ S.domain := by
  rw [← Real.coe_toNNReal s hs, S.realOperator_coe]
  exact S.map_mem_domain s.toNNReal hx

omit [CompleteSpace X] in
/-- Real-time form of generator commutation at nonnegative times. -/
theorem realOperator_generator_map (S : StronglyContinuousSemigroup X) {s : ℝ} (hs : 0 ≤ s)
    (x : S.domain) :
    S.generator ⟨S.realOperator s x, by
      rw [S.generator_domain]
      exact S.realOperator_mem_domain hs x.property⟩ =
      S.realOperator s (S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩) := by
  have hop : S.realOperator s = S s.toNNReal := by
    rw [← S.realOperator_coe, Real.coe_toNNReal s hs]
  calc
    _ = S.generator ⟨S s.toNNReal x, by
        rw [S.generator_domain]
        exact S.map_mem_domain s.toNNReal x.property⟩ := by
      apply congrArg S.generator
      apply Subtype.ext
      exact congrArg (fun f : X →L[ℝ] X => f x) hop
    _ = S s.toNNReal (S.generator ⟨x, by
        rw [S.generator_domain]
        exact x.property⟩) := S.generator_map s.toNNReal x
    _ = _ := by rw [← hop]

end StronglyContinuousSemigroup

end TauCeti.Semigroups
