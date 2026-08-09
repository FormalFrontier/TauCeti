/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Closed
import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Uniformly continuous semigroups

This file proves the bounded-generator characterization of uniformly continuous semigroups. In
the standard semigroup terminology, "uniformly continuous" means that the semigroup is continuous
in operator norm (it does not mean uniform continuity on the unbounded time interval).

For the nontrivial direction, operator-norm continuity makes the normalized local orbit average

`B_t = t⁻¹ ∫₀ᵗ S(s) ds`

arbitrarily close to the identity for small positive `t`. Hence `B_t` is invertible. Its range is
contained in the generator domain by the local-orbit integral identity, so that domain is all of
the Banach space. Conversely, a full-domain generator is bounded by the closed graph theorem, and
generator uniqueness identifies the semigroup with its operator exponential.

## Main results

* `StronglyContinuousSemigroup.domain_eq_top_of_continuousAt_zero`: operator-norm continuity at
  zero implies that the generator has full domain.
* `StronglyContinuousSemigroup.continuousAt_zero_iff_domain_eq_top`: operator-norm continuity at
  zero is equivalent to boundedness of the generator.
* `StronglyContinuousSemigroup.continuous_iff_domain_eq_top`: operator-norm continuity is
  equivalent to boundedness of the generator.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem I.3.7.
-/

public section

noncomputable section

open MeasureTheory NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

private theorem normalizedIntegral_sub_one_eq (S : StronglyContinuousSemigroup X)
    {t : ℝ} (ht : 0 < t) (hint : IntervalIntegrable S.realOperator volume 0 t) :
    t⁻¹ • (∫ s in (0 : ℝ)..t, S.realOperator s) - 1 =
      t⁻¹ • ∫ s in (0 : ℝ)..t, (S.realOperator s - 1) := by
  rw [intervalIntegral.integral_sub hint (continuous_const.intervalIntegrable 0 t),
    intervalIntegral.integral_const, smul_sub, smul_smul, sub_zero,
    inv_mul_cancel₀ ht.ne', one_smul]

private theorem continuous_of_continuousAt_zero (S : StronglyContinuousSemigroup X)
    (hS : ContinuousAt (fun t : NNReal ↦ S t) 0) : Continuous fun t : NNReal ↦ S t := by
  obtain ⟨ω, M, hb⟩ := S.existsGrowthBound
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let C := max ‖S t₀‖ (M * Real.exp (|ω| * t₀)) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hS (ε / C) (div_pos hε hC)
  refine ⟨δ, hδ, fun t ht ↦ ?_⟩
  rcases le_total t₀ t with ht₀t | htt₀
  · have hdiff : S t - S t₀ = (S t₀).comp (S (t - t₀) - 1) := by
      have hmap := S.map_add t₀ (t - t₀)
      rw [add_tsub_cancel_of_le ht₀t] at hmap
      rw [hmap, ContinuousLinearMap.comp_sub]
      congr 1
    have hsmall' : ‖S (t - t₀) - 1‖ < ε / C := by
      simpa only [S.map_zero, ContinuousLinearMap.one_def, dist_eq_norm] using
        hsmall (by simpa [NNReal.dist_eq, NNReal.coe_sub ht₀t] using ht)
    rw [dist_eq_norm, hdiff]
    calc
      ‖(S t₀).comp (S (t - t₀) - 1)‖
          ≤ ‖S t₀‖ * ‖S (t - t₀) - 1‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < C * (ε / C) := by
        gcongr
        dsimp [C]
        linarith [le_max_left ‖S t₀‖ (M * Real.exp (|ω| * t₀))]
      _ = ε := by field_simp
  · have hdiff : S t - S t₀ = (S t).comp (1 - S (t₀ - t)) := by
      have hmap := S.map_add t (t₀ - t)
      rw [add_tsub_cancel_of_le htt₀] at hmap
      rw [hmap, ContinuousLinearMap.comp_sub]
      congr 1
    have hsmall' : ‖1 - S (t₀ - t)‖ < ε / C := by
      rw [← norm_neg, neg_sub]
      simpa only [S.map_zero, ContinuousLinearMap.one_def, dist_eq_norm] using
        hsmall (by simpa [NNReal.dist_eq, NNReal.coe_sub htt₀, abs_sub_comm] using ht)
    have hSt : ‖S t‖ < C := by
      have hω : ω * (t : ℝ) ≤ |ω| * (t₀ : ℝ) := calc
        ω * (t : ℝ) ≤ |ω| * (t : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self ω) t.2
        _ ≤ |ω| * (t₀ : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast htt₀) (abs_nonneg ω)
      have hbound : ‖S t‖ ≤ M * Real.exp (|ω| * t₀) := by
        rw [← S.realOperator_coe]
        exact (hb.bound t t.2).trans (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hω) (zero_le_one.trans hb.one_le))
      dsimp [C]
      linarith [hbound, le_max_right ‖S t₀‖ (M * Real.exp (|ω| * t₀))]
    rw [dist_eq_norm, hdiff]
    calc
      ‖(S t).comp (1 - S (t₀ - t))‖
          ≤ ‖S t‖ * ‖1 - S (t₀ - t)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < C * (ε / C) := by gcongr
      _ = ε := by field_simp

omit [CompleteSpace X] in
/-- **A norm-continuous semigroup stays within any prescribed distance of the identity on a short
enough initial interval.** -/
private theorem exists_pos_forall_norm_realOperator_sub_one_le
    (S : StronglyContinuousSemigroup X)
    (hreal : ContinuousAt (fun t : ℝ ↦ S.realOperator t) 0) {c : ℝ} (hc : 0 < c) :
    ∃ t : ℝ, 0 < t ∧ ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖S.realOperator s - 1‖ ≤ c := by
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp hreal c hc
  refine ⟨δ / 2, half_pos hδ, fun s hs ↦ ?_⟩
  rw [Set.uIoc_of_le (half_pos hδ).le] at hs
  have hsδ : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
    exact hs.2.trans_lt (half_lt_self hδ)
  simpa only [S.realOperator_zero, ContinuousLinearMap.one_def, dist_eq_norm] using
    (hsmall hsδ).le

/-- **The normalized local orbit average inherits any uniform bound on the orbit's distance to
the identity.** -/
private theorem norm_normalizedIntegral_sub_one_le (S : StronglyContinuousSemigroup X)
    {t c : ℝ} (ht : 0 < t) (hint : IntervalIntegrable S.realOperator volume 0 t)
    (hnorm : ∀ s ∈ Set.uIoc (0 : ℝ) t, ‖S.realOperator s - 1‖ ≤ c) :
    ‖t⁻¹ • (∫ s in (0 : ℝ)..t, S.realOperator s) - 1‖ ≤ c := by
  rw [S.normalizedIntegral_sub_one_eq ht hint, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos ht]
  calc
    t⁻¹ * ‖∫ s in (0 : ℝ)..t, (S.realOperator s - 1)‖
        ≤ t⁻¹ * (c * |t - 0|) := by
          gcongr
          exact intervalIntegral.norm_integral_le_of_norm_le_const hnorm
    _ = c := by
          simp only [sub_zero, abs_of_pos ht]
          field_simp

/-- If a strongly continuous semigroup is continuous in operator norm at zero, then every vector
lies in the domain of its generator. -/
theorem domain_eq_top_of_continuousAt_zero (S : StronglyContinuousSemigroup X)
    (hS : ContinuousAt (fun t : NNReal ↦ S t) 0) : S.domain = ⊤ := by
  have hS' := S.continuous_of_continuousAt_zero hS
  have hreal : Continuous fun t : ℝ ↦ S.realOperator t :=
    (hS'.comp continuous_real_toNNReal).congr fun t ↦ (S.realOperator_def t).symm
  obtain ⟨t, ht, hnorm⟩ :=
    S.exists_pos_forall_norm_realOperator_sub_one_le hreal.continuousAt (c := 1 / 2) (by norm_num)
  have hint : IntervalIntegrable S.realOperator volume 0 t := hreal.intervalIntegrable 0 t
  have hB : ‖t⁻¹ • (∫ s in (0 : ℝ)..t, S.realOperator s) - 1‖ < 1 :=
    (S.norm_normalizedIntegral_sub_one_le ht hint hnorm).trans_lt (by norm_num)
  have hBunit : IsUnit (t⁻¹ • ∫ s in (0 : ℝ)..t, S.realOperator s) := by
    have hone_sub : ‖1 - t⁻¹ • (∫ s in (0 : ℝ)..t, S.realOperator s)‖ < 1 := by
      rwa [norm_sub_rev]
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hone_sub
  apply top_unique
  intro y _
  obtain ⟨x, hx⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp hBunit).2 y
  rw [← hx]
  have horbit : (∫ s in (0 : ℝ)..t, S.realOperator s) x =
      ∫ s in Set.Ioc 0 t, S.realOperator s x := by
    rw [ContinuousLinearMap.intervalIntegral_apply hint, intervalIntegral.integral_of_le ht.le]
  rw [smul_apply, horbit]
  exact S.domain.smul_mem t⁻¹ (S.integral_orbit_mem_domain x ht)

/-- If a strongly continuous semigroup is continuous in operator norm, then every vector lies in
the domain of its generator. -/
theorem domain_eq_top_of_continuous (S : StronglyContinuousSemigroup X)
    (hS : Continuous fun t : NNReal ↦ S t) : S.domain = ⊤ :=
  S.domain_eq_top_of_continuousAt_zero hS.continuousAt

private noncomputable def generatorDomainEquivOfDomainEqTop
    (S : StronglyContinuousSemigroup X) (hS : S.domain = ⊤) : X ≃ₗ[ℝ] S.generator.domain :=
  Submodule.topEquiv.symm.trans <| LinearEquiv.ofEq _ _ ((S.generator_domain.trans hS).symm)

private noncomputable def generatorLinearMapOfDomainEqTop (S : StronglyContinuousSemigroup X)
    (hS : S.domain = ⊤) : X →ₗ[ℝ] X :=
  S.generator.toFun.comp (S.generatorDomainEquivOfDomainEqTop hS).toLinearMap

omit [CompleteSpace X] in
@[simp]
private theorem generatorLinearMapOfDomainEqTop_apply (S : StronglyContinuousSemigroup X)
    (hS : S.domain = ⊤) (x : X) (hx : x ∈ S.generator.domain) :
    S.generatorLinearMapOfDomainEqTop hS x =
      S.generator ⟨x, hx⟩ := by
  -- The domain equivalence sends `x` to the same underlying vector; its subtype proof is built
  -- from `hS` rather than `hx`. Exposing the generator applications leaves only proof-irrelevant
  -- equality of these two subtype values.
  change S.generator _ = S.generator _
  congr

omit [CompleteSpace X] in
private theorem generator_eq_toPMap_generatorLinearMapOfDomainEqTop
    (S : StronglyContinuousSemigroup X) (hS : S.domain = ⊤) :
    S.generator = (S.generatorLinearMapOfDomainEqTop hS).toPMap ⊤ := by
  apply LinearPMap.ext
  · simp [hS]
  · intro x hx hg
    simp only [LinearMap.toPMap_domain, LinearMap.toPMap_apply] at hg ⊢
    exact (S.generatorLinearMapOfDomainEqTop_apply hS x hx).symm

private theorem isClosed_graph_generatorLinearMapOfDomainEqTop
    (S : StronglyContinuousSemigroup X) (hS : S.domain = ⊤) :
    IsClosed ((S.generatorLinearMapOfDomainEqTop hS).graph : Set (X × X)) := by
  have hclosed : ((S.generatorLinearMapOfDomainEqTop hS).toPMap ⊤).IsClosed := by
    rw [← S.generator_eq_toPMap_generatorLinearMapOfDomainEqTop hS]
    exact S.isClosed_generator
  rw [LinearPMap.IsClosed] at hclosed
  have hgraph : (((S.generatorLinearMapOfDomainEqTop hS).toPMap ⊤).graph : Set (X × X)) =
      (S.generatorLinearMapOfDomainEqTop hS).graph := by
    ext p
    -- The two graph-membership lemmas use different coercions, so expose their propositions
    -- before applying the corresponding characteristic lemmas.
    change p ∈ ((S.generatorLinearMapOfDomainEqTop hS).toPMap ⊤).graph ↔
      p ∈ (S.generatorLinearMapOfDomainEqTop hS).graph
    rw [LinearPMap.mem_graph_iff, LinearMap.mem_graph_iff]
    constructor
    · rintro ⟨x, hxval, hx⟩
      rw [← hx]
      exact (LinearMap.toPMap_apply (S.generatorLinearMapOfDomainEqTop hS) ⊤ x).trans
        (congrArg (S.generatorLinearMapOfDomainEqTop hS) hxval)
    · intro hp
      exact ⟨⟨p.1, Submodule.mem_top⟩, rfl, hp.symm⟩
  rwa [hgraph] at hclosed

/-- A strongly continuous semigroup is continuous in operator norm at zero if and only if its
generator has full domain. Equivalently, the generator is a bounded operator and the semigroup is
its operator exponential. -/
theorem continuousAt_zero_iff_domain_eq_top (S : StronglyContinuousSemigroup X) :
    ContinuousAt (fun t : NNReal ↦ S t) 0 ↔ S.domain = ⊤ := by
  constructor
  · exact S.domain_eq_top_of_continuousAt_zero
  · intro hS
    let A : X →L[ℝ] X := ContinuousLinearMap.ofIsClosedGraph
      (S.isClosed_graph_generatorLinearMapOfDomainEqTop hS)
    have hgen : S.generator = (A : X →ₗ[ℝ] X).toPMap ⊤ := by
      rw [S.generator_eq_toPMap_generatorLinearMapOfDomainEqTop hS]
      rw [ContinuousLinearMap.coe_ofIsClosedGraph]
    rw [S.eq_ofBounded_of_generator_eq A hgen]
    exact (ofBounded_continuous A).continuousAt

/-- A strongly continuous semigroup is continuous in operator norm if and only if its generator
has full domain. Equivalently, the generator is a bounded operator and the semigroup is its
operator exponential. -/
theorem continuous_iff_domain_eq_top (S : StronglyContinuousSemigroup X) :
    Continuous (fun t : NNReal ↦ S t) ↔ S.domain = ⊤ := by
  rw [← S.continuousAt_zero_iff_domain_eq_top]
  exact ⟨fun h ↦ h.continuousAt, S.continuous_of_continuousAt_zero⟩

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
