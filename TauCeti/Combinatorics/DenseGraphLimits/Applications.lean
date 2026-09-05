/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.SmallGraphs
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Extremal inequalities for graphons

This file records the first analytic extremal consequences of the graphon API.  The main results
are Goodman's inequality

`t(K₃, W) ≥ 2 * t(K₂, W)^2 - t(K₂, W)`,

and Sidorenko's inequality for the four-cycle.  Goodman's proof writes the nonnegative integral
`∫ W(x,y) (1 - W(x,z)) (1 - W(y,z))` in two ways and uses Cauchy--Schwarz for the degree
function, followed by Mantel's triangle-free corollary.  The four-cycle proof identifies its
density with the integral of the square of a two-step kernel and applies two second-moment
inequalities.  All statements are for arbitrary probability carriers; no atomlessness or standard
Borel assumption is involved.

They use only the strict graphon carrier and its edge, triangle, and product-integral APIs.

## Main results

* `goodman_triangle_density` — Goodman's lower bound for triangle density;
* `mantel_triangle_free` — a triangle-free graphon has edge density at most `1 / 2`.
* `sidorenko_cycle_four` — the 4-cycle density is at least the fourth power of edge density.

## References

* A. Goodman, "On sets of acquaintances and strangers at a party", *American Mathematical Monthly*
  66 (1959), 778--783; see also L. Lovász, *Large Networks and Graph Limits*, §7.2.
* Y. Zhao, *Graph Theory and Additive Combinatorics*, Cambridge University Press (2023),
  Theorem 5.2.1, [online notes](https://yufeizhao.com/gtacbook/gtacbook.pdf).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private def graphonDegree (W : Graphon Ω μ) (x : Ω) : ℝ := ∫ y, W x y ∂μ

private theorem integrable_graphonDegree (W : Graphon Ω μ) :
    Integrable (graphonDegree W) μ := by
  -- The definition is private so the expected function does not unfold under `simpa` here.
  change Integrable (fun x => ∫ y, W x y ∂μ) μ
  exact (integrable_edge_integrand W).integral_prod_left

private theorem integrable_graphon_slice (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun y => W x y) μ := by
  apply (integrable_const (1 : ℝ)).mono
    ((W.measurable.comp measurable_prodMk_left).aestronglyMeasurable)
  filter_upwards [] with y
  simpa only [Function.comp_apply, Function.uncurry_apply_pair, Real.norm_eq_abs,
    abs_of_nonneg (W.nonneg x y), norm_one] using W.le_one x y

private theorem graphonDegree_nonneg (W : Graphon Ω μ) (x : Ω) : 0 ≤ graphonDegree W x := by
  exact integral_nonneg fun y => W.nonneg x y

private theorem graphonDegree_le_one (W : Graphon Ω μ) (x : Ω) : graphonDegree W x ≤ 1 := by
  have h := integral_mono (integrable_graphon_slice W x) (integrable_const (1 : ℝ))
    (fun y => W.le_one x y)
  simpa [graphonDegree] using h

private theorem integrable_graphonDegree_sq (W : Graphon Ω μ) :
    Integrable (fun x => graphonDegree W x ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono
    ((integrable_graphonDegree W).aestronglyMeasurable.pow 2)
  filter_upwards [] with x
  -- The norm bound is the square of the pointwise `[0, 1]` bound on the degree.
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_one]
  have hsq := mul_self_le_mul_self (graphonDegree_nonneg W x) (graphonDegree_le_one W x)
  simpa [pow_two] using hsq

private theorem integral_graphonDegree_sq_ge (W : Graphon Ω μ) :
    (∫ x, graphonDegree W x ∂μ) ^ 2 ≤ ∫ x, graphonDegree W x ^ 2 ∂μ := by
  have h := TauCeti.MeasureTheory.sq_setIntegral_le_measureReal_mul_setIntegral_sq
    (graphonDegree W) Set.univ (measure_ne_top μ Set.univ)
    (by simpa using integrable_graphonDegree W)
    (by simpa using integrable_graphonDegree_sq W)
  simpa [measureReal_def, IsProbabilityMeasure.measure_univ] using h

private theorem integrable_triple_graphon_product (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω =>
      W p.1 p.2.1 * (1 - W p.1 p.2.2) * (1 - W p.2.1 p.2.2)) (μ.prod (μ.prod μ)) := by
  apply (integrable_const (1 : ℝ)).mono
    (by
      have hxy : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.1) :=
        W.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hxz : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.2) :=
        W.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      have hyz : Measurable (fun p : Ω × Ω × Ω => W p.2.1 p.2.2) :=
        W.measurable.comp (measurable_fst.comp measurable_snd |>.prodMk
          (measurable_snd.comp measurable_snd))
      exact (hxy.mul ((measurable_const.sub hxz))).mul (measurable_const.sub hyz)
        |>.aestronglyMeasurable)
  filter_upwards [] with p
  have h₁ : 0 ≤ W p.1 p.2.1 := W.nonneg _ _
  have h₂ : W p.1 p.2.1 ≤ 1 := W.le_one _ _
  have h₃ : 0 ≤ 1 - W p.1 p.2.2 := sub_nonneg.mpr (W.le_one _ _)
  have h₄ : 1 - W p.1 p.2.2 ≤ 1 := by linarith [W.nonneg p.1 p.2.2]
  have h₅ : 0 ≤ 1 - W p.2.1 p.2.2 := sub_nonneg.mpr (W.le_one _ _)
  have h₆ : 1 - W p.2.1 p.2.2 ≤ 1 := by linarith [W.nonneg p.2.1 p.2.2]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h₁ h₃) h₅), norm_one]
  exact (mul_le_mul (mul_le_mul h₂ h₄ h₃ (by norm_num)) h₆ h₅ (by norm_num)).trans_eq
    (by ring)

private theorem integrable_triple_graphon_edge (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => W p.1 p.2.1) (μ.prod (μ.prod μ)) := by
  have hm : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.1) :=
    W.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  apply (integrable_const (1 : ℝ)).mono
    hm.aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Function.comp_apply, Function.uncurry_apply_pair, norm_one, Real.norm_eq_abs,
    abs_of_nonneg (W.nonneg _ _)] using W.le_one p.1 p.2.1

private theorem integrable_triple_graphon_two_edges_left (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => W p.1 p.2.1 * W p.1 p.2.2)
      (μ.prod (μ.prod μ)) := by
  apply (integrable_const (1 : ℝ)).mono
    (by
      have hxy : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.1) :=
        W.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hxz : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.2) :=
        W.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
      exact (hxy.mul hxz).aestronglyMeasurable)
  filter_upwards [] with p
  have h₁ := W.nonneg p.1 p.2.1
  have h₂ := W.nonneg p.1 p.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h₁ h₂), norm_one]
  simpa only [one_mul] using mul_le_mul (W.le_one _ _) (W.le_one _ _) h₂ (by norm_num)

private theorem integral_triple_graphon_edge (W : Graphon Ω μ) :
    (∫ p : Ω × Ω × Ω, W p.1 p.2.1 ∂(μ.prod (μ.prod μ))) =
      ∫ x, ∫ y, W x y ∂μ ∂μ := by
  rw [integral_prod _ (integrable_triple_graphon_edge W)]
  simp_rw [integral_fun_fst]
  simp [measureReal_def, IsProbabilityMeasure.measure_univ]

private theorem integral_triple_graphon_two_edges_left (W : Graphon Ω μ) :
    (∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2 ∂(μ.prod (μ.prod μ))) =
      ∫ x, graphonDegree W x ^ 2 ∂μ := by
  rw [integral_prod _ (integrable_triple_graphon_two_edges_left W)]
  simp_rw [integral_prod_mul]
  simp only [graphonDegree, pow_two]

private theorem integrable_pair_graphon_mixed (W : Graphon Ω μ) (x : Ω) :
    Integrable (fun p : Ω × Ω => W x p.1 * W p.1 p.2) (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono
    (by
      have h₁ : Measurable (fun p : Ω × Ω => W x p.1) :=
        W.measurable.comp (measurable_const.prodMk measurable_fst)
      have h₂ : Measurable (fun p : Ω × Ω => W p.1 p.2) :=
        W.measurable
      exact (h₁.mul h₂).aestronglyMeasurable)
  filter_upwards [] with p
  have h₁ := W.nonneg x p.1
  have h₂ := W.nonneg p.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h₁ h₂), norm_one]
  simpa only [one_mul] using mul_le_mul (W.le_one _ _) (W.le_one _ _) h₂ (by norm_num)

private theorem integrable_triple_graphon_two_edges_right (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω × Ω => W p.1 p.2.1 * W p.2.1 p.2.2)
      (μ.prod (μ.prod μ)) := by
  apply (integrable_const (1 : ℝ)).mono
    (by
      have h₁ : Measurable (fun p : Ω × Ω × Ω => W p.1 p.2.1) :=
        W.measurable.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have h₂ : Measurable (fun p : Ω × Ω × Ω => W p.2.1 p.2.2) :=
        W.measurable.comp (measurable_fst.comp measurable_snd |>.prodMk
          (measurable_snd.comp measurable_snd))
      exact (h₁.mul h₂).aestronglyMeasurable)
  filter_upwards [] with p
  have h₁ := W.nonneg p.1 p.2.1
  have h₂ := W.nonneg p.2.1 p.2.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h₁ h₂), norm_one]
  simpa only [one_mul] using mul_le_mul (W.le_one _ _) (W.le_one _ _) h₂ (by norm_num)

private theorem integral_triple_graphon_two_edges_right (W : Graphon Ω μ) :
    (∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.2.1 p.2.2 ∂(μ.prod (μ.prod μ))) =
      ∫ x, graphonDegree W x ^ 2 ∂μ := by
  have hinner (x : Ω) :
      (∫ p : Ω × Ω, W x p.1 * W p.1 p.2 ∂(μ.prod μ)) =
        ∫ y, W x y * graphonDegree W y ∂μ := by
    rw [integral_prod _ (integrable_pair_graphon_mixed W x)]
    simp only [integral_const_mul, graphonDegree]
  rw [integral_prod _ (integrable_triple_graphon_two_edges_right W)]
  simp_rw [hinner]
  have hpair : Integrable (fun p : Ω × Ω => W p.1 p.2 * graphonDegree W p.2) (μ.prod μ) := by
    have hdprod : Integrable (fun p : Ω × Ω => graphonDegree W p.2) (μ.prod μ) :=
      (integrable_graphonDegree W).comp_snd μ
    have h := hdprod.mul_bdd W.measurable.aestronglyMeasurable
      (ae_of_all _ fun p => by
        -- This rewrites the `uncurry W` norm bound supplied by `W.measurable`.
        change ‖W p.1 p.2‖ ≤ 1
        simpa only [Real.norm_eq_abs, abs_of_nonneg (W.nonneg _ _)] using
          W.le_one p.1 p.2)
    -- `W` is a two-variable function while its measurable theorem is stated for `uncurry W`.
    change Integrable (fun p : Ω × Ω => graphonDegree W p.2 * W p.1 p.2) (μ.prod μ) at h
    simpa only [mul_comm] using h
  have hpair_swap :
      Integrable (fun p : Ω × Ω => W p.2 p.1 * graphonDegree W p.1) (μ.prod μ) := by
    exact hpair.swap
  rw [← integral_prod _ hpair, ← integral_prod_swap]
  -- `integral_prod_swap` leaves the coordinate permutation in projection notation.
  change (∫ p : Ω × Ω, W p.2 p.1 * graphonDegree W p.1 ∂(μ.prod μ)) = _
  rw [integral_prod _ hpair_swap]
  congr 1
  funext x
  -- The product projections in the iterated integral reduce to the displayed coordinates.
  change (∫ y, W y x * graphonDegree W x ∂μ) = _
  rw [integral_mul_const]
  have hs : (∫ a, W a x ∂μ) = graphonDegree W x := by
    apply integral_congr_ae
    filter_upwards [] with a
    rw [Graphon.symm]
  rw [hs]
  simp only [pow_two]

private theorem integral_goodman_witness_nonneg (W : Graphon Ω μ) :
    0 ≤ ∫ p : Ω × Ω × Ω,
      W p.1 p.2.1 * (1 - W p.1 p.2.2) * (1 - W p.2.1 p.2.2)
        ∂(μ.prod (μ.prod μ)) := by
  exact integral_nonneg fun p => by
    exact mul_nonneg (mul_nonneg (W.nonneg _ _) (sub_nonneg.mpr (W.le_one _ _)))
      (sub_nonneg.mpr (W.le_one _ _))

private theorem integral_goodman_witness_expand (W : Graphon Ω μ) :
    (∫ p : Ω × Ω × Ω,
      W p.1 p.2.1 * (1 - W p.1 p.2.2) * (1 - W p.2.1 p.2.2)
        ∂(μ.prod (μ.prod μ))) =
      (∫ p : Ω × Ω × Ω, W p.1 p.2.1 ∂(μ.prod (μ.prod μ))) -
        (∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2
          ∂(μ.prod (μ.prod μ))) -
        (∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.2.1 p.2.2
          ∂(μ.prod (μ.prod μ))) +
        (∫ p : Ω × Ω × Ω, W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2
          ∂(μ.prod (μ.prod μ))) := by
  have h₁ := integrable_triple_graphon_edge W
  have h₂ := integrable_triple_graphon_two_edges_left W
  have h₃ := integrable_triple_graphon_two_edges_right W
  have h₄ := integrable_triangle_integrand W
  have h₁₂ : Integrable (fun p : Ω × Ω × Ω =>
      W p.1 p.2.1 - W p.1 p.2.1 * W p.1 p.2.2) (μ.prod (μ.prod μ)) := h₁.sub h₂
  have h₁₂₃ : Integrable (fun p : Ω × Ω × Ω =>
      W p.1 p.2.1 - W p.1 p.2.1 * W p.1 p.2.2 -
        W p.1 p.2.1 * W p.2.1 p.2.2) (μ.prod (μ.prod μ)) := h₁₂.sub h₃
  have hpoint : (fun p : Ω × Ω × Ω =>
      W p.1 p.2.1 * (1 - W p.1 p.2.2) * (1 - W p.2.1 p.2.2)) =
      (fun p : Ω × Ω × Ω =>
        W p.1 p.2.1 - W p.1 p.2.1 * W p.1 p.2.2 -
          W p.1 p.2.1 * W p.2.1 p.2.2) +
        (fun p : Ω × Ω × Ω =>
          W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2) := by
    funext p
    simp only [Pi.add_apply]
    ring
  rw [hpoint]
  -- Make the pointwise sum explicit for the integral linearity lemma.
  change (∫ p : Ω × Ω × Ω,
      (W p.1 p.2.1 - W p.1 p.2.1 * W p.1 p.2.2 -
        W p.1 p.2.1 * W p.2.1 p.2.2) +
        W p.1 p.2.1 * W p.1 p.2.2 * W p.2.1 p.2.2
        ∂(μ.prod (μ.prod μ))) = _
  rw [integral_add h₁₂₃ h₄, integral_sub h₁₂ h₃, integral_sub h₁ h₂]

private theorem integral_graphonDegree_eq_edge_density (W : Graphon Ω μ) :
    (∫ x, graphonDegree W x ∂μ) =
      homDensity (⊤ : SimpleGraph (Fin 2)) W := by
  rw [homDensity_top_fin_two_eq_integral_integral]
  rfl

/-! ### The 4-cycle integral -/

private def finFourArrowRight (Ω : Type*) [MeasurableSpace Ω] :
    (Fin 4 → Ω) ≃ᵐ Ω × Ω × Ω × Ω :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => Ω) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Ω) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Ω)
          MeasurableEquiv.finTwoArrow)))

private def middleSwap (Ω : Type*) [MeasurableSpace Ω] :
    (Ω × Ω × Ω) ≃ᵐ Ω × Ω × Ω :=
  ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω).symm.trans
    ((MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ Ω × Ω).prodCongr
      (MeasurableEquiv.refl Ω))).trans
    (MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω)

private def reorderFour (Ω : Type*) [MeasurableSpace Ω] :
    (Ω × Ω × Ω × Ω) ≃ᵐ Ω × Ω × Ω × Ω :=
  (MeasurableEquiv.refl Ω).prodCongr (middleSwap Ω)

private def finFourArrowPairPair (Ω : Type*) [MeasurableSpace Ω] :
    (Fin 4 → Ω) ≃ᵐ (Ω × Ω) × (Ω × Ω) :=
  (finFourArrowRight Ω).trans (reorderFour Ω) |>.trans
    ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × (Ω × Ω)) ≃ᵐ Ω × Ω × (Ω × Ω)).symm)

private theorem middleSwap_apply (p : Ω × Ω × Ω) :
    middleSwap Ω p = (p.2.1, p.1, p.2.2) := by
  rfl

@[simp]
private theorem finFourArrowPairPair_apply (x : Fin 4 → Ω) :
    finFourArrowPairPair Ω x = ((x 0, x 2), (x 1, x 3)) := by
  rfl

private theorem measurePreserving_middleSwap (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (middleSwap Ω) (μ.prod (μ.prod μ)) (μ.prod (μ.prod μ)) := by
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω)
      ((μ.prod μ).prod μ) (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have hSwap : MeasurePreserving (MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ Ω × Ω)
      (μ.prod μ) (μ.prod μ) := Measure.measurePreserving_swap
  convert hAssoc.comp ((hSwap.prod (MeasurePreserving.id μ)).comp hAssoc.symm) using 1
  funext p
  exact middleSwap_apply p

private theorem measurePreserving_finFourArrowPairPair (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (finFourArrowPairPair Ω) (Measure.pi fun _ : Fin 4 => μ)
      ((μ.prod μ).prod (μ.prod μ)) := by
  have hright : MeasurePreserving (finFourArrowRight Ω) (Measure.pi fun _ : Fin 4 => μ)
      (μ.prod (μ.prod (μ.prod μ))) :=
    ((MeasurePreserving.id μ).prod
      (((MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μ) 0)
  have hswap : MeasurePreserving (reorderFour Ω)
      (μ.prod (μ.prod (μ.prod μ))) (μ.prod (μ.prod (μ.prod μ))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_middleSwap μ)
  have hassoc : MeasurePreserving
      ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × (Ω × Ω)) ≃ᵐ Ω × Ω × (Ω × Ω)).symm)
      (μ.prod (μ.prod (μ.prod μ))) ((μ.prod μ).prod (μ.prod μ)) :=
    (measurePreserving_prodAssoc μ μ (μ.prod μ)).symm
  convert hassoc.comp (hswap.comp hright) using 1
  funext x
  exact finFourArrowPairPair_apply x

private theorem homDensity_fin_four (F : SimpleGraph (Fin 4)) [DecidableRel F.Adj]
    (W : Graphon Ω μ) :
    homDensity F W =
      ∫ p : (Ω × Ω) × (Ω × Ω),
        ∏ e ∈ F.edgeFinset,
          edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e
          ∂((μ.prod μ).prod (μ.prod μ)) := by
  have key : ∀ x : Fin 4 → Ω,
      (∏ e ∈ F.edgeFinset, edgeFactor W x e) =
        ∏ e ∈ F.edgeFinset, edgeFactor W ![x 0, x 1, x 2, x 3] e := by
    intro x
    have hx : ![x 0, x 1, x 2, x 3] = x := FinVec.etaExpand_eq x
    rw [hx]
  rw [homDensity_def, ← (measurePreserving_finFourArrowPairPair μ).integral_comp
    (finFourArrowPairPair Ω).measurableEmbedding
    (fun p : (Ω × Ω) × (Ω × Ω) =>
      ∏ e ∈ F.edgeFinset, edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e)]
  simp only [finFourArrowPairPair_apply]
  exact integral_congr_ae (ae_of_all _ fun x => key x)

private theorem prod_edgeFactor_cycle_four (W : Graphon Ω μ)
    (p : (Ω × Ω) × (Ω × Ω)) :
    ∏ e ∈ (SimpleGraph.cycleGraph 4).edgeFinset,
        edgeFactor W ![p.1.1, p.2.1, p.1.2, p.2.2] e =
      W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1 := by
  have hedge : (SimpleGraph.cycleGraph 4).edgeFinset =
      {s(0, 1), s(0, 3), s(1, 2), s(2, 3)} := by decide
  rw [hedge, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [edgeFactor_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Graphon.symm (W := W) (p.1.1) (p.2.2)]
  ring

private theorem integrable_cycle_four (W : Graphon Ω μ) :
    Integrable (fun p : (Ω × Ω) × (Ω × Ω) =>
      W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1)
      ((μ.prod μ).prod (μ.prod μ)) := by
  have h := integrable_prod_edgeFactor (Ω := Ω) (μ := μ)
    (SimpleGraph.cycleGraph 4).edgeFinset (fun _ => W)
  refine ((measurePreserving_finFourArrowPairPair μ).integrable_comp_emb
    (finFourArrowPairPair Ω).measurableEmbedding).mp ?_
  refine h.congr (ae_of_all _ fun x => ?_)
  have hp := prod_edgeFactor_cycle_four W (finFourArrowPairPair Ω x)
  simp only [finFourArrowPairPair_apply] at hp
  simp only [Function.comp_apply, finFourArrowPairPair_apply]
  rw [← FinVec.etaExpand_eq x]
  exact hp

private theorem homDensity_cycle_four (W : Graphon Ω μ) :
    homDensity (SimpleGraph.cycleGraph 4) W =
      ∫ p : (Ω × Ω) × (Ω × Ω),
        W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1
          ∂((μ.prod μ).prod (μ.prod μ)) := by
  rw [homDensity_fin_four]
  exact integral_congr_ae (ae_of_all _ fun p => prod_edgeFactor_cycle_four W p)

private def twoStepIntegral (W : Graphon Ω μ) (x z : Ω) : ℝ :=
  ∫ y, W x y * W y z ∂μ

private theorem integrable_twoStep_integrand (W : Graphon Ω μ) :
    Integrable (fun p : (Ω × Ω) × Ω => W p.1.1 p.2 * W p.2 p.1.2)
      ((μ.prod μ).prod μ) := by
  apply (integrable_const (1 : ℝ)).mono
    (by
      have h₁ : Measurable (fun p : (Ω × Ω) × Ω => W p.1.1 p.2) :=
        W.measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have h₂ : Measurable (fun p : (Ω × Ω) × Ω => W p.2 p.1.2) :=
        W.measurable.comp
          (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
      exact (h₁.mul h₂).aestronglyMeasurable)
  filter_upwards [] with p
  have h₁ := W.nonneg p.1.1 p.2
  have h₂ := W.nonneg p.2 p.1.2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h₁ h₂), norm_one]
  simpa only [one_mul] using mul_le_mul (W.le_one _ _) (W.le_one _ _) h₂ (by norm_num)

private theorem integrable_twoStep (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => twoStepIntegral W p.1 p.2) (μ.prod μ) := by
  -- Unfold the local two-step notation so the product-measure integrability lemma applies.
  change Integrable (fun p : Ω × Ω => ∫ y, W p.1 y * W y p.2 ∂μ) (μ.prod μ)
  exact (integrable_twoStep_integrand W).integral_prod_left

private theorem twoStep_nonneg (W : Graphon Ω μ) (x z : Ω) :
    0 ≤ twoStepIntegral W x z := by
  exact integral_nonneg fun y => mul_nonneg (W.nonneg _ _) (W.nonneg _ _)

private theorem integrable_twoStep_slice (W : Graphon Ω μ) (x z : Ω) :
    Integrable (fun y => W x y * W y z) μ := by
  apply (integrable_const (1 : ℝ)).mono
    ((W.measurable.comp (measurable_const.prodMk measurable_id)).mul
      (W.measurable.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  filter_upwards [] with y
  have hbound : W x y * W y z ≤ 1 := by
    simpa only [one_mul] using
      mul_le_mul (W.le_one x y) (W.le_one y z) (W.nonneg y z) (by norm_num)
  simpa [Function.comp_def, Real.norm_eq_abs,
    abs_of_nonneg (W.nonneg x y), abs_of_nonneg (W.nonneg y z)] using hbound

private theorem twoStep_le_one (W : Graphon Ω μ) (x z : Ω) :
    twoStepIntegral W x z ≤ 1 := by
  have h := integral_mono (integrable_twoStep_slice W x z) (integrable_const (1 : ℝ))
    (fun y => by
      simpa only [one_mul] using
        mul_le_mul (W.le_one x y) (W.le_one y z) (W.nonneg y z) (by norm_num))
  simpa [twoStepIntegral, one_mul, mul_one] using h

private theorem integrable_twoStep_sq (W : Graphon Ω μ) :
    Integrable (fun p : Ω × Ω => twoStepIntegral W p.1 p.2 ^ 2) (μ.prod μ) := by
  apply (integrable_const (1 : ℝ)).mono
    ((integrable_twoStep W).aestronglyMeasurable.pow 2)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_one]
  have hsq := mul_self_le_mul_self (twoStep_nonneg W p.1 p.2)
    (twoStep_le_one W p.1 p.2)
  simpa [pow_two] using hsq

private theorem prodAssoc_prodComm_apply (p : (Ω × Ω) × Ω) :
    ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω).trans
      ((MeasurableEquiv.refl Ω).prodCongr
        (MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ Ω × Ω))) p =
      (p.1.1, p.2, p.1.2) := by
  rfl

private theorem integral_twoStep_eq_degree_sq (W : Graphon Ω μ) :
    (∫ p : Ω × Ω, twoStepIntegral W p.1 p.2 ∂(μ.prod μ)) =
      ∫ x, graphonDegree W x ^ 2 ∂μ := by
  -- Expose the iterated integral so Fubini can rewrite it as a product-measure integral.
  change (∫ p : Ω × Ω, (∫ y, W p.1 y * W y p.2 ∂μ) ∂(μ.prod μ)) = _
  rw [integral_integral (integrable_twoStep_integrand W)]
  have hpath : MeasurePreserving
      ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω).trans
        ((MeasurableEquiv.refl Ω).prodCongr
          (MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ Ω × Ω)))
      ((μ.prod μ).prod μ) (μ.prod (μ.prod μ)) :=
    ((MeasurePreserving.id μ).prod Measure.measurePreserving_swap).comp
      (measurePreserving_prodAssoc μ μ μ)
  calc
    (∫ z, (fun p : (Ω × Ω) × Ω => W p.1.1 p.2 * W p.2 p.1.2) z
        ∂((μ.prod μ).prod μ)) =
        ∫ q : Ω × Ω × Ω, W q.1 q.2.1 * W q.2.1 q.2.2
          ∂(μ.prod (μ.prod μ)) := by
      rw [← hpath.integral_comp
        ((MeasurableEquiv.prodAssoc : ((Ω × Ω) × Ω) ≃ᵐ Ω × Ω × Ω).trans
          ((MeasurableEquiv.refl Ω).prodCongr
            (MeasurableEquiv.prodComm : (Ω × Ω) ≃ᵐ Ω × Ω))).measurableEmbedding]
      simp only [prodAssoc_prodComm_apply]
    _ = ∫ x, graphonDegree W x ^ 2 ∂μ := integral_triple_graphon_two_edges_right W

private theorem homDensity_cycle_four_eq_twoStep_sq (W : Graphon Ω μ) :
    homDensity (SimpleGraph.cycleGraph 4) W =
      ∫ p : Ω × Ω, twoStepIntegral W p.1 p.2 ^ 2 ∂(μ.prod μ) := by
  calc
    homDensity (SimpleGraph.cycleGraph 4) W =
        ∫ p : (Ω × Ω) × (Ω × Ω),
          W p.1.1 p.2.1 * W p.2.1 p.1.2 * W p.1.2 p.2.2 * W p.2.2 p.1.1
            ∂((μ.prod μ).prod (μ.prod μ)) := homDensity_cycle_four W
    _ = ∫ q : Ω × Ω, ∫ r : Ω × Ω,
          (W q.1 r.1 * W r.1 q.2) *
            (W q.2 r.2 * W r.2 q.1) ∂(μ.prod μ) ∂(μ.prod μ) := by
      simpa only [mul_assoc] using integral_prod _ (integrable_cycle_four W)
    _ = ∫ q : Ω × Ω,
          (∫ y, W q.1 y * W y q.2 ∂μ) *
            (∫ y, W q.2 y * W y q.1 ∂μ) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with q
      rw [integral_prod_mul
        (fun y : Ω => W q.1 y * W y q.2)
        (fun y : Ω => W q.2 y * W y q.1)]
    _ = ∫ q : Ω × Ω, twoStepIntegral W q.1 q.2 ^ 2 ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with q
      have hsecond : (∫ w, W q.2 w * W w q.1 ∂μ) =
          ∫ w, W q.1 w * W w q.2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with w
        calc
          W q.2 w * W w q.1 = W w q.2 * W q.1 w := by
            congr 1
            · exact Graphon.symm W q.2 w
            · exact Graphon.symm W w q.1
          _ = W q.1 w * W w q.2 := by
            rw [Graphon.symm W w q.2]
            ring
      rw [hsecond]
      simp only [twoStepIntegral, pow_two]

private theorem integral_goodman_witness_value (W : Graphon Ω μ) :
    (∫ p : Ω × Ω × Ω,
      W p.1 p.2.1 * (1 - W p.1 p.2.2) * (1 - W p.2.1 p.2.2)
        ∂(μ.prod (μ.prod μ))) =
      homDensity (⊤ : SimpleGraph (Fin 2)) W -
        2 * (∫ x, graphonDegree W x ^ 2 ∂μ) +
        homDensity (⊤ : SimpleGraph (Fin 3)) W := by
  rw [integral_goodman_witness_expand, integral_triple_graphon_edge,
    integral_triple_graphon_two_edges_left, integral_triple_graphon_two_edges_right,
    homDensity_top_fin_two_eq_integral_integral]
  rw [← homDensity_top_fin_three W]
  ring

/-! The public extremal inequalities. -/

/-- **Goodman's inequality.**  For every graphon, triangle density is at least
`2 * t(K₂, W)^2 - t(K₂, W)`. -/
theorem goodman_triangle_density (W : Graphon Ω μ) :
    2 * homDensity (⊤ : SimpleGraph (Fin 2)) W ^ 2 -
        homDensity (⊤ : SimpleGraph (Fin 2)) W ≤
      homDensity (⊤ : SimpleGraph (Fin 3)) W := by
  have hnonneg := integral_goodman_witness_nonneg W
  rw [integral_goodman_witness_value] at hnonneg
  have hsq := integral_graphonDegree_sq_ge W
  rw [integral_graphonDegree_eq_edge_density] at hsq
  nlinarith

/-- **Mantel's inequality for graphons.**  A graphon with zero triangle density has edge
density at most `1 / 2`. -/
theorem mantel_triangle_free (W : Graphon Ω μ)
    (htriangle : homDensity (⊤ : SimpleGraph (Fin 3)) W = 0) :
    homDensity (⊤ : SimpleGraph (Fin 2)) W ≤ 1 / 2 := by
  have hgoodman := goodman_triangle_density W
  rw [htriangle] at hgoodman
  nlinarith [homDensity_nonneg (⊤ : SimpleGraph (Fin 2)) W]

/-! ### The four-cycle inequality -/

/-- **Sidorenko's inequality for the 4-cycle.**  The 4-cycle homomorphism density is at least the
fourth power of the edge density, on every probability carrier. This is the graphon form of the
`K_{2,2}` case in Y. Zhao, *Graph Theory and Additive Combinatorics*, Theorem 5.2.1. -/
theorem sidorenko_cycle_four (W : Graphon Ω μ) :
    homDensity (SimpleGraph.cycleGraph 4) W ≥
      homDensity (⊤ : SimpleGraph (Fin 2)) W ^ 4 := by
  have hmean := TauCeti.MeasureTheory.sq_setIntegral_le_measureReal_mul_setIntegral_sq
    (fun p : Ω × Ω => twoStepIntegral W p.1 p.2) Set.univ
    (measure_ne_top (μ.prod μ) Set.univ)
    (by simpa using integrable_twoStep W)
    (by simpa using integrable_twoStep_sq W)
  have hmean' :
      (∫ p : Ω × Ω, twoStepIntegral W p.1 p.2 ∂(μ.prod μ)) ^ 2 ≤
        ∫ p : Ω × Ω, twoStepIntegral W p.1 p.2 ^ 2 ∂(μ.prod μ) := by
    simpa [measureReal_def, IsProbabilityMeasure.measure_univ] using hmean
  rw [integral_twoStep_eq_degree_sq W] at hmean'
  rw [← homDensity_cycle_four_eq_twoStep_sq W] at hmean'
  have hdegree := integral_graphonDegree_sq_ge W
  rw [integral_graphonDegree_eq_edge_density] at hdegree
  calc
    homDensity (⊤ : SimpleGraph (Fin 2)) W ^ 4 =
        (homDensity (⊤ : SimpleGraph (Fin 2)) W ^ 2) *
          (homDensity (⊤ : SimpleGraph (Fin 2)) W ^ 2) := by ring
    _ ≤ (∫ x, graphonDegree W x ^ 2 ∂μ) *
        (∫ x, graphonDegree W x ^ 2 ∂μ) :=
      mul_self_le_mul_self (sq_nonneg _) hdegree
    _ = (∫ x, graphonDegree W x ^ 2 ∂μ) ^ 2 := by ring
    _ ≤ homDensity (SimpleGraph.cycleGraph 4) W := hmean'

end DenseGraphLimits

end TauCeti
