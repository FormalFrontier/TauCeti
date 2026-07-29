/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.DeFinetti.BlockFactorization
public import TauCeti.Probability.DeFinetti.ConditionalCommonEnding

/-!
# Work in progress: the directing-measure joint-rectangle factorization
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The event that the directing measure lands in `S` is a tail event: this is what lets the
conditional factorization be integrated against it. -/
private theorem measurableSet_tailProcess_directingProbabilityMeasure_preimage
    [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    MeasurableSet[tailProcess X] (directingProbabilityMeasure μ X ⁻¹' S) :=
  measurable_tailProcess_directingProbabilityMeasure hS

/-- **Core set-integral identity.** The mass on the tail event `ν ⁻¹' S` intersected with a prefix
block cylinder is the integral of the directing-measure product over that event.

All real/`ℝ≥0∞` conversion for the joint-rectangle argument is confined here: the tail event is
`tailProcess X`-measurable, so `setIntegral_condExp` may be tested against it, and the prefix
factorization then replaces the conditional expectation. -/
private theorem measure_inter_blockCylinder_eq_setLIntegral
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    μ ((directingProbabilityMeasure μ X ⁻¹' S)
        ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B)
      = ∫⁻ ω in directingProbabilityMeasure μ X ⁻¹' S,
          ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  classical
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  haveI : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set A : Set Ω := directingProbabilityMeasure μ X ⁻¹' S with hA_def
  have hA_tail : MeasurableSet[tailProcess X] A :=
    measurable_tailProcess_directingProbabilityMeasure hS
  have hA : MeasurableSet A := hTail _ hA_tail
  set g : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (B i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_directingMeasure_coe hTail (hB i)).ennreal_toReal
  have hg_nonneg : ∀ ω, 0 ≤ g ω := fun ω =>
    Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  have hg_bound : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    rw [Real.norm_of_nonneg (hg_nonneg ω)]
    refine Finset.prod_le_one (fun i _ => ENNReal.toReal_nonneg) fun i _ => ?_
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ)
  have hg_int : Integrable g μ :=
    (integrable_const (1 : ℝ)).mono' hg_meas.aestronglyMeasurable (ae_of_all _ hg_bound)
  have hind_int : Integrable (blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B) μ :=
    integrable_blockIndicatorProd (fun i => (hX_meas _).aemeasurable) hB
  -- the conditional factorization, tested against the tail event `A`
  have hchain : ∫ ω in A, blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B ω ∂μ
      = ∫ ω in A, g ω ∂μ := by
    rw [← setIntegral_condExp hTail hind_int hA_tail]
    refine setIntegral_congr_ae hA ?_
    filter_upwards
      [condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure hX hX_meas hB] with ω hω _
    exact hω
  -- the left side is the real mass of the intersection
  have hleft : ∫ ω in A, blockIndicatorProd X (fun i : Fin r => (i : ℕ)) B ω ∂μ
      = μ.real (A ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B) := by
    rw [blockIndicatorProd_eq_indicator,
      setIntegral_indicator (measurableSet_blockCylinder
        (fun i => hX_meas _) hB), setIntegral_const, Set.inter_comm]
    simp [measureReal_def]
  have hne : μ (A ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B) ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, ← hleft, hchain,
    ofReal_integral_eq_lintegral_ofReal (hg_int.restrict) (ae_of_all _ hg_nonneg)]
  refine setLIntegral_congr_fun hA (fun ω _ => ?_)
  simp only [hg, measureReal_def]
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => ENNReal.toReal_nonneg]
  exact Finset.prod_congr rfl fun i _ => ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- **Joint-rectangle factorization, prefix case.** The joint law of the directing measure with a
length-`r` prefix block agrees with the disintegration on rectangles `S ×ˢ ∏ i, B i`. -/
private theorem jointRectangle_prefix
    [StandardBorelSpace Ω] [StandardBorelSpace α] [Nonempty α] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    (μ.map fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X i ω))
        (S ×ˢ Set.univ.pi B)
      = (μ.bind fun ω =>
          (Measure.dirac (directingProbabilityMeasure μ X ω)).prod
            (ProbabilityMeasure.pi fun _ : Fin r =>
              directingProbabilityMeasure μ X ω).toMeasure)
        (S ×ˢ Set.univ.pi B) := by
  classical
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  have hν : Measurable (directingProbabilityMeasure μ X) :=
    measurable_directingProbabilityMeasure hTail
  have hjoint : Measurable fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X i ω) :=
    hν.prodMk (measurable_pi_lambda _ fun i => hX_meas _)
  have hker : Measurable fun ω =>
      (Measure.dirac (directingProbabilityMeasure μ X ω)).prod
        (ProbabilityMeasure.pi fun _ : Fin r => directingProbabilityMeasure μ X ω).toMeasure :=
    TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure _ hν
  have hrect : MeasurableSet (S ×ˢ Set.univ.pi B) :=
    hS.prod (MeasurableSet.univ_pi hB)
  -- the joint law's mass is the mass of the tail event meeting the block cylinder
  have hpre : (fun ω => (directingProbabilityMeasure μ X ω, fun i : Fin r => X i ω))
        ⁻¹' (S ×ˢ Set.univ.pi B)
      = (directingProbabilityMeasure μ X ⁻¹' S)
        ∩ blockCylinder X (fun i : Fin r => (i : ℕ)) B := by
    ext ω
    simp [Set.mem_prod, mem_blockCylinder, Set.mem_pi]
  rw [Measure.map_apply hjoint hrect, hpre,
    measure_inter_blockCylinder_eq_setLIntegral hX hX_meas hB hS,
    Measure.bind_apply hrect hker.aemeasurable]
  -- the mixture side splits as a Dirac indicator times the product measure
  rw [← lintegral_indicator (hν hS)]
  refine lintegral_congr fun ω => ?_
  have hprod : (ProbabilityMeasure.pi fun _ : Fin r => directingProbabilityMeasure μ X ω).toMeasure
      (Set.univ.pi B) = ∏ i, directingMeasure μ X ω (B i) := by
    rw [ProbabilityMeasure.toMeasure_pi, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => by rw [directingProbabilityMeasure_toMeasure]
  rw [Measure.prod_prod, Measure.dirac_apply' _ hS, hprod]
  by_cases hω : directingProbabilityMeasure μ X ω ∈ S
  · simp [Set.indicator_of_mem, hω, Set.mem_preimage]
  · simp [Set.indicator_of_notMem, hω, Set.mem_preimage]

end Probability

end TauCeti
