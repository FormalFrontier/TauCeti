/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Stability
public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Regularity
import TauCeti.Combinatorics.DenseGraphLimits.Kernel.Pullback
import TauCeti.Combinatorics.DenseGraphLimits.Graphon.Pullback
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition
import TauCeti.MeasureTheory.OptimalTransport.Gluing

/-!
# The triangle inequality for graphon cut distance

This file proves the triangle inequality for the coupling-primary cut distance on arbitrary
probability carriers.  The central finite-middle case glues two couplings over a countable
intermediate carrier and pulls all three overlaid kernels back to the glued probability space,
where their pointwise difference telescopes.  Exact invariance of the cut norm under
measure-preserving pullback then returns the estimate to the original couplings.

For an arbitrary intermediate carrier, Frieze--Kannan weak regularity replaces the middle graphon
by a finite step graphon.  Its finite set of blocks is the countable middle carrier to which the
gluing argument applies, and stability of cut distance under cut-norm approximation removes the
replacement error.  This avoids imposing standard-Borel or atomlessness hypotheses on any of the
three carriers.

The triangle inequality is the final pseudometric law needed to form the metric quotient of
graphons at cut distance zero.

## Main results

* `TauCeti.DenseGraphLimits.cutDist_triangle_of_countable_middle` proves the triangle inequality
  when the intermediate carrier is countable with measurable singletons.
* `TauCeti.DenseGraphLimits.cutDist_triangle` proves it on arbitrary probability carriers.

## References

* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Lemma 6.5.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), Section 8.2.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti.MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

variable {Ω₁ Ω₂ Ω₃ : Type*}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃}
variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃]

/-- Pulling the three overlaid differences to a joint law makes the outer difference telescope.

Here `gamma` has `pi12` as its `(Omega1, Omega2)` marginal and `pi23` as its
`(Omega2, Omega3)` marginal.  Its outer marginal is therefore a coupling of `mu1` and `mu3`, and
the cut norm along that coupling is at most the sum of the two input cut norms. -/
private theorem exists_isCoupling_cutNorm_overlayDiff_le_of_glue
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (X : Graphon Ω₃ μ₃)
    {π₁₂ : Measure (Ω₁ × Ω₂)} {π₂₃ : Measure (Ω₂ × Ω₃)}
    (hπ₁₂ : IsCoupling μ₁ μ₂ π₁₂) (hπ₂₃ : IsCoupling μ₂ μ₃ π₂₃)
    {γ : Measure (Ω₁ × Ω₂ × Ω₃)}
    (hleft : γ.map (Prod.map id Prod.fst) = π₁₂) (hright : γ.snd = π₂₃) :
    ∃ (π₁₃ : Measure (Ω₁ × Ω₃)) (hπ₁₃ : IsCoupling μ₁ μ₃ π₁₃),
      @cutNorm _ _ π₁₃ hπ₁₃.isFiniteMeasure (overlayDiff U X π₁₃) ≤
        @cutNorm _ _ π₁₂ hπ₁₂.isFiniteMeasure (overlayDiff U W π₁₂) +
          @cutNorm _ _ π₂₃ hπ₂₃.isFiniteMeasure (overlayDiff W X π₂₃) := by
  let _ := hπ₁₂.isProbabilityMeasure
  let _ := hπ₂₃.isProbabilityMeasure
  let _ : IsProbabilityMeasure (γ.map (Prod.map id Prod.fst)) :=
    hleft.symm ▸ hπ₁₂.isProbabilityMeasure
  let _ : IsProbabilityMeasure γ :=
    Measure.isProbabilityMeasure_of_map (measurable_id.prodMap measurable_fst).aemeasurable
  let π₁₃ : Measure (Ω₁ × Ω₃) := γ.map (Prod.map id Prod.snd)
  have hπ₁₃ : IsCoupling μ₁ μ₃ π₁₃ := isCoupling_iff.2
    <| ⟨(TauCeti.Measure.fst_map_prodMap_id_snd hleft).trans hπ₁₂.fst_eq,
      (TauCeti.Measure.snd_map_prodMap_id_snd hright).trans hπ₂₃.snd_eq⟩
  let _ := hπ₁₃.isProbabilityMeasure
  have hmp12 : MeasurePreserving (fun p : Ω₁ × Ω₂ × Ω₃ => (p.1, p.2.1)) γ π₁₂ :=
    ⟨measurable_id.prodMap measurable_fst, hleft⟩
  have hmp23 : MeasurePreserving Prod.snd γ π₂₃ := ⟨measurable_snd, hright⟩
  have hmp13 : MeasurePreserving (fun p : Ω₁ × Ω₂ × Ω₃ => (p.1, p.2.2)) γ π₁₃ :=
    ⟨measurable_id.prodMap measurable_snd, rfl⟩
  refine ⟨π₁₃, hπ₁₃, ?_⟩
  calc
    cutNorm π₁₃ (overlayDiff U X π₁₃) =
        cutNorm γ ((overlayDiff U X π₁₃).comap (fun p => (p.1, p.2.2))
          (measurable_id.prodMap measurable_snd) γ) :=
      (cutNorm_comap hmp13 _).symm
    _ = cutNorm γ
        ((overlayDiff U W π₁₂).comap (fun p => (p.1, p.2.1))
            (measurable_id.prodMap measurable_fst) γ +
          (overlayDiff W X π₂₃).comap Prod.snd measurable_snd γ) := by
      congr 1
      ext p q
      simp only [overlayDiff_apply, SymmKernel.comap_apply, SymmKernel.coe_add, Pi.add_apply]
      ring
    _ ≤ cutNorm γ
          ((overlayDiff U W π₁₂).comap (fun p => (p.1, p.2.1))
            (measurable_id.prodMap measurable_fst) γ) +
        cutNorm γ ((overlayDiff W X π₂₃).comap Prod.snd measurable_snd γ) :=
      cutNorm_add_le γ _ _
    _ = cutNorm π₁₂ (overlayDiff U W π₁₂) + cutNorm π₂₃ (overlayDiff W X π₂₃) := by
      rw [cutNorm_comap hmp12, cutNorm_comap hmp23]

/-- The coupling cut distance satisfies the triangle inequality when the intermediate carrier is
countable and has measurable singletons.

Two nearly optimal couplings are glued over the middle marginal.  This result is the exact finite
gluing statement used after replacing an arbitrary middle graphon by a finite step graphon. -/
theorem cutDist_triangle_of_countable_middle [Countable Ω₂]
    [MeasurableSingletonClass Ω₂] (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂)
    (X : Graphon Ω₃ μ₃) : cutDist U X ≤ cutDist U W + cutDist W X := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨π₁₂, hπ₁₂, hnorm12⟩ :=
    exists_isCoupling_cutNorm_lt U W (c := cutDist U W + ε / 2)
      (lt_add_of_pos_right _ (half_pos hε))
  obtain ⟨π₂₃, hπ₂₃, hnorm23⟩ :=
    exists_isCoupling_cutNorm_lt W X (c := cutDist W X + ε / 2)
      (lt_add_of_pos_right _ (half_pos hε))
  let _ := hπ₂₃.isFiniteMeasure
  obtain ⟨γ, hleft, hright⟩ :=
    TauCeti.MeasureTheory.exists_glue_of_countable_middle π₁₂ π₂₃
      (hπ₁₂.snd_eq.trans hπ₂₃.fst_eq.symm)
  obtain ⟨π₁₃, hπ₁₃, hnorm13⟩ :=
    exists_isCoupling_cutNorm_overlayDiff_le_of_glue U W X hπ₁₂ hπ₂₃ hleft hright
  calc
    cutDist U X ≤
        @cutNorm _ _ π₁₃ hπ₁₃.isFiniteMeasure (overlayDiff U X π₁₃) :=
      cutDist_le U X hπ₁₃
    _ ≤ @cutNorm _ _ π₁₂ hπ₁₂.isFiniteMeasure (overlayDiff U W π₁₂) +
        @cutNorm _ _ π₂₃ hπ₂₃.isFiniteMeasure (overlayDiff W X π₂₃) := hnorm13
    _ ≤ cutDist U W + cutDist W X + ε := by linarith

private theorem cutDist_le_cutDist_comap_right
    {Ω₂' : Type*} [MeasurableSpace Ω₂'] {μ₂' : Measure Ω₂'} [IsProbabilityMeasure μ₂']
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {f : Ω₂' → Ω₂}
    (hf : MeasurePreserving f μ₂' μ₂) :
    cutDist U W ≤ cutDist U (W.comap f hf.measurable μ₂') := by
  refine le_cutDist U (W.comap f hf.measurable μ₂') fun π hπ => ?_
  let _ := hπ.isProbabilityMeasure
  let ρ : Measure (Ω₁ × Ω₂) := π.map (Prod.map id f)
  have hρ : IsCoupling μ₁ μ₂ ρ := isCoupling_iff.2
    ⟨by
      rw [← hπ.fst_eq]
      simp only [ρ, Measure.fst, Measure.map_map measurable_fst
        (measurable_id.prodMap hf.measurable), Prod.map_fst', Function.id_comp],
    by
      rw [← hf.map_eq, ← hπ.snd_eq]
      simp only [ρ, Measure.snd, Measure.map_map measurable_snd
        (measurable_id.prodMap hf.measurable), Measure.map_map hf.measurable measurable_snd,
        Prod.map_snd']⟩
  let _ := hρ.isProbabilityMeasure
  have hmp : MeasurePreserving (Prod.map id f) π ρ :=
    ⟨measurable_id.prodMap hf.measurable, rfl⟩
  calc
    cutDist U W ≤ cutNorm ρ (overlayDiff U W ρ) := cutDist_le U W hρ
    _ = cutNorm π ((overlayDiff U W ρ).comap (Prod.map id f)
          (measurable_id.prodMap hf.measurable) π) := (cutNorm_comap hmp _).symm
    _ = cutNorm π (overlayDiff U (W.comap f hf.measurable μ₂') π) := by
      congr 1
      ext p q
      simp

private theorem cutDist_comap_right_of_countable
    [Countable Ω₂] [MeasurableSingletonClass Ω₂]
    {Ω₂' : Type*} [MeasurableSpace Ω₂'] {μ₂' : Measure Ω₂'} [IsProbabilityMeasure μ₂']
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) {f : Ω₂' → Ω₂}
    (hf : MeasurePreserving f μ₂' μ₂) :
    cutDist U (W.comap f hf.measurable μ₂') = cutDist U W := by
  apply le_antisymm
  · have hzero : cutDist W (W.comap f hf.measurable μ₂') = 0 := by
      apply le_antisymm
      · have h := cutDist_le_cutNorm_sub_of_measurePreserving W
          (W.comap f hf.measurable μ₂') hf (MeasurePreserving.id μ₂')
        rw [Graphon.toSymmKernel_comap, SymmKernel.comap_id, sub_self, cutNorm_zero] at h
        exact h
      · exact cutDist_nonneg _ _
    calc
      cutDist U (W.comap f hf.measurable μ₂') ≤
          cutDist U W + cutDist W (W.comap f hf.measurable μ₂') :=
        cutDist_triangle_of_countable_middle U W _
      _ = cutDist U W := by rw [hzero, add_zero]
  · exact cutDist_le_cutDist_comap_right U W hf

section StepModel

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {P : Finpartition (Set.univ : Set Ω)} [MeasurableSpace P.parts]
variable [DiscreteMeasurableSpace P.parts]

/-- A finite step graphon's block matrix, regarded as a graphon on the discrete probability space
of partition parts. -/
private def stepGraphonModel
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p) :
    Graphon P.parts (μ.map P.indexedPartition.index) where
  toFun p q := val p q
  symm' p q := congrArg Subtype.val (hsymm p q)
  meas' := measurable_of_countable _
  bdd' := ⟨1, fun p q => by
    rw [abs_of_nonneg (val p q).property.1]
    exact (val p q).property.2⟩
  mem01' p q := (val p q).property

@[simp]
private theorem stepGraphonModel_apply
    (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p)
    (p q : P.parts) : stepGraphonModel (μ := μ) val hsymm p q = val p q := rfl

end StepModel

/-- The cut distance satisfies the triangle inequality when the intermediate graphon is constant
on the rectangles of a measurable finite partition. -/
private theorem cutDist_triangle_of_constantOn_partition
    (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (X : Graphon Ω₃ μ₃)
    (P : Finpartition (Set.univ : Set Ω₂)) (hP : ∀ p ∈ P.parts, MeasurableSet p)
    (hconst : ∀ (p q : P.parts) {x y : Ω₂}, x ∈ (p : Set Ω₂) → y ∈ (q : Set Ω₂) →
      W x y = W (P.indexedPartition.some p) (P.indexedPartition.some q)) :
    cutDist U X ≤ cutDist U W + cutDist W X := by
  let _ : MeasurableSpace P.parts := ⊤
  let ν : Measure P.parts := μ₂.map P.indexedPartition.index
  let val : P.parts → P.parts → Set.Icc (0 : ℝ) 1 := fun p q =>
    ⟨W (P.indexedPartition.some p) (P.indexedPartition.some q), W.mem_Icc _ _⟩
  have hsymm : ∀ p q, val p q = val q p := fun p q => by
    apply Subtype.ext
    exact W.symm _ _
  let A : Graphon P.parts ν := stepGraphonModel (μ := μ₂) val hsymm
  have hindex : Measurable P.indexedPartition.index :=
    Finpartition.measurable_indexedPartition_index P hP
  have hmp : MeasurePreserving P.indexedPartition.index μ₂ ν := ⟨hindex, rfl⟩
  have hmodel : W = A.comap P.indexedPartition.index hindex μ₂ := by
    ext x y
    rw [Graphon.comap_apply, stepGraphonModel_apply]
    exact hconst _ _ (P.indexedPartition.mem_index x) (P.indexedPartition.mem_index y)
  rw [hmodel, cutDist_comap_right_of_countable U A hmp, cutDist_comm
    (A.comap P.indexedPartition.index hindex μ₂) X, cutDist_comap_right_of_countable X A hmp,
    cutDist_comm X A]
  exact cutDist_triangle_of_countable_middle U A X

/-- The coupling-primary graphon cut distance satisfies the triangle inequality on arbitrary
probability carriers. -/
theorem cutDist_triangle (U : Graphon Ω₁ μ₁) (W : Graphon Ω₂ μ₂) (X : Graphon Ω₃ μ₃) :
    cutDist U X ≤ cutDist U W + cutDist W X := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨P, hP, _, happrox⟩ := weak_regularity_frieze_kannan μ₂ W (half_pos hε)
  let W' := stepGraphonAvg (μ := μ₂) P hP W
  have htriangle : cutDist U X ≤ cutDist U W' + cutDist W' X := by
    apply cutDist_triangle_of_constantOn_partition U W' X P hP
    intro p q x y hx hy
    rw [show W' = stepGraphonAvg (μ := μ₂) P hP W from rfl,
      stepGraphonAvg_apply P hP W hx hy,
      stepGraphonAvg_apply P hP W (P.indexedPartition.some_mem p)
        (P.indexedPartition.some_mem q)]
  have htransfer := cutDist_le_add_two_mul_cutNorm_of_le_add U W W' X htriangle
  dsimp only [W'] at htransfer
  nlinarith

end DenseGraphLimits

end TauCeti
