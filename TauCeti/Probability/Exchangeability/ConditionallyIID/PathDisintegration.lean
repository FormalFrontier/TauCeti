/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The full-path joint disintegration
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint path law: the law of the directing measure together with the whole path. -/
@[expose]
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.map fun ω => (ν ω, fun i => X i ω)

/-- The full-path disintegration measure `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`. -/
@[expose]
def pathDisintegration (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.bind fun ω =>
    (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))

theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    jointPathLaw μ X ν = μ.map fun ω => (ν ω, fun i => X i ω) := rfl

theorem pathDisintegration_def (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    pathDisintegration μ ν = μ.bind fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α)) := rfl

/-- The prefix pushforward of the joint path law is the joint block law of the first `n`
coordinates. -/
theorem map_prefix_jointPathLaw (hX : ∀ i, Measurable (X i)) (hν : Measurable ν) (n : ℕ) :
    (jointPathLaw μ X ν).map (fun q => (q.1, fun i : Fin n => q.2 i))
      = μ.map fun ω => (ν ω, fun i : Fin n => X i ω) := by
  have hpath : Measurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) :=
    hν.prodMk (measurable_pi_lambda _ hX)
  have hproj : Measurable (fun q : ProbabilityMeasure α × (ℕ → α) =>
      (q.1, fun i : Fin n => q.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_lambda _ fun i =>
      (measurable_pi_apply (i : ℕ)).comp measurable_snd))
  rw [jointPathLaw_def, Measure.map_map hproj hpath]
  rfl

/-- The prefix pushforward of the joint path law is the block-level disintegration, by the defining
identity at the first `n` coordinates. -/
theorem map_prefix_jointPathLaw_eq (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i))
    (n : ℕ) :
    (jointPathLaw μ X ν).map (fun q => (q.1, fun i : Fin n => q.2 i))
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  rw [map_prefix_jointPathLaw hX h.measurable_directing n]
  exact h.jointLaw_eq_disintegration (fun i : Fin n => (i : ℕ)) Fin.val_injective

/-- The prefix pushforward of the full-path disintegration is the block-level disintegration:
projecting `δ_{ν ω} ⊗ (ν ω)^{⊗ℕ}` onto the first `n` path coordinates leaves
`δ_{ν ω} ⊗ (ν ω)^{⊗ Fin n}`. -/
theorem map_prefix_pathDisintegration (hν : Measurable ν) (n : ℕ) :
    (pathDisintegration μ ν).map (fun q => (q.1, fun i : Fin n => q.2 i))
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  have hproj : Measurable (fun q : ProbabilityMeasure α × (ℕ → α) =>
      (q.1, fun i : Fin n => q.2 i)) :=
    measurable_fst.prodMk ((measurable_pi_lambda _ fun i =>
      (measurable_pi_apply (i : ℕ)).comp measurable_snd))
  have hker : Measurable (fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))) :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const (ι' := ℕ)
      (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).comp hν
  -- Projecting one fibre `δ_Q ⊗ Q^{⊗ℕ}` onto the first `n` path coordinates.
  have hfibre : ∀ Q : ProbabilityMeasure α,
      ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
          (fun q : ProbabilityMeasure α × (ℕ → α) => (q.1, fun i : Fin n => q.2 i))
        = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
    intro Q
    have hpref : Measurable (fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    calc ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
            (fun q : ProbabilityMeasure α × (ℕ → α) => (q.1, fun i : Fin n => q.2 i))
        = ((Measure.dirac Q).map id).prod
            ((Measure.infinitePi fun _ : ℕ => (Q : Measure α)).map
              fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) := by
          rw [Measure.map_prod_map _ _ measurable_id hpref]
          rfl
      _ = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
          rw [Measure.map_id, TauCeti.MeasureTheory.map_prefixProj_infinitePi_const Q n,
            ProbabilityMeasure.toMeasure_pi]
  rw [pathDisintegration_def, TauCeti.MeasureTheory.map_bind hker.aemeasurable hproj]
  congr 1
  funext ω
  exact hfibre (ν ω)

end Probability

end TauCeti
