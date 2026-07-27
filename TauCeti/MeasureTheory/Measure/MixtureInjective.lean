/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.ProductKernel
public import TauCeti.MeasureTheory.Measure.GiryMonad
public import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# The mixing measure is identified by the i.i.d. mixture

Work in progress.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The mixture's finite-dimensional rectangle probabilities are the mixed moments of the
evaluation maps: pushing `π.bind (P ↦ P^{⊗ℕ})` to its first `n` coordinates and evaluating on a
rectangle `∏ i, B i` gives `∫⁻ P, ∏ i, P (B i) ∂π`. -/
theorem map_prefixProj_bind_infinitePi_pi (π : Measure (ProbabilityMeasure α))
    {n : ℕ} (B : Fin n → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ((π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
        (fun x : ℕ → α => fun i : Fin n => x i)) (Set.univ.pi B)
      = ∫⁻ P, ∏ i, (P : Measure α) (B i) ∂π := by
  have hproj : Measurable (fun x : ℕ → α => fun i : Fin n => x i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hmeas : AEMeasurable (fun P : ProbabilityMeasure α =>
      (Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
        fun x : ℕ → α => fun i : Fin n => x i) π :=
    ((Measure.measurable_map _ hproj).comp measurable_infinitePi_const).aemeasurable
  rw [map_bind measurable_infinitePi_const.aemeasurable hproj,
    Measure.bind_apply (MeasurableSet.univ_pi hB) hmeas]
  refine lintegral_congr fun P => ?_
  rw [map_prefixProj_infinitePi_const, Measure.pi_pi]

end MeasureTheory

end TauCeti
