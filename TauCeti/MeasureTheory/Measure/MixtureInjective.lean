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

variable {π₁ π₂ : Measure (ProbabilityMeasure α)}

/-- Equal mixtures have equal rectangle probabilities, hence equal mixed moments of the evaluation
maps over an arbitrary finite family of measurable sets — repetitions allowed. -/
private theorem lintegral_prod_eq_of_bind_eq
    (h : (π₁.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
      = π₂.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
    {n : ℕ} (B : Fin n → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫⁻ P, ∏ i, (P : Measure α) (B i) ∂π₁ = ∫⁻ P, ∏ i, (P : Measure α) (B i) ∂π₂ := by
  rw [← map_prefixProj_bind_infinitePi_pi π₁ B hB, ← map_prefixProj_bind_infinitePi_pi π₂ B hB, h]

/-- The monomial form. Since `lintegral_prod_eq_of_bind_eq` allows repetitions in the family,
listing `B j` exactly `m j` times turns the rectangle identity into one for the mixed monomial
`∏ j, (P (B j)) ^ m j`. -/
private theorem lintegral_prod_pow_eq_of_bind_eq
    (h : (π₁.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
      = π₂.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
    {k : ℕ} (B : Fin k → Set α) (hB : ∀ i, MeasurableSet (B i)) (m : Fin k → ℕ) :
    ∫⁻ P, ∏ j, ((P : Measure α) (B j)) ^ m j ∂π₁
      = ∫⁻ P, ∏ j, ((P : Measure α) (B j)) ^ m j ∂π₂ := by
  classical
  -- index the repeated family by `Σ j, Fin (m j)`, transported to `Fin n`
  set S := Σ j : Fin k, Fin (m j) with hS
  have hcard : Fintype.card S = ∑ j, m j := by simp [hS]
  set e : S ≃ Fin (∑ j, m j) := Fintype.equivFinOfCardEq hcard with he
  set B' : Fin (∑ j, m j) → Set α := fun i => B (e.symm i).1 with hB'
  have hB'm : ∀ i, MeasurableSet (B' i) := fun i => hB _
  have hprod : ∀ P : ProbabilityMeasure α,
      ∏ i, (P : Measure α) (B' i) = ∏ j, ((P : Measure α) (B j)) ^ m j := by
    intro P
    rw [Fintype.prod_bijective e.symm e.symm.bijective
      (fun i => (P : Measure α) (B' i)) (fun p : S => (P : Measure α) (B p.1)) (fun _ => rfl),
      Fintype.prod_sigma]
    simp
  simpa only [hprod] using lintegral_prod_eq_of_bind_eq h B' hB'm

end MeasureTheory

end TauCeti
