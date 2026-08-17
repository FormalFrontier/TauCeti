/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.Probability.Moments.CompactDeterminacy
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Ext

/-!
# The mixing measure is identified by the i.i.d. mixture

The map `π ↦ π.bind (P ↦ P^{⊗ℕ})`, sending a measure on `ProbabilityMeasure α` to the law of a
sequence drawn i.i.d. from a `π`-random probability measure, is injective on finite measures.

## Main results

* `Measure.ext_of_bind_infinitePi_eq` — two finite measures on `ProbabilityMeasure α` inducing the
  same mixture are equal.

## Sources

The construction and proof plan follow the human-authored roadmap
`TauCetiRoadmap/Exchangeability/README.md`, *Layer 6 — directing measures and de Finetti
representation*, which names mixing-law uniqueness as the target this theorem serves.

## Implementation

Evaluating the mixture on a finite-dimensional rectangle gives the mixed moment
`∫⁻ P, ∏ i, P (B i) ∂π` of the evaluation maps. Nothing forces the sets `B i` to be distinct, so
listing `B j` exactly `m j` times turns the rectangle identity into one for the mixed monomial
`∏ j, (P (B j)) ^ m j` — this is the whole of the passage from rectangles to moments, and it is
where the argument gains its strength.

From there the two imported ingredients finish it. A finite evaluation family takes values in the
compact box `[0,1]^k`, so `Measure.ext_of_forall_integral_monomial_eq_of_support` identifies its
law from those monomials; and `Measure.ext_of_forall_map_probabilityMeasure_eval_eq` promotes
agreement of every finite evaluation law to equality of the measures.

Only `π₁` is assumed finite. Every infinite product of probability measures is a probability
measure, so the mixture has the same total mass as its mixing measure, and equality of the two
mixtures transfers finiteness to `π₂`.
-/
public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

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

/-- The `ℝ≥0∞`-valued mixed monomial is `ENNReal.ofReal` of its real-valued counterpart; a
probability measure's values are finite, so `toReal` passes through the product. -/
private theorem toReal_prod_pow (P : ProbabilityMeasure α) {k : ℕ} (B : Fin k → Set α)
    (m : Fin k → ℕ) : (∏ j, ((P : Measure α) (B j)) ^ m j).toReal = ∏ j, (P (B j) : ℝ) ^ m j := by
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, ← ENNReal.coe_pow,
    ENNReal.coe_toReal, NNReal.coe_pow]

/-- The mixture has the same total mass as the mixing measure, since every infinite product of
probability measures is itself a probability measure. -/
private theorem bind_infinitePi_univ (π : Measure (ProbabilityMeasure α)) :
    (π.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) Set.univ = π Set.univ := by
  rw [Measure.bind_apply MeasurableSet.univ measurable_infinitePi_const.aemeasurable]
  simp

/-- **The evaluation family lands in the unit box.** The pushforward of any measure on
`ProbabilityMeasure α` along `P ↦ (P (B 0), …, P (B (k-1)))` gives measure zero to the complement
of `[0, 1] ^ k`. -/
private theorem map_eval_family_compl_pi_Icc_eq_zero {k : ℕ} (B : Fin k → Set α)
    (hB : ∀ j, MeasurableSet (B j)) (π : Measure (ProbabilityMeasure α)) :
    (π.map fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ))
      (Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hKc : IsCompact (Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  rw [← mem_ae_iff, _root_.MeasureTheory.mem_ae_map_iff
    (measurable_probabilityMeasure_eval_family B hB).aemeasurable hKc.isClosed.measurableSet]
  exact Filter.Eventually.of_forall fun P j _ =>
    ⟨(P (B j)).coe_nonneg, by exact_mod_cast (P.apply_le_one (B j))⟩

/-- **A monomial moment of the evaluation family is a mixed moment of the set measures.** The
integral of `∏ j, x j ^ m j` against the pushforward along `P ↦ (P (B 0), …)` is
`(∫⁻ P, ∏ j, P (B j) ^ m j).toReal`. -/
private theorem integral_prod_pow_map_eq_toReal_lintegral {k : ℕ} (B : Fin k → Set α)
    (hB : ∀ j, MeasurableSet (B j)) (m : Fin k → ℕ) (π : Measure (ProbabilityMeasure α)) :
    ∫ x, ∏ j, x j ^ m j ∂(π.map fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ))
      = (∫⁻ P, ∏ j, ((P : Measure α) (B j)) ^ m j ∂π).toReal := by
  rw [integral_map (measurable_probabilityMeasure_eval_family B hB).aemeasurable
    (Finset.measurable_prod _ fun j _ =>
      (measurable_pi_apply j).pow_const _).aestronglyMeasurable]
  rw [← integral_toReal ?meas ?fin]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun P => (toReal_prod_pow P B m).symm)
  case meas =>
    exact (Finset.measurable_prod _ fun j _ =>
      ((Measure.measurable_coe (hB j)).comp measurable_subtype_coe).pow_const _).aemeasurable
  case fin =>
    exact Filter.Eventually.of_forall fun P =>
      ENNReal.prod_lt_top fun j _ => (ENNReal.pow_ne_top (measure_ne_top _ _)).lt_top

/-- **The i.i.d. mixture determines the mixing measure.** If two finite measures on
`ProbabilityMeasure α` induce the same mixture `π.bind (P ↦ P^{⊗ℕ})`, they are equal.

The mixture's finite-dimensional rectangle probabilities are the mixed moments of the evaluation
maps, and repetitions in the rectangle turn those into mixed monomials. Each finite evaluation
family lands in the compact box `[0,1]^k`, so multivariate moment determinacy identifies its law,
and finite evaluation laws determine the measure. -/
theorem Measure.ext_of_bind_infinitePi_eq [IsFiniteMeasure π₁]
    (h : (π₁.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α))
      = π₂.bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) :
    π₁ = π₂ := by
  have : IsFiniteMeasure π₂ := by
    constructor
    rw [← bind_infinitePi_univ π₂, ← h, bind_infinitePi_univ π₁]
    exact measure_lt_top π₁ _
  refine TauCeti.MeasureTheory.Measure.ext_of_forall_map_probabilityMeasure_eval_eq
    fun k B hB => ?_
  have : IsFiniteMeasure (π₁.map fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ)) :=
    Measure.isFiniteMeasure_map _ _
  have : IsFiniteMeasure (π₂.map fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ)) :=
    Measure.isFiniteMeasure_map _ _
  have hKc : IsCompact (Set.univ.pi fun _ : Fin k => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine Measure.ext_of_forall_integral_monomial_eq_of_support hKc
    (map_eval_family_compl_pi_Icc_eq_zero B hB π₁)
    (map_eval_family_compl_pi_Icc_eq_zero B hB π₂) fun m => ?_
  rw [integral_prod_pow_map_eq_toReal_lintegral B hB m π₁,
    integral_prod_pow_map_eq_toReal_lintegral B hB m π₂,
    lintegral_prod_pow_eq_of_bind_eq h B hB m]

end MeasureTheory

end TauCeti
