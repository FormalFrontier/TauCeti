/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
public import TauCeti.Probability.Process.EmpiricalMeasure
-- Public: the de Finetti corollary is stated for an exchangeable process.
public import TauCeti.Probability.DeFinetti.Theorem
-- Non-public: the fibrewise strong law, the measurability of an observable's integral, and the
-- measurability of a convergence set are used only inside proofs.
import TauCeti.Probability.StrongLaw
import TauCeti.MeasureTheory.Integral.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The conditional strong law of large numbers

A conditionally i.i.d. process obeys the strong law of large numbers **conditionally**: almost
surely, the averages of a bounded observable along the process converge to that observable's
integral against the *directing measure*, not against a deterministic law. Equivalently, the
empirical measures converge to the directing measure, setwise and almost surely.

`ConditionallyIID/EmpiricalMeasure.lean` already gives the mean-square form of this, with the exact
finite-sample error. What is new here is almost-sure convergence, and the strengthening from a
single observable to a whole countable family under one null set.

## Main results

* `ConditionallyIIDWith.tendsto_average_ae` — the conditional strong law for a bounded measurable
  observable;
* `ConditionallyIIDWith.tendsto_integral_empiricalMeasure_ae` — its reading through
  `empiricalMeasure`;
* `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae` and
  `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae_forall` — the setwise form, for one
  measurable set and for a countable family of them under a single null set;
* `deFinetti_tendsto_empiricalMeasure_apply` — for an exchangeable process on a standard Borel
  state space, a directing measure that is recovered as the almost-sure setwise limit of the
  empirical measures.

## Implementation

The conditional statement is reduced to an unconditional one by the full-path joint disintegration
`ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw`: the law of the pair `(ν, X)` on
`ProbabilityMeasure α × (ℕ → α)` is the mixture `∫ δ_Q ⊗ Q^{⊗ℕ} d(μ.map ν)(Q)`. The event

```text
G = {(Q, x) | the averages of `f` along `x` converge to `∫ f dQ`}
```

is measurable — `measurableSet_tendsto_fun`, using that `Q ↦ ∫ f dQ` is measurable for a bounded
observable (`measurable_probabilityMeasure_integral`) — and every fibre `δ_Q ⊗ Q^{⊗ℕ}` of the
mixture puts full mass on it, which is exactly `strong_law_ae_infinitePi` at the law `Q`. Mixing
over `Q` and transporting the resulting almost-sure statement back along `ω ↦ (ν ω, X · ω)` gives
the conditional strong law. No martingale or ergodic input is used: the joint disintegration
already carries all the conditional structure, and Mathlib's strong law does the analysis.

Boundedness of the observable is what makes the argument uniform in `Q`: it gives integrability
against *every* probability measure at once, and it is all the empirical-measure corollaries need.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6 (directing measures), the
  empirical-measure form of the directing-measure theorem. The roadmap's target there is weak
  convergence in `ProbabilityMeasure α` against bounded continuous test functions; that form needs
  a compatible Polish topology on `α`, which `[StandardBorelSpace α]` does not select, so it is not
  attempted here. The setwise almost-sure convergence below is its analytic core, and
  `tendsto_empiricalMeasure_apply_ae_forall` is the "one null set for a countable determining
  class" step such an upgrade consumes.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), §1.1.

No material is adapted from `cameronfreer/exchangeability`, which does not treat empirical
measures.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- **The conditional strong law of large numbers.** For a conditionally i.i.d. process and a
bounded measurable observable `f`, the averages of `f` along the process converge almost surely to
the integral of `f` against the directing measure.

The limit is random: it is `∫ f dν(ω)`, and reduces to a constant exactly when the directing
measure is. -/
theorem ConditionallyIIDWith.tendsto_average_ae [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (X i ω)) atTop
      (𝓝 (∫ y, f y ∂(ν ω : Measure α))) := by
  -- The event, on the joint space of the directing measure and the path, that the averages
  -- converge to the integral against the first coordinate.
  set G : Set (ProbabilityMeasure α × (ℕ → α)) :=
    {z | Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (z.2 i)) atTop
      (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} with hG
  have hGmeas : MeasurableSet G := by
    rw [hG]
    exact MeasureTheory.measurableSet_tendsto_fun
      (fun n => measurable_const.mul (Finset.measurable_sum _ fun i _ =>
        hf.comp ((measurable_pi_apply i).comp measurable_snd)))
      ((TauCeti.MeasureTheory.measurable_probabilityMeasure_integral hf hbdd).comp measurable_fst)
  -- Every fibre of the mixture is an i.i.d. law, where the strong law applies.
  have hfibre : ∀ Q : ProbabilityMeasure α,
      ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))) Gᶜ = 0 := by
    intro Q
    have hint : Integrable f (Q : Measure α) :=
      Integrable.of_bound hf.aestronglyMeasurable C
        (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbdd x)
    have hsl : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => (Q : Measure α)), (Q, x) ∈ G := by
      filter_upwards [strong_law_ae_infinitePi (Q : Measure α) hf hint] with x hx
      rw [hG]
      simpa only [Set.mem_ofPred_eq, smul_eq_mul] using hx
    rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hGmeas.compl]
    exact ae_iff.mp hsl
  have hker : Measurable fun Q : ProbabilityMeasure α =>
      (Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α)) :=
    TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
      (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id
  have hnull : jointPathLaw μ X ν Gᶜ = 0 := by
    rw [h.jointPathLaw_eq_iidMixtureLaw hX]
    simp only [iidMixtureLaw_def, id_eq]
    rw [Measure.bind_apply hGmeas.compl hker.aemeasurable]
    simp [hfibre]
  -- Transport the almost-sure statement back to the sample space.
  have hjointae : ∀ᵐ z ∂(μ.map fun ω => (ν ω, fun i => X i ω)), z ∈ G :=
    mem_ae_iff.mpr (by rwa [jointPathLaw_def] at hnull)
  have hmap : AEMeasurable
      (fun ω => (ν ω, fun i => X i ω) : Ω → ProbabilityMeasure α × (ℕ → α)) μ :=
    h.measurable_directing.aemeasurable.prodMk (aemeasurable_pi_lambda _ hX)
  filter_upwards [(ae_map_iff hmap
    (p := fun z : ProbabilityMeasure α × (ℕ → α) => z ∈ G) hGmeas).mp hjointae] with ω hω
  simpa only [hG, Set.mem_ofPred_eq] using hω

/-- **The conditional strong law, read through empirical measures.** The integral of a bounded
measurable observable against the empirical measure of a conditionally i.i.d. process converges
almost surely to its integral against the directing measure. -/
theorem ConditionallyIIDWith.tendsto_integral_empiricalMeasure_ae [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hbdd : ∀ x, |f x| ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ∫ y, f y ∂(empiricalMeasure (fun i => X i ω) n : Measure α)) atTop
      (𝓝 (∫ y, f y ∂(ν ω : Measure α))) := by
  filter_upwards [h.tendsto_average_ae hX hf hbdd] with ω hω
  -- `empiricalMeasure … n` averages the first `n + 1` terms, so the limit is along the shifted
  -- sequence.
  refine Tendsto.congr (fun n => ?_) (hω.comp (tendsto_add_atTop_nat 1))
  rw [Function.comp_apply, integral_empiricalMeasure hf.stronglyMeasurable, smul_eq_mul]

/-- **Empirical measures converge setwise, almost surely.** For a conditionally i.i.d. process and
a fixed measurable set, the empirical frequency of that set converges almost surely to the mass the
directing measure gives it.

The mean-square form of the same convergence, with its exact finite-sample error, is
`ConditionallyIIDWith.tendsto_integral_empiricalMeasure_apply_sub_sq`. -/
theorem ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    {B : Set α} (hB : MeasurableSet B) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n : ℕ => ((empiricalMeasure (fun i => X i ω) n : Measure α) B).toReal) atTop
      (𝓝 (((ν ω : Measure α) B).toReal)) := by
  have hf : Measurable (B.indicator (1 : α → ℝ)) := measurable_one.indicator hB
  have hbdd : ∀ x, |B.indicator (1 : α → ℝ) x| ≤ 1 := fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  filter_upwards [h.tendsto_integral_empiricalMeasure_ae hX hf hbdd] with ω hω
  simpa only [integral_indicator_one hB, measureReal_def] using hω

/-- **A single null set serves a countable family of sets.** Almost surely, the empirical
frequencies of *every* member of a countable family of measurable sets converge simultaneously.

Interchanging the two quantifiers is not cosmetic: an upgrade of setwise convergence to convergence
in the weak topology on `ProbabilityMeasure α` tests against a countable determining class, and
needs the null set to be chosen before the class is inspected. -/
theorem ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae_forall [IsFiniteMeasure μ]
    {ι : Type*} [Countable ι] (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    {B : ι → Set α} (hB : ∀ j, MeasurableSet (B j)) :
    ∀ᵐ ω ∂μ, ∀ j, Tendsto
      (fun n : ℕ => ((empiricalMeasure (fun i => X i ω) n : Measure α) (B j)).toReal) atTop
      (𝓝 (((ν ω : Measure α) (B j)).toReal)) :=
  ae_all_iff.2 fun j => h.tendsto_empiricalMeasure_apply_ae hX (hB j)

/-- **De Finetti's theorem in setwise empirical-measure form.** An exchangeable process valued in a
nonempty standard Borel space has a directing measure which is recovered, almost surely and on
every measurable set, as the limit of the empirical measures of the process.

The directing measure is thus not merely asserted to exist: it is the pathwise limit of an explicit
statistic of the process. The weak-topology form of the same statement, testing against bounded
continuous functions, needs a compatible Polish topology on `α` and is not proved here. -/
theorem deFinetti_tendsto_empiricalMeasure_apply [StandardBorelSpace α] [Nonempty α]
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ n, Measurable (X n)) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      ∀ B : Set α, MeasurableSet B → ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ((empiricalMeasure (fun i => X i ω) n : Measure α) B).toReal) atTop
        (𝓝 (((ν ω : Measure α) B).toReal)) := by
  obtain ⟨ν, hν⟩ := (conditionallyIID_of_exchangeable hX hX_meas).exists_directing
  exact ⟨ν, hν, fun B hB =>
    hν.tendsto_empiricalMeasure_apply_ae (fun i => (hX_meas i).aemeasurable) hB⟩

end Probability

end TauCeti
