/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
public import TauCeti.Probability.Process.EmpiricalMeasure
-- Non-public: the fibrewise strong law, the measurability of an observable's integral, and the
-- measurability of a convergence set are used only inside proofs.
import TauCeti.Probability.StrongLaw
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# The conditional strong law of large numbers

A conditionally i.i.d. process obeys the strong law of large numbers **conditionally**: almost
surely, the averages of a bounded observable along the process converge to that observable's
integral against the *directing measure*, not against a deterministic law. Taking the observable to
be an indicator: for each *fixed* measurable set, the empirical frequency of that set converges
almost surely to the mass the directing measure gives it.

`ConditionallyIID/EmpiricalMeasure.lean` already gives the `L²` form of this, with the exact
finite-sample error. What is new here is almost-sure convergence, and the strengthening from a
single measurable set to a countable family of sets under one null set.

The quantifier order matters, and `∀ B, ∀ᵐ ω` is the strongest order available here: the null set
genuinely depends on the set tested. Setwise almost-sure convergence — one null set outside which
the empirical measures converge on *every* measurable set at once — is false as soon as the
directing measure is nonatomic, since the countable range of the sample path then carries empirical
mass `1` and directing mass `0`. Countability is exactly the room there is to improve the order,
and `tendsto_empiricalMeasure_apply_ae_forall` takes all of it.

## Main results

* `ConditionallyIIDWith.tendsto_average_ae` — the conditional strong law for a bounded measurable
  observable valued in a Banach space;
* `ConditionallyIIDWith.tendsto_integral_empiricalMeasure_ae` — its reading through
  `empiricalMeasure`;
* `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae` and
  `ConditionallyIIDWith.tendsto_empiricalMeasure_apply_ae_forall` — the empirical frequencies, for
  one fixed measurable set and for a countable family of them under a single null set;

The de Finetti endpoint of these — the same statement for an *exchangeable* process, where the
directing measure has to be produced first — is `deFinetti_tendsto_empiricalMeasure_apply` in
`DeFinetti/EmpiricalMeasure.lean`. It is kept out of this module so that the conditional strong law
does not drag the de Finetti summit into every importer's closure.

## Implementation

The conditional statement is reduced to an unconditional one by the full-path joint disintegration
`ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw`: the law of the pair `(ν, X)` on
`ProbabilityMeasure α × (ℕ → α)` is the mixture `∫ δ_Q ⊗ Q^{⊗ℕ} d(μ.map ν)(Q)`. The event

```text
G = {(Q, x) | the averages of `f` along `x` converge to `∫ f dQ`}
```

is measurable — `measurableSet_tendsto_fun`, using that `Q ↦ ∫ f dQ` is measurable, which is
Mathlib's `MeasureTheory.StronglyMeasurable.integral_kernel` for the coercion kernel
`ProbabilityMeasure α → Measure α` — and every fibre `δ_Q ⊗ Q^{⊗ℕ}` of the
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
  attempted here. The fixed-set almost-sure convergence below is its analytic core, and
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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
/-- The set of pairs `(Q, x)` for which the averages of `f` along the path `x` converge to the
integral of `f` against `Q` is measurable. -/
private theorem measurableSet_tendsto_average_integral {f : α → E} (hf : Measurable f) :
    MeasurableSet {z : ProbabilityMeasure α × (ℕ → α) |
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
        (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} :=
  MeasureTheory.measurableSet_tendsto_fun
    (fun _n => (Finset.measurable_sum _ fun i _ =>
      hf.comp ((measurable_pi_apply i).comp measurable_snd)).const_smul _)
    -- `Q ↦ ∫ f dQ` is measurable: it is the integral against the coercion kernel
    -- `ProbabilityMeasure α → Measure α`.
    ((hf.stronglyMeasurable.integral_kernel
      (κ := ⟨((↑) : ProbabilityMeasure α → Measure α), measurable_subtype_coe⟩)).measurable.comp
        measurable_fst)

/-- **On each fibre of the mixture the averages converge almost surely.** For `f` measurable and
integrable against a probability measure `Q`, the pairing of `Q` with an i.i.d. `Q`-path lands
almost surely in the set where the averages of `f` converge to `∫ f dQ`.

This is the classical strong law, read on the fibre `(δ_Q, Q^{⊗ℕ})`; nothing about the directing
measure or the process is involved. -/
private theorem measure_compl_tendsto_average_integral_eq_zero {f : α → E} (hf : Measurable f)
    (Q : ProbabilityMeasure α) (hint : Integrable f (Q : Measure α)) :
    ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α)))
      {z : ProbabilityMeasure α × (ℕ → α) |
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
          (𝓝 (∫ y, f y ∂(z.1 : Measure α)))}ᶜ = 0 := by
  have hsl : ∀ᵐ x ∂(Measure.infinitePi fun _ : ℕ => (Q : Measure α)),
      (Q, x) ∈ {z : ProbabilityMeasure α × (ℕ → α) |
        Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
          (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} := by
    filter_upwards [strong_law_ae_infinitePi (Q : Measure α) hf hint] with x hx
    simpa only [Set.mem_ofPred_eq] using hx
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
    (measurableSet_tendsto_average_integral hf).compl]
  exact ae_iff.mp hsl

/-- **The conditional strong law of large numbers.** For a conditionally i.i.d. process and a
bounded measurable observable `f` valued in a Banach space, the averages of `f` along the process
converge almost surely to the integral of `f` against the directing measure.

The limit is random: it is `∫ f dν(ω)`. It reduces to a constant when the directing measure is
almost everywhere constant, but also for observables — `f = 0`, say — whose integral happens not to
see the randomness of `ν`. -/
theorem ConditionallyIIDWith.tendsto_average_ae [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ)
    {f : α → E} (hf : Measurable f) {C : ℝ} (hbdd : ∀ x, ‖f x‖ ≤ C) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (X i ω)) atTop
      (𝓝 (∫ y, f y ∂(ν ω : Measure α))) := by
  -- The event, on the joint space of the directing measure and the path, that the averages
  -- converge to the integral against the first coordinate.
  set G : Set (ProbabilityMeasure α × (ℕ → α)) :=
    {z | Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, f (z.2 i)) atTop
      (𝓝 (∫ y, f y ∂(z.1 : Measure α)))} with hG
  have hGmeas : MeasurableSet G := by
    rw [hG]
    exact measurableSet_tendsto_average_integral hf
  -- Every fibre of the mixture is an i.i.d. law, where the strong law applies.
  have hfibre : ∀ Q : ProbabilityMeasure α,
      ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))) Gᶜ = 0 := by
    rw [hG]
    exact fun Q => measure_compl_tendsto_average_integral_eq_zero hf Q
      (Integrable.of_bound hf.aestronglyMeasurable C (.of_forall hbdd))
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
  have hbdd' : ∀ x, ‖f x‖ ≤ C := fun x => by simpa only [Real.norm_eq_abs] using hbdd x
  filter_upwards [h.tendsto_average_ae hX hf hbdd'] with ω hω
  -- `empiricalMeasure … n` averages the first `n + 1` terms, so the limit is along the shifted
  -- sequence.
  refine Tendsto.congr (fun n => ?_) (hω.comp (tendsto_add_atTop_nat 1))
  rw [Function.comp_apply, integral_empiricalMeasure hf.stronglyMeasurable]

/-- **Empirical frequencies converge almost surely, on each fixed measurable set.** For a
conditionally i.i.d. process and a fixed measurable set `B`, the empirical frequency of `B`
converges almost surely to the mass the directing measure gives it.

The null set depends on `B`, and outside a countable family of sets it must:
`tendsto_empiricalMeasure_apply_ae_forall` is as far as the quantifiers can be interchanged.

The `L²` form of the same convergence is
`ConditionallyIIDWith.tendsto_integral_empiricalMeasure_apply_sub_sq`, and
`ConditionallyIIDWith.integral_empiricalMeasure_apply_sub_sq` computes its exact finite-sample
error. -/
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

end Probability

end TauCeti
