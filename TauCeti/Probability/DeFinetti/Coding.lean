/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the coding map and its defining property appear in every statement below.
public import TauCeti.Probability.Kernel.Randomization
-- Public: the barycenter is the right-hand side of the mixture identity, and this module
-- re-exports the mixing-law existence theorem the representation consumes.
public import TauCeti.Probability.DeFinetti.Barycenter
-- Public: `jointPathLaw` and `iidMixtureLaw` appear in the joint statements.
public import TauCeti.Probability.Exchangeability.ConditionallyIID.PathDisintegration
-- Non-public: de Finetti's theorem is used only inside proofs.
import TauCeti.Probability.DeFinetti.Theorem
import TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The coding representation of an exchangeable sequence

De Finetti's theorem describes an exchangeable sequence by a *conditional law*: there is a random
probability measure `ν` such that, given `ν`, the coordinates are i.i.d. `ν`. This file converts
that description into a *functional* one. Writing `ϑ` for a sequence of independent uniform
variables on the unit interval, independent of `ν`, there is a single jointly measurable

```text
f : ProbabilityMeasure α → I → α
```

with

```text
(ν, X) =ᵈ (ν, (f ν ϑᵢ)ᵢ).
```

Thus, in distribution, an exchangeable sequence is a fixed measurable function of one random
parameter — its directing measure — and an independent i.i.d. uniform noise sequence, with all the
randomness of the sequence carried by the noise. This is the sequence case of the representations
in the Aldous–Hoover family, and the shape in which those representations are stated.

The function is `unitIntervalCoding α` of
`TauCeti.Probability.Kernel.Randomization`, the same one for every process on `α`; only the law of
the parameter changes. The converse holds for an arbitrary jointly measurable `f`, without a
standard Borel hypothesis and for an arbitrary parameter space and arbitrary exchangeable noise
(`exchangeableLaw_map_prod_coding`), so the two together characterize exchangeability
(`exchangeableLaw_iff_exists_coding`).

## Main results

* `TauCeti.Probability.map_prod_unitIntervalCoding_eq_deFinettiBarycenter` and
  `TauCeti.Probability.map_prod_unitIntervalCoding_eq_iidMixtureLaw` — coding a mixing law by
  uniform noise reproduces the de Finetti barycenter, and, keeping the parameter, the canonical
  conditionally i.i.d. law.
* `TauCeti.Probability.ConditionallyIIDWith.jointPathLaw_eq_map_unitIntervalCoding` — the joint law
  of a directing measure and its process is the law of the coded pair.
* `TauCeti.Probability.deFinetti_coding` — **the representation**: the joint law of an exchangeable
  process and its directing measure is the law of the coded parameter-noise pair.
* `TauCeti.Probability.ExchangeableLaw.exists_eq_map_unitIntervalCoding` and
  `TauCeti.Probability.exchangeableLaw_iff_exists_coding` — the path-law forms, the second an
  equivalence.

## Implementation

Everything reduces to two identities about `Measure.prod`: evaluating the pushforward of
`π ⊗ (uniform)^{⊗ℕ}` fibrewise over the parameter turns the coding into the countable power
`map_infinitePi_volume_unitIntervalCoding`, which is exactly the integrand of
`deFinettiBarycenter_apply` and of `iidMixtureLaw`. No new measure theory is needed: the analytic
content is Mathlib's `ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval` and the
probabilistic content is the already-proved de Finetti theorem.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "exchangeable arrays and the
Aldous–Hoover representation": a functional representation is the form those theorems take, and the
sequence case built here is the base of that tower. No material is adapted from
`cameronfreer/exchangeability`, which stops at the conditional-law form of de Finetti.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005,
  Chapter 1, Proposition 1.4.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section Coding

variable [StandardBorelSpace α] [Nonempty α]

/-- Joint measurability of the canonical coordinatewise coding map. -/
theorem measurable_unitIntervalCodingPath :
    Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      fun i => unitIntervalCoding α p.1 (p.2 i) :=
  measurable_pi_uncurry_prod (measurable_uncurry_unitIntervalCoding α)

/-- **Coding a mixing law, keeping the parameter.** Retaining the drawn probability measure as a
coordinate, the same construction produces the canonical conditionally i.i.d. law `iidMixtureLaw`:
the parameter is not merely a mixing representative of the coded sequence but its directing
measure. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_iidMixtureLaw (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))
      = iidMixtureLaw π id := by
  have hG : Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hG hs, Measure.prod_apply (hG hs), iidMixtureLaw_def,
    Measure.bind_apply hs (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
      (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).aemeasurable]
  refine lintegral_congr fun P => ?_
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hs, id_eq,
    ← map_infinitePi_volume_unitIntervalCoding (ι := ℕ) P,
    Measure.map_apply (measurable_pi_unitIntervalCoding P) (measurable_prodMk_left hs)]
  -- Both preimages are `{u | (P, fun i => unitIntervalCoding α P (u i)) ∈ s}`.
  rfl

/-- **Coding a mixing law.** Drawing a probability measure from `π`, then coding an independent
i.i.d. uniform sequence by it, produces the de Finetti barycenter of `π`. -/
@[simp]
theorem map_prod_unitIntervalCoding_eq_deFinettiBarycenter (π : Measure (ProbabilityMeasure α)) :
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p i => unitIntervalCoding α p.1 (p.2 i))
      = deFinettiBarycenter π := by
  have hG : Measurable fun p : ProbabilityMeasure α × (ℕ → I) =>
      (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  calc
    (π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p i => unitIntervalCoding α p.1 (p.2 i))
        = ((π.prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
            (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i)))).map Prod.snd := by
              rw [Measure.map_map measurable_snd hG]
              rfl
    _ = (iidMixtureLaw π id).map Prod.snd := by
          rw [map_prod_unitIntervalCoding_eq_iidMixtureLaw]
    _ = deFinettiBarycenter π := by
          rw [iidMixtureLaw_def, TauCeti.MeasureTheory.map_bind
            (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const
              (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).aemeasurable
            measurable_snd, deFinettiBarycenter_def]
          simp

/-- **The coding representation of a conditionally i.i.d. process.** The joint law of a directing
measure and the whole path is the joint law of a parameter drawn from the mixing law and the path
obtained by coding independent uniform noise by that parameter.

Keeping the directing measure as a coordinate is what makes this a representation of the process
and not merely of its path law. -/
theorem ConditionallyIIDWith.jointPathLaw_eq_map_unitIntervalCoding {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) :
    jointPathLaw μ X ν =
      ((μ.map ν).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i))) := by
  rw [h.jointPathLaw_eq_iidMixtureLaw hX, map_prod_unitIntervalCoding_eq_iidMixtureLaw]

/-- **The coding representation of an exchangeable process.** An exchangeable sequence in a nonempty
standard Borel space has a directing measure `ν` — it is conditionally i.i.d. `ν` — such that the
joint law of `(ν, X)` equals the law of the pair obtained by applying one fixed measurable map
coordinatewise to `ν` and independent i.i.d. uniform noise.

This is the functional form of de Finetti's theorem: all the randomness of the sequence beyond its
directing measure is the uniform noise. -/
theorem deFinetti_coding {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX_meas : ∀ n, AEMeasurable (X n) μ) (hX : Exchangeable μ X) :
    ∃ ν : Ω → ProbabilityMeasure α, ConditionallyIIDWith μ X ν ∧
      jointPathLaw μ X ν =
        ((μ.map ν).prod (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          (fun p => (p.1, fun i => unitIntervalCoding α p.1 (p.2 i))) := by
  obtain ⟨ν, hν⟩ := conditionallyIID_iff.mp (deFinetti hX_meas hX)
  exact ⟨ν, hν, hν.jointPathLaw_eq_map_unitIntervalCoding hX_meas⟩

/-- **The coding representation of an exchangeable path law.** An exchangeable probability measure
on `ℕ → α` is the law of a coded i.i.d. uniform sequence, for a mixing law on
`ProbabilityMeasure α`. -/
theorem ExchangeableLaw.exists_eq_map_unitIntervalCoding {ρ : Measure (ℕ → α)}
    [IsProbabilityMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure α),
      ρ = ((π : Measure (ProbabilityMeasure α)).prod
            (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
          fun p i => unitIntervalCoding α p.1 (p.2 i) := by
  obtain ⟨π, hπ, -⟩ := hρ.existsUnique_mixingLaw
  exact ⟨π, by rw [map_prod_unitIntervalCoding_eq_deFinettiBarycenter, ← hπ]⟩

/-- **Exchangeability is exactly codability.** A probability law on `ℕ → α`, with `α` nonempty
standard Borel, is exchangeable iff it is the law of a jointly measurable function of a random
parameter and an independent i.i.d. uniform sequence, applied coordinatewise.

The forward direction produces the canonical coding map `unitIntervalCoding α` and takes the
parameter to be the directing measure itself; the converse holds for an arbitrary jointly
measurable `f`. -/
theorem exchangeableLaw_iff_exists_coding {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] :
    ExchangeableLaw ρ ↔
      ∃ (π : ProbabilityMeasure (ProbabilityMeasure α)) (f : ProbabilityMeasure α → I → α),
        Measurable (Function.uncurry f) ∧
          ρ = ((π : Measure (ProbabilityMeasure α)).prod
                (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
              fun p i => f p.1 (p.2 i) := by
  refine ⟨fun hρ => ?_, fun ⟨π, f, hf, hρ⟩ => ?_⟩
  · obtain ⟨π, hπ⟩ := hρ.exists_eq_map_unitIntervalCoding
    exact ⟨π, unitIntervalCoding α, measurable_uncurry_unitIntervalCoding α, hπ⟩
  · have : IsProbabilityMeasure (π : Measure (ProbabilityMeasure α)) := π.2
    have hnoise : ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (volume : Measure I)) := by
      simpa only [ProbabilityMeasure.coe_mk] using
        exchangeableLaw_infinitePi_const (⟨volume, inferInstance⟩ : ProbabilityMeasure I)
    rw [hρ]
    exact exchangeableLaw_map_prod_coding _ hnoise hf

/-- The path-law form of `deFinetti_coding`: the law of an exchangeable process is the law of a
coded i.i.d. uniform sequence. -/
theorem exists_pathLaw_eq_map_unitIntervalCoding {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (hX_meas : ∀ n, AEMeasurable (X n) μ) (hX : Exchangeable μ X) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure α),
      pathLaw μ X = ((π : Measure (ProbabilityMeasure α)).prod
          (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
        fun p i => unitIntervalCoding α p.1 (p.2 i) := by
  have : IsProbabilityMeasure (pathLaw μ X) :=
    Measure.isProbabilityMeasure_map (aemeasurable_pi_lambda _ hX_meas)
  exact ((exchangeable_iff_exchangeableLaw_pathLaw hX_meas).mp hX).exists_eq_map_unitIntervalCoding

end Coding

end Probability

end TauCeti
