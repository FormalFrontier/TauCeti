/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Implications
-- Non-public: used only inside the proof below.
import TauCeti.Probability.Exchangeability.FiniteMarginals
import TauCeti.MeasureTheory.Measure.GiryMonad
import TauCeti.MeasureTheory.Measure.MixtureInjective

/-!
# The path law of a mixed i.i.d. process

A mixed i.i.d. process has, as its **path law**, a mixture of infinite product measures: for a
mixing representative `ν`,

```text
pathLaw μ X = ∫ P^{⊗ℕ} d(μ.map ν)(P)
```

written in the `Measure.bind` idiom.

## Main results

* `pathLaw_eq_bind_infinitePi_of_mixedIIDWith` — the representation, for an arbitrary mixing
  representative.
* `mixedIID_mixingLaw_eq_of_pathLaw_eq` — the mixing law is a function of the path law alone.
* `mixedIID_mixingLaw_unique` — the mixing law `μ.map ν` is determined by the process.
* `MixedIID.existsUnique_mixingLaw` — a mixed i.i.d. process under a probability law has a unique
  probability mixing law in the infinite-product representation.

The witness-level representation and uniqueness results need only `[IsFiniteMeasure μ]`,
a.e.-measurable coordinates, and the witness. `MixedIID.existsUnique_mixingLaw` assumes
`[IsProbabilityMeasure μ]` only so that the unique mixing law can be bundled as a
`ProbabilityMeasure`. No standard-Borel hypothesis appears: that is the cost of *supplying* a
canonical witness, not of using one, so this file carries no de Finetti dependency.

## Implementation

`MixedIIDWith` constrains only the *finite* blocks, so the work is the passage from finite blocks to
the whole path. The two sides are compared through their finite-dimensional prefix marginals via
`measure_eq_of_prefixProj_map_eq`: on the left `map_prefixProj_pathLaw` and the block identity, on
the right `map_bind` to push the marginal inside the mixture, `map_prefixProj_infinitePi_const` to
recognise each prefix marginal of an infinite power as the corresponding finite power, and
`bind_map` to re-index the mixture over `μ` rather than over `μ.map ν`.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 6, the directing-measure API bullet
asking for the mixture-of-product-measures form. That bullet also asks for `π` to be the *unique*
law of `ν`, which `mixedIID_mixingLaw_unique` now supplies: the mixture representation turns two
witnesses into the same `Measure.bind`, and injectivity of `π ↦ π.bind (P ↦ P^{⊗ℕ})`
(`Measure.ext_of_bind_infinitePi_eq`) identifies the mixing laws. The roadmap name
`deFinetti_mixture`, which derives the unique representation from exchangeability rather than
assuming a witness, lives in `TauCeti.Probability.DeFinetti.Representation`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The mixture representation of a path law.** If `ν` is a mixing representative for `X`, the
path law of `X` is the `μ.map ν`-mixture of the infinite product measures `P^{⊗ℕ}`. -/
theorem pathLaw_eq_bind_infinitePi_of_mixedIIDWith {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) :
    pathLaw μ X = (μ.map ν).bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  have hΦ : AEMeasurable (fun ω => fun i => X i ω : Ω → ℕ → α) μ :=
    aemeasurable_pi_lambda _ h.aemeasurable
  have hν : AEMeasurable ν μ := h.measurable_mixingRepresentative.aemeasurable
  have hpow : AEMeasurable (fun P : ProbabilityMeasure α =>
      Measure.infinitePi fun _ : ℕ => (P : Measure α)) (μ.map ν) :=
    TauCeti.MeasureTheory.measurable_infinitePi_const.aemeasurable
  have : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  refine measure_eq_of_prefixProj_map_eq fun n => ?_
  have hfin : AEMeasurable (fun P : ProbabilityMeasure α =>
      (ProbabilityMeasure.pi fun _ : Fin n => P).toMeasure) (μ.map ν) :=
    TauCeti.MeasureTheory.aemeasurable_probabilityMeasure_pi_const_toMeasure
      (fun P : ProbabilityMeasure α => P) measurable_id.aemeasurable
  -- the prefix marginal of each infinite power is the corresponding finite power
  have hstep : ∀ P : ProbabilityMeasure α,
      (Measure.infinitePi fun _ : ℕ => (P : Measure α)).map (prefixProj α n)
        = (ProbabilityMeasure.pi fun _ : Fin n => P).toMeasure := by
    intro P
    have hp : prefixProj α n = fun x : ℕ → α => fun i : Fin n => x i := rfl
    rw [hp, ProbabilityMeasure.toMeasure_pi,
      TauCeti.MeasureTheory.map_prefixProj_infinitePi_const P n]
  calc (pathLaw μ X).map (prefixProj α n)
      = μ.bind fun ω => (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
        rw [map_prefixProj_pathLaw μ hΦ n, h.prefixLaw_eq_mixture n]
    _ = ((μ.map ν).bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)).map
          (prefixProj α n) := by
        rw [TauCeti.MeasureTheory.map_bind hpow (measurable_prefixProj n)]
        simp_rw [hstep]
        rw [TauCeti.MeasureTheory.bind_map hν hfin]
        rfl

/-- **The mixing law is a function of the path law.** Two mixed i.i.d. processes with the same path
law — on possibly different sample spaces — have mixing representatives with the same law.

This is the sharp form of mixing-law uniqueness: the mixture representation writes the path law as
`π.bind (P ↦ P^{⊗ℕ})` for `π = μ.map ν`, and that assignment is injective
(`Measure.ext_of_bind_infinitePi_eq`), so the path law already determines `π`. Comparing two
witnesses for one and the same process (`mixedIID_mixingLaw_unique`) is the special case
`hpath = rfl`. -/
theorem mixedIID_mixingLaw_eq_of_pathLaw_eq {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} [IsFiniteMeasure μ] {μ' : Measure Ω'} [IsFiniteMeasure μ']
    {X : ℕ → Ω → α} {Y : ℕ → Ω' → α}
    {ν : Ω → ProbabilityMeasure α} {ν' : Ω' → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) (h' : MixedIIDWith μ' Y ν')
    (hpath : pathLaw μ X = pathLaw μ' Y) :
    μ.map ν = μ'.map ν' := by
  have : IsFiniteMeasure (μ.map ν) := Measure.isFiniteMeasure_map _ _
  refine TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq ?_
  rw [← pathLaw_eq_bind_infinitePi_of_mixedIIDWith h,
    ← pathLaw_eq_bind_infinitePi_of_mixedIIDWith h', hpath]

/-- **Uniqueness of the mixing law.** Two mixing representatives for the same process induce the
same law on `ProbabilityMeasure α`.

Only the *law* `μ.map ν` is unique, not the witness. For a nondegenerate mixing law an independent
copy of a mixing representative is another one, so no witness-level a.e.-equality theorem can
conclude `ν =ᵐ[μ] ν'` from `MixedIIDWith` alone; a.e. uniqueness of the witness belongs to the
conditional predicate (`conditionallyIID_ae_unique`).

*Finiteness* of `μ` is load-bearing rather than decorative: for an infinite base measure, distinct
mixing measures can produce identical `∞`-valued finite-dimensional mixtures, so mixing-law
uniqueness fails at the hypothesis-light generality the definitions otherwise enjoy.

Normalization, however, is not needed. The roadmap states this target with
`[IsProbabilityMeasure μ]`, but the justification it gives only separates finite from infinite base
measures, and the proof goes through for any finite `μ`. -/
theorem mixedIID_mixingLaw_unique {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    {ν ν' : Ω → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) (h' : MixedIIDWith μ X ν') :
    μ.map ν = μ.map ν' :=
  mixedIID_mixingLaw_eq_of_pathLaw_eq h h' rfl

/-- **Existence and uniqueness of the mixing law.** A mixed i.i.d. process under a probability
law has a unique probability measure `π` on `ProbabilityMeasure α` such that its path law is
the `π`-mixture of the infinite product measures `P^{⊗ℕ}`.

This identifies the mixing law intrinsically from the path law, rather than merely comparing the
pushforwards of two supplied mixing representatives as `mixedIID_mixingLaw_unique` does. -/
theorem MixedIID.existsUnique_mixingLaw {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} (h : MixedIID μ X) :
    ∃! π : ProbabilityMeasure (ProbabilityMeasure α),
      pathLaw μ X = (π : Measure (ProbabilityMeasure α)).bind
        fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α) := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  let π : ProbabilityMeasure (ProbabilityMeasure α) :=
    ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure Ω)
      hν.measurable_mixingRepresentative.aemeasurable
  refine ⟨π, ?_, ?_⟩
  · change pathLaw μ X = (Measure.map ν μ).bind
      fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)
    exact pathLaw_eq_bind_infinitePi_of_mixedIIDWith hν
  · intro π' hπ'
    apply ProbabilityMeasure.toMeasure_injective
    refine TauCeti.MeasureTheory.Measure.ext_of_bind_infinitePi_eq ?_
    change (π' : Measure (ProbabilityMeasure α)).bind
        (fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)) =
      (Measure.map ν μ).bind fun P => Measure.infinitePi fun _ : ℕ => (P : Measure α)
    exact hπ'.symm.trans (pathLaw_eq_bind_infinitePi_of_mixedIIDWith hν)

end Probability

end TauCeti
