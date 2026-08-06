/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Construct
public import TauCeti.Probability.Exchangeability.JointPathLaw
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The full-path joint disintegration

`ConditionallyIIDWith μ X ν` constrains the joint law of `(ν, block)` along each *finite* selection
of coordinates. This file upgrades that to the whole path at once: the joint law of the directing
measure together with the entire process is the disintegration `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

## Main results

* `TauCeti.Probability.ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw`

## Implementation

The right-hand side is not a new construction: `iidMixtureLaw (μ.map ν) id` is the canonical
two-stage law of `ConditionallyIID.Construct` — draw a probability measure from the mixing law
`μ.map ν`, then sample i.i.d. from it, keeping the drawn measure as a coordinate. So the theorem
says the abstract conditional predicate is *exactly* realised by that generative construction, which
is a stronger statement than naming a bespoke disintegration measure would be.

Both measures live on `ProbabilityMeasure α × (ℕ → α)`, and the proof identifies them prefix by
prefix. For the joint law that prefix marginal is the defining identity of `ConditionallyIIDWith`
at the selection `Fin n → ℕ`. For the mixture law no fibre calculation is needed either: the
canonical construction is *itself* conditionally i.i.d. (`conditionallyIIDWith_iidMixtureLaw`), so
its own block-level disintegration supplies the prefix marginal, and `iidMixtureLaw_map_directing`
rewrites the first factor back along `ν`. The two agree, and `measure_eq_of_prefixProjPair_map_eq`
promotes that agreement to equality of the full measures.

That last step is where the paired prefix maps `prefixProjPair` earn their keep. Mathlib's
`IsProjectiveLimit` is stated for pure dependent products `∀ i, α i`, so it does not apply to a
product with a fixed first factor; `measure_eq_of_prefixProjPair_map_eq` instead replicates the
first factor at every coordinate to reduce to the honest path case.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 6 (directing measures) — the
  path-level form of the conditional disintegration the directing-measure layer is stated against.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles* (Springer, 2005), §1.1, where
  the conditional predicate is stated blockwise.

The path-level form is what downstream work consumes — empirical measures as objects, the
affine/barycenter representation, and ergodic decomposition all read the joint law of `(ν, X)` in
one piece rather than block by block.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The prefix pushforward of the joint path law is the block-level disintegration, by the defining
identity at the first `n` coordinates. -/
theorem map_prefixProjPair_jointPathLaw_eq_disintegration (h : ConditionallyIIDWith μ X ν)
    (hX : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixProjPair (ProbabilityMeasure α) α n)
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  rw [map_prefixProjPair_jointPathLaw hX h.measurable_directing.aemeasurable n]
  exact h.jointLaw_eq_disintegration (fun i : Fin n => (i : ℕ)) Fin.val_injective

/-- **The prefix pushforward of the canonical mixture law.** Projecting `δ_t ⊗ (P t)^{⊗ℕ}` onto the
first `n` path coordinates leaves `δ_t ⊗ (P t)^{⊗ Fin n}`, fibre by fibre over the mixing law. -/
theorem map_prefixProjPair_iidMixtureLaw {T : Type*} [MeasurableSpace T] {π : Measure T}
    {P : T → ProbabilityMeasure α} (hP : Measurable P) (n : ℕ) :
    (iidMixtureLaw π P).map (prefixProjPair T α n)
      = π.bind fun t =>
          (Measure.dirac t).prod (ProbabilityMeasure.pi fun _ : Fin n => P t).toMeasure := by
  have hker : Measurable fun t : T =>
      (Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α)) :=
    TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const P hP
  -- Fibre by fibre, the prefix projection turns the infinite power into the finite one.
  have hstep : ∀ t : T,
      ((Measure.dirac t).prod (Measure.infinitePi fun _ : ℕ => (P t : Measure α))).map
          (prefixProjPair T α n)
        = (Measure.dirac t).prod (ProbabilityMeasure.pi fun _ : Fin n => P t).toMeasure := by
    intro t
    have hblk : Measurable fun x : ℕ → α => fun i : Fin n => x (i : ℕ) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    have hcomp : (prefixProjPair T α n) ∘ (Prod.mk t)
        = fun x : ℕ → α => (t, fun i : Fin n => x (i : ℕ)) := by
      funext x; simp [prefixProjPair_apply]
    have hfac : (fun x : ℕ → α => (t, fun i : Fin n => x (i : ℕ)))
        = (Prod.mk t) ∘ fun x : ℕ → α => fun i : Fin n => x (i : ℕ) := rfl
    rw [Measure.dirac_prod,
      Measure.map_map (measurable_prefixProjPair T α n) measurable_prodMk_left, hcomp, hfac,
      ← Measure.map_map measurable_prodMk_left hblk,
      TauCeti.MeasureTheory.map_prefixProj_infinitePi_const (P t) n,
      ProbabilityMeasure.toMeasure_pi, Measure.dirac_prod]
  rw [iidMixtureLaw_def,
    TauCeti.MeasureTheory.map_bind hker.aemeasurable (measurable_prefixProjPair T α n)]
  simp_rw [hstep]

/-! ### The full-path disintegration -/

/-- **The full-path joint disintegration.** For a conditionally i.i.d. process the joint law of the
directing measure together with the *whole* path is the disintegration
`∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

The definition of `ConditionallyIIDWith` gives this along each finite selection of coordinates; this
upgrades it to the entire path at once. -/
theorem ConditionallyIIDWith.jointPathLaw_eq_iidMixtureLaw [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, AEMeasurable (X i) μ) :
    jointPathLaw μ X ν = iidMixtureLaw (μ.map ν) id := by
  have : IsFiniteMeasure (jointPathLaw μ X ν) := by
    rw [jointPathLaw_def]; exact Measure.isFiniteMeasure_map _ _
  refine measure_eq_of_prefixProjPair_map_eq fun n => ?_
  set F : ProbabilityMeasure α → Measure (ProbabilityMeasure α × (Fin n → α)) := fun Q =>
    (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure with hF
  have hker : Measurable F :=
    TauCeti.MeasureTheory.measurable_dirac_prod_probabilityMeasure_pi_const_toMeasure _
      measurable_id
  rw [map_prefixProjPair_jointPathLaw_eq_disintegration h hX n,
    map_prefixProjPair_iidMixtureLaw
      (P := (id : ProbabilityMeasure α → ProbabilityMeasure α)) measurable_id n]
  simp only [id_eq]
  rw [← hF, TauCeti.MeasureTheory.bind_map h.measurable_directing.aemeasurable
    hker.aemeasurable]
  rfl

end Probability

end TauCeti
