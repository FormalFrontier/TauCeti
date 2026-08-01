/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.MixedIID.Implications
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# An i.i.d. sequence is mixed i.i.d., exchangeable, and contractable

This file discharges the first worked example of the Exchangeability roadmap
(`TauCetiRoadmap/Exchangeability/README.md`, "Worked examples"):

> The law of an i.i.d. sequence is `MixedIID`, `Exchangeable`, and `Contractable`.

For a sequence `X : ℕ → Ω → α` on a probability space whose coordinates are independent
(`ProbabilityTheory.iIndepFun X μ`) and identically distributed
(`∀ i, IdentDistrib (X i) (X 0) μ μ`), the constant random measure `ω ↦ law of X 0` is a
mixing representative: `MixedIIDWith.of_iIndepFun_identDistrib`. Exchangeability and
contractability then follow from the Layer 0 implications
`MixedIIDWith.exchangeable` and `MixedIIDWith.contractable`.

Only the *conclusions* `Exchangeable` and `Contractable` need `ℕ`. The mixed-i.i.d. results hold
for a family over an arbitrary index type: `MixedIIDWith.of_iIndepFun_map_eq` takes the common law
as a parameter, and `MixedIIDWith.of_iIndepFun_identDistrib_at` takes a caller-supplied reference
coordinate in place of `0`. The unsuffixed `of_iIndepFun_identDistrib` forms are their `ℕ`
specializations.

The mathematical content is the block-law identity: along an injective selection
`k : Fin m → ℕ` the coordinates `X ∘ k` are independent (a subfamily of an independent
family, `ProbabilityTheory.iIndepFun.precomp`) with common law `μ.map (X 0)`, so their joint
law is the `m`-fold product `Measure.pi (fun _ => μ.map (X 0))`
(`ProbabilityTheory.iIndepFun.map_fun_eq_pi_map`); this is exactly the value of the mixture
against a constant mixing representative. The example validates the Layer 0 mixed-i.i.d.
API on the canonical i.i.d. case and needs no material from
`cameronfreer/exchangeability`.

The roadmap's worked-example entry also asks for the sharper statement that an i.i.d. sequence is
genuinely `ConditionallyIID`, with this constant measure as its *directing measure*. That is
`TauCeti.Probability.ConditionallyIIDWith.of_iIndepFun_identDistrib`, in
`TauCeti/Probability/Exchangeability/ConditionallyIID/Const.lean`, which upgrades the mixture form
below; the same file records that a constant witness makes the two predicates equivalent.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Independent coordinates with a common named law are mixed i.i.d.**, at an arbitrary index
type. Naming the common law as a parameter avoids nominating a reference coordinate, which an
abstract index type does not supply; over `ℕ` that reference is `X 0`, and
`MixedIIDWith.of_iIndepFun_identDistrib` recovers that form. -/
theorem MixedIIDWith.of_iIndepFun_map_eq {μ : Measure Ω} {X : ι → Ω → α}
    {p : ProbabilityMeasure α} (hindep : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = (p : Measure α)) :
    MixedIIDWith μ X fun _ => p := by
  haveI := hindep.isProbabilityMeasure
  have hX : ∀ i, AEMeasurable (X i) μ := fun i =>
    AEMeasurable.of_map_ne_zero (by rw [hlaw i]; exact IsProbabilityMeasure.ne_zero _)
  refine MixedIIDWith.intro measurable_const fun m k hk => ?_
  have hindep_k : iIndepFun (fun i : Fin m => X (k i)) μ := hindep.precomp hk
  have hblock : blockLaw μ X k = Measure.pi (fun _ : Fin m => (p : Measure α)) := by
    have h1 : blockLaw μ X k = Measure.pi (fun i : Fin m => μ.map (X (k i))) := by
      rw [blockLaw_def]
      exact hindep_k.map_fun_eq_pi_map fun i => hX (k i)
    rw [h1]
    exact congrArg Measure.pi (funext fun i => hlaw (k i))
  rw [hblock, Measure.bind_const, measure_univ, one_smul, ProbabilityMeasure.toMeasure_pi]

/-- **Independent, identically distributed coordinates are mixed i.i.d.**, at an arbitrary index
type, with the common law `μ.map (X i₀)` as constant mixing representative.

`i₀` is a caller-supplied reference coordinate: an abstract index type provides none, and
`IdentDistrib` needs one to compare against. `MixedIIDWith.of_iIndepFun_map_eq` avoids it entirely
by naming the law instead, and is the better entry point when the law is already known. -/
theorem MixedIIDWith.of_iIndepFun_identDistrib_at {μ : Measure Ω}
    {X : ι → Ω → α} (i₀ : ι) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X i₀) μ μ) :
    haveI := hindep.isProbabilityMeasure
    MixedIIDWith μ X
      (fun _ => (⟨μ.map (X i₀),
        Measure.isProbabilityMeasure_map (hident i₀).aemeasurable_fst⟩ :
          ProbabilityMeasure α)) := by
  haveI := hindep.isProbabilityMeasure
  exact MixedIIDWith.of_iIndepFun_map_eq hindep fun i => (hident i).map_eq

/-- **An i.i.d. sequence is mixed i.i.d.**, with the common law `μ.map (X 0)` as constant mixing
representative. The `ℕ`-indexed specialization of `MixedIIDWith.of_iIndepFun_identDistrib_at` at
the reference coordinate `0`. -/
theorem MixedIIDWith.of_iIndepFun_identDistrib {μ : Measure Ω}
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    haveI := hindep.isProbabilityMeasure
    MixedIIDWith μ X
      (fun _ => (⟨μ.map (X 0),
        Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst⟩ :
          ProbabilityMeasure α)) :=
  MixedIIDWith.of_iIndepFun_identDistrib_at 0 hindep hident

/-- **An i.i.d. family is mixed i.i.d.** (existential mixing-representative form), at an arbitrary
index type, with `i₀` the caller-supplied reference coordinate. -/
theorem MixedIID.of_iIndepFun_identDistrib_at {μ : Measure Ω}
    {X : ι → Ω → α} (i₀ : ι) (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X i₀) μ μ) :
    MixedIID μ X :=
  MixedIID.of_mixingRepresentative
    (MixedIIDWith.of_iIndepFun_identDistrib_at i₀ hindep hident)

/-- **An i.i.d. sequence is mixed i.i.d.** (existential form), the `ℕ`-indexed specialization at
the reference coordinate `0`. -/
theorem MixedIID.of_iIndepFun_identDistrib {μ : Measure Ω}
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    MixedIID μ X :=
  MixedIID.of_iIndepFun_identDistrib_at 0 hindep hident

/-- **An i.i.d. sequence is exchangeable.** Sequence-level, and necessarily so: `Exchangeable` is
defined for `X : ℕ → Ω → α`, so no reference-index parameter would generalize it. The family-level
statement is `MixedIIDWith.exchangeableFamily`. -/
theorem Exchangeable.of_iIndepFun_identDistrib {μ : Measure Ω}
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Exchangeable μ X :=
  (MixedIIDWith.of_iIndepFun_identDistrib hindep hident).exchangeable

/-- **An i.i.d. sequence is contractable.** -/
theorem Contractable.of_iIndepFun_identDistrib {μ : Measure Ω}
    {X : ℕ → Ω → α} (hindep : iIndepFun X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Contractable μ X :=
  (MixedIIDWith.of_iIndepFun_identDistrib hindep hident).contractable

end Probability

end TauCeti
