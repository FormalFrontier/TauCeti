/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.MixedIID.Const

/-!
# Constant directing measures: the degenerate case of de Finetti

At a constant random measure `ω ↦ p`, the conditional and mixture identities coincide. Thus an
i.i.d. sequence is conditionally i.i.d. with its common law as a constant directing measure.

The equivalence itself holds at an arbitrary index type
(`conditionallyIIDWith_const_of_mixedIIDWith`, `conditionallyIIDWith_const_iff_mixedIIDWith`). The
`iIndepFun` characterizations below stay over `ℕ` for a narrower reason than it may appear.
Independence itself does not need it — Mathlib's `ProbabilityTheory.iIndepFun` is stated for an
arbitrary index type — and neither does the forward direction: `MixedIIDWith.iIndepFun_of_const`
is index-generic, since enumerating a finite subset needs only *some* bijection with `Fin s.card`,
not an order. What is still sequence-level is the *reverse* direction, which reconstructs the
common law as `μ.map (X 0)` and so nominates a reference coordinate that an abstract index type
does not supply. Removing that means restating the constructor with the common law as a parameter.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **At a constant `ν` the conditional identity is free.** The joint law of `(p, block)` is the
block law pushed forward by `Prod.mk p`, and the disintegration `δ_p ⊗ p^{⊗m}` is the product law
pushed forward by the same map, so the mixture identity already gives the joint one. -/
theorem conditionallyIIDWith_const_of_mixedIIDWith {μ : Measure Ω}
    {X : ι → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) :
    ConditionallyIIDWith μ X fun _ => p := by
  by_cases hμ : μ = 0
  · subst μ
    refine ConditionallyIIDWith.intro measurable_const fun m k hk => ?_
    simp
  refine ConditionallyIIDWith.intro measurable_const fun m k hk => ?_
  have hblock_ne : blockLaw μ X k ≠ 0 := by
    rw [h.blockLaw_eq_mixture k hk, Measure.bind_const]
    intro hzero
    have huniv := congrArg (fun q : Measure (Fin m → α) => q Set.univ) hzero
    exact hμ (Measure.measure_univ_eq_zero.mp (by simpa using huniv))
  have hblock : AEMeasurable (fun ω (i : Fin m) => X (k i) ω) μ :=
    AEMeasurable.of_map_ne_zero (by simpa only [blockLaw_def] using hblock_ne)
  calc μ.map (fun ω => (p, fun i : Fin m => X (k i) ω))
      = (μ.map fun ω (i : Fin m) => X (k i) ω).map (Prod.mk p) := by
        rw [measurable_prodMk_left.aemeasurable.map_map_of_aemeasurable hblock]
        rfl
    _ = (μ.bind fun _ : Ω =>
          (ProbabilityMeasure.pi fun _ : Fin m => p).toMeasure).map (Prod.mk p) := by
        rw [← blockLaw_def, h.blockLaw_eq_mixture k hk]
    _ = μ.bind fun _ : Ω =>
          (Measure.dirac p).prod (ProbabilityMeasure.pi fun _ : Fin m => p).toMeasure := by
        rw [Measure.bind_const, Measure.bind_const, Measure.map_smul, Measure.dirac_prod]

/-- **The two de Finetti predicates agree at a constant witness.** In general only
`mixedIIDWith_of_conditionallyIIDWith` is available and the two need not agree; at a constant `ν`
the converse holds too, so they coincide. -/
theorem conditionallyIIDWith_const_iff_mixedIIDWith {μ : Measure Ω}
    {X : ι → Ω → α} {p : ProbabilityMeasure α} :
    (ConditionallyIIDWith μ X fun _ => p) ↔ MixedIIDWith μ X fun _ => p :=
  ⟨mixedIIDWith_of_conditionallyIIDWith, conditionallyIIDWith_const_of_mixedIIDWith⟩

/-- **A constant directing measure means plain i.i.d.**: `fun _ => p` witnesses
`ConditionallyIIDWith` exactly when the coordinates are independent and each has law `p`. -/
theorem conditionallyIIDWith_const_iff_iIndepFun_and_map_eq {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} {p : ProbabilityMeasure α} :
    (ConditionallyIIDWith μ X fun _ => p) ↔ iIndepFun X μ ∧ ∀ i, μ.map (X i) = (p : Measure α) :=
  conditionallyIIDWith_const_iff_mixedIIDWith.trans mixedIIDWith_const_iff_iIndepFun_and_map_eq

/-- **An i.i.d. sequence is conditionally i.i.d.**, with the constant directing measure
`ω ↦ μ.map (X 0)`. This is the sharp form of the roadmap's first worked example: the constant
random measure is a genuine *directing measure*, not merely a mixing representative.
`MixedIIDWith.of_iIndepFun_identDistrib` is the mixture form it projects down to. -/
theorem ConditionallyIIDWith.of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    haveI := hindep.isProbabilityMeasure
    ConditionallyIIDWith μ X
      (fun _ => ⟨μ.map (X 0), Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst⟩) := by
  haveI := hindep.isProbabilityMeasure
  exact conditionallyIIDWith_const_of_mixedIIDWith
    (MixedIIDWith.of_iIndepFun_identDistrib hindep hident)

/-- **An i.i.d. sequence is conditionally i.i.d.** (existential directing-measure form). -/
theorem ConditionallyIID.of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConditionallyIID μ X :=
  haveI := hindep.isProbabilityMeasure
  ConditionallyIID.of_directing (ConditionallyIIDWith.of_iIndepFun_identDistrib hindep hident)

end Probability

end TauCeti
