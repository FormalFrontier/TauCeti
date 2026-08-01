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
The *named-law* constant-witness API is index-generic:
`MixedIIDWith.iIndepFun_of_const`, `mixedIIDWith_const_iff_iIndepFun_and_map_eq`, and
`MixedIIDWith.of_iIndepFun_map_eq` all take an arbitrary index type. Independence itself never
needed `ℕ` — Mathlib's `ProbabilityTheory.iIndepFun` is stated generically — the forward direction
enumerates finite subsets by *some* bijection with `Fin s.card` rather than by an order, and the
reverse direction takes the common law as a parameter instead of reconstructing it from a reference
coordinate.

The `of_iIndepFun_identDistrib` forms come in two shapes. The `_at` versions take a caller-supplied
reference coordinate `i₀` and hold at an arbitrary index type; the unsuffixed ones are their
`ℕ`-indexed specializations at `0`, kept because that is the ergonomic form for sequences and
because existing callers use it.
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
    [IsProbabilityMeasure μ] {X : ι → Ω → α} {p : ProbabilityMeasure α} :
    (ConditionallyIIDWith μ X fun _ => p) ↔ iIndepFun X μ ∧ ∀ i, μ.map (X i) = (p : Measure α) :=
  conditionallyIIDWith_const_iff_mixedIIDWith.trans mixedIIDWith_const_iff_iIndepFun_and_map_eq

/-- **Independent, identically distributed coordinates are conditionally i.i.d.**, at an arbitrary
index type, with the common law `μ.map (X i₀)` as constant directing measure. Conditional rather
than merely mixture-level: at a constant witness the two identities coincide. -/
theorem ConditionallyIIDWith.of_iIndepFun_identDistrib_at {μ : Measure Ω} {X : ι → Ω → α}
    (i₀ : ι) (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X i₀) μ μ) :
    haveI := hindep.isProbabilityMeasure
    ConditionallyIIDWith μ X
      (fun _ => ⟨μ.map (X i₀), Measure.isProbabilityMeasure_map (hident i₀).aemeasurable_fst⟩) := by
  haveI := hindep.isProbabilityMeasure
  exact conditionallyIIDWith_const_of_mixedIIDWith
    (MixedIIDWith.of_iIndepFun_identDistrib_at i₀ hindep hident)

/-- **An i.i.d. sequence is conditionally i.i.d.**, with its common law as constant directing
measure. The `ℕ`-indexed specialization at the reference coordinate `0`. -/
theorem ConditionallyIIDWith.of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    haveI := hindep.isProbabilityMeasure
    ConditionallyIIDWith μ X
      (fun _ => ⟨μ.map (X 0), Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst⟩) :=
  ConditionallyIIDWith.of_iIndepFun_identDistrib_at 0 hindep hident

/-- **An i.i.d. family is conditionally i.i.d.** (existential directing-measure form), at an
arbitrary index type, with `i₀` the caller-supplied reference coordinate. The `ℕ` specialization
follows. -/
theorem ConditionallyIID.of_iIndepFun_identDistrib_at {μ : Measure Ω} {X : ι → Ω → α}
    (i₀ : ι) (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X i₀) μ μ) :
    ConditionallyIID μ X :=
  haveI := hindep.isProbabilityMeasure
  ConditionallyIID.of_directing (ConditionallyIIDWith.of_iIndepFun_identDistrib_at i₀ hindep hident)

/-- **An i.i.d. sequence is conditionally i.i.d.** (existential form), the `ℕ`-indexed
specialization at the reference coordinate `0`. -/
theorem ConditionallyIID.of_iIndepFun_identDistrib {μ : Measure Ω} {X : ℕ → Ω → α}
    (hindep : iIndepFun X μ) (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConditionallyIID μ X :=
  ConditionallyIID.of_iIndepFun_identDistrib_at 0 hindep hident

end Probability

end TauCeti
