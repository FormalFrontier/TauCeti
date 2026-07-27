/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
public import TauCeti.Probability.Exchangeability.IID

/-!
# Constant directing measures: the degenerate case of de Finetti

A *constant* random measure `ω ↦ p` is the degenerate mixing law. This file shows that for such a
`ν` the whole de Finetti hierarchy collapses: `MixedIIDWith`, `ConditionallyIIDWith`, and plain
independence with common law `p` all say the same thing.

That collapse is exactly what the general theory warns is *false* for a nondegenerate mixing law:
`MixedIIDWith μ X ν` constrains only each block's marginal, so an independent copy of a directing
measure witnesses it without the process being conditionally i.i.d. given that copy. When `ν` is
constant there is nothing left to be independent of, and the two predicates agree.

## Main results

* `MixedIIDWith.blockLaw_eq_pi_of_const`, `MixedIIDWith.aemeasurable_of_const`,
  `MixedIIDWith.map_eq_of_const` — what a constant mixing representative says: every injective
  block law is the `m`-fold product of `p`, every coordinate is a.e. measurable, and every
  coordinate has law `p`.
* `mixedIIDWith_const_iff_iIndepFun_and_map_eq` — a constant `p` is a mixing representative exactly
  when the coordinates are independent with common law `p`.
* `conditionallyIIDWith_const_iff_mixedIIDWith` — at a constant `ν` the conditional and mixture
  identities coincide, and `conditionallyIIDWith_const_iff_iIndepFun_and_map_eq` reads off the
  resulting characterization.
* `ConditionallyIIDWith.of_iIndepFun_identDistrib`, `ConditionallyIID.of_iIndepFun_identDistrib` —
  the sharp form of the first worked example of `TauCetiRoadmap/Exchangeability/README.md`
  ("Worked examples"):

  > The law of an i.i.d. sequence is `MixedIID` — indeed `ConditionallyIID`, with the constant
  > directing measure.

  `TauCeti.Probability.MixedIID.of_iIndepFun_identDistrib` discharged the mixture half; the
  conditional half was deferred there until the `ConditionallyIIDWith` predicate landed, and is
  supplied here.

The mathematical content is the identity `δ_p ⊗ p^{⊗m} = (p^{⊗m}).map (Prod.mk p)`
(`MeasureTheory.Measure.dirac_prod`): a joint law whose first coordinate is deterministic carries
no more information than its second marginal. Everything else is bookkeeping over the already
available block-law identities, so nothing from `cameronfreer/exchangeability` is needed.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Implementation helper: binding a probability measure against the *constant* random product
measure `ω ↦ p^{⊗m}` just returns `p^{⊗m}`. -/
private theorem bind_const_probabilityMeasure_pi (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ProbabilityMeasure α) (m : ℕ) :
    (μ.bind fun _ : Ω => (ProbabilityMeasure.pi fun _ : Fin m => p).toMeasure) =
      Measure.pi fun _ : Fin m => (p : Measure α) := by
  rw [Measure.bind_const, measure_univ, one_smul, ProbabilityMeasure.toMeasure_pi]

/-- Implementation helper: a constant finite product measure is invariant under reindexing the
factors by a bijection. This is `MeasureTheory.measurePreserving_piCongrLeft` for a constant
family, with the reindexing written as honest precomposition rather than as a dependent
`Equiv.piCongrLeft`. -/
private theorem map_comp_equiv_pi_const {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (q : Measure α) [IsProbabilityMeasure q] :
    (Measure.pi fun _ : ι => q).map (fun g (j : ι') => g (e.symm j)) =
      Measure.pi fun _ : ι' => q := by
  have hmap : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι' => α) e) =
      fun g (j : ι') => g (e.symm j) := by
    funext g j
    rw [MeasurableEquiv.coe_piCongrLeft]
    simpa using Equiv.piCongrLeft_apply_apply (fun _ : ι' => α) e g (e.symm j)
  rw [← hmap]
  exact Measure.pi_map_piCongrLeft e fun _ : ι' => q

/-- A constant mixing representative says exactly that every injective block law is the
corresponding product of `p`. -/
theorem MixedIIDWith.blockLaw_eq_pi_of_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k) :
    blockLaw μ X k = Measure.pi fun _ : Fin m => (p : Measure α) := by
  rw [h.blockLaw_eq_mixture k hk, bind_const_probabilityMeasure_pi]

/-- A constant mixing representative already forces the coordinates to be a.e. measurable, so no
such hypothesis is needed alongside it: the singleton block law is the probability measure `p`,
hence nonzero, while `Measure.map` of a non-a.e.-measurable function is `0`. -/
theorem MixedIIDWith.aemeasurable_of_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) (i : ℕ) :
    AEMeasurable (X i) μ := by
  have hblock :=
    h.blockLaw_eq_pi_of_const (fun _ : Fin 1 => i) fun a b _ => Subsingleton.elim a b
  rw [blockLaw_def] at hblock
  have hne : (μ.map fun ω (_ : Fin 1) => X i ω) ≠ 0 := by
    rw [hblock]; exact IsProbabilityMeasure.ne_zero _
  exact (measurable_pi_apply 0).comp_aemeasurable (AEMeasurable.of_map_ne_zero hne)

/-- Every coordinate of a process with a constant mixing representative `p` has law `p`. -/
theorem MixedIIDWith.map_eq_of_const {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) (i : ℕ) :
    μ.map (X i) = (p : Measure α) := by
  have hone : AEMeasurable (fun ω (_ : Fin 1) => X i ω) μ :=
    aemeasurable_pi_lambda _ fun _ => h.aemeasurable_of_const i
  have hblock :=
    h.blockLaw_eq_pi_of_const (fun _ : Fin 1 => i) fun a b _ => Subsingleton.elim a b
  calc μ.map (X i)
      = (μ.map fun ω (_ : Fin 1) => X i ω).map (Function.eval 0) := by
        rw [(measurable_pi_apply _).aemeasurable.map_map_of_aemeasurable hone]
        rfl
    _ = (Measure.pi fun _ : Fin 1 => (p : Measure α)).map (Function.eval 0) := by
        rw [← blockLaw_def, hblock]
    _ = (p : Measure α) := (measurePreserving_eval (fun _ : Fin 1 => (p : Measure α)) 0).map_eq

/-- The coordinates of a process with a constant mixing representative are independent. Along an
injective selection the block law is a product measure, and `Measure.pi` on a finite index set is
exactly what independence of that finite subfamily means. -/
theorem MixedIIDWith.iIndepFun_of_const {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → α}
    {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) : iIndepFun X μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := h.aemeasurable_of_const
  rw [iIndepFun_iff_finset]
  intro s
  -- `Finset.restrict` is the coordinate restriction `fun i : s => X i`; unfold it so that the
  -- finite subfamily is presented as an honest lambda for `iIndepFun_iff_map_fun_eq_pi_map`.
  simp only [Finset.restrict_def]
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i : s => hX i]
  -- Enumerate `s` increasingly to turn it into a `Fin s.card`-indexed injective selection.
  set e : Fin s.card ≃ s := (s.orderIsoOfFin rfl).toEquiv
  have hk : Function.Injective fun i : Fin s.card => ((e i : s) : ℕ) :=
    Subtype.val_injective.comp e.injective
  have hblock := h.blockLaw_eq_pi_of_const (fun i : Fin s.card => ((e i : s) : ℕ)) hk
  have hcomp : (fun ω (j : s) => X (j : ℕ) ω) =
      (fun g (j : s) => g (e.symm j)) ∘ fun ω (i : Fin s.card) => X ((e i : s) : ℕ) ω := by
    funext ω j
    simp [e.apply_symm_apply j]
  have hae : AEMeasurable (fun ω (i : Fin s.card) => X ((e i : s) : ℕ) ω) μ :=
    aemeasurable_pi_lambda _ fun i => hX _
  calc μ.map (fun ω (j : s) => X (j : ℕ) ω)
      = (μ.map fun ω (i : Fin s.card) => X ((e i : s) : ℕ) ω).map
          (fun g (j : s) => g (e.symm j)) := by
        rw [(measurable_pi_lambda _ fun j => measurable_pi_apply
          (e.symm j)).aemeasurable.map_map_of_aemeasurable hae, hcomp]
    _ = (Measure.pi fun _ : Fin s.card => (p : Measure α)).map fun g (j : s) => g (e.symm j) := by
        rw [← blockLaw_def, hblock]
    _ = Measure.pi fun _ : s => (p : Measure α) := map_comp_equiv_pi_const e _
    _ = Measure.pi fun j : s => μ.map (X (j : ℕ)) :=
        congrArg Measure.pi (funext fun j => (h.map_eq_of_const j).symm)

/-- **A constant mixing representative means plain i.i.d.**: `fun _ => p` witnesses `MixedIIDWith`
exactly when the coordinates are independent and each has law `p`. -/
theorem mixedIIDWith_const_iff_iIndepFun_and_map_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {p : ProbabilityMeasure α} :
    (MixedIIDWith μ X fun _ => p) ↔ iIndepFun X μ ∧ ∀ i, μ.map (X i) = (p : Measure α) := by
  refine ⟨fun h => ⟨h.iIndepFun_of_const, h.map_eq_of_const⟩, fun ⟨hindep, hlaw⟩ => ?_⟩
  have hX : ∀ i, AEMeasurable (X i) μ := fun i =>
    AEMeasurable.of_map_ne_zero (by rw [hlaw i]; exact IsProbabilityMeasure.ne_zero _)
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i => ⟨hX i, hX 0, by rw [hlaw i, hlaw 0]⟩
  have hp : (⟨μ.map (X 0), Measure.isProbabilityMeasure_map (hX 0)⟩ : ProbabilityMeasure α) = p :=
    Subtype.ext (hlaw 0)
  simpa [hp] using MixedIIDWith.of_iIndepFun_identDistrib hindep hident

/-- **At a constant `ν` the conditional identity is free.** The joint law of `(p, block)` is the
block law pushed forward by `Prod.mk p`, and the disintegration `δ_p ⊗ p^{⊗m}` is the product law
pushed forward by the same map, so the mixture identity already gives the joint one. -/
theorem conditionallyIIDWith_const_of_mixedIIDWith {μ : Measure Ω}
    {X : ℕ → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) :
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

/-- **The two de Finetti predicates agree at a constant witness.** For a nondegenerate mixing law
the conditional predicate is strictly stronger; the degenerate case is exactly where the gap
closes. -/
theorem conditionallyIIDWith_const_iff_mixedIIDWith {μ : Measure Ω}
    {X : ℕ → Ω → α} {p : ProbabilityMeasure α} :
    (ConditionallyIIDWith μ X fun _ => p) ↔ MixedIIDWith μ X fun _ => p :=
  ⟨mixedIIDWith_of_conditionallyIIDWith, conditionallyIIDWith_const_of_mixedIIDWith⟩

/-- **A constant directing measure means plain i.i.d.** -/
theorem conditionallyIIDWith_const_iff_iIndepFun_and_map_eq {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ω → α} {p : ProbabilityMeasure α} :
    (ConditionallyIIDWith μ X fun _ => p) ↔
      iIndepFun X μ ∧ ∀ i, μ.map (X i) = (p : Measure α) := by
  rw [conditionallyIIDWith_const_iff_mixedIIDWith, mixedIIDWith_const_iff_iIndepFun_and_map_eq]

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
