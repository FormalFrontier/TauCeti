/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.IID

/-!
# Constant mixing measures

This file characterizes `MixedIIDWith` for a constant mixing representative. It is equivalent to
plain independence with common marginal law.

## Main results

* `MixedIIDWith.blockLaw_eq_pi_of_const`, `MixedIIDWith.aemeasurable_of_const`,
  `MixedIIDWith.map_eq_of_const` — what a constant mixing representative says: every injective
  block law is the `m`-fold product of `p`, every coordinate is a.e. measurable, and every
  coordinate has law `p`.
* `mixedIIDWith_const_iff_iIndepFun_and_map_eq` — a constant `p` is a mixing representative exactly
  when the coordinates are independent with common law `p`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti

namespace Probability

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A constant mixing representative says exactly that every injective block law is the
corresponding product of `p`. -/
theorem MixedIIDWith.blockLaw_eq_pi_of_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p)
    {m : ℕ} (k : Fin m → ι) (hk : Function.Injective k) :
    blockLaw μ X k = Measure.pi fun _ : Fin m => (p : Measure α) := by
  rw [h.blockLaw_eq_mixture k hk, Measure.bind_const, measure_univ, one_smul,
    ProbabilityMeasure.toMeasure_pi]

/-- A constant mixing representative already forces the coordinates to be a.e. measurable, so no
such hypothesis is needed alongside it: the singleton block law is the probability measure `p`,
hence nonzero, while `Measure.map` of a non-a.e.-measurable function is `0`. -/
theorem MixedIIDWith.aemeasurable_of_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → α} {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) (i : ι) :
    AEMeasurable (X i) μ := by
  have hblock :=
    h.blockLaw_eq_pi_of_const (fun _ : Fin 1 => i) fun a b _ => Subsingleton.elim a b
  rw [blockLaw_def] at hblock
  have hne : (μ.map fun ω (_ : Fin 1) => X i ω) ≠ 0 := by
    rw [hblock]; exact IsProbabilityMeasure.ne_zero _
  exact (measurable_pi_apply 0).comp_aemeasurable (AEMeasurable.of_map_ne_zero hne)

/-- Every coordinate of a family with a constant mixing representative `p` has law `p`. -/
theorem MixedIIDWith.map_eq_of_const {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → α}
    {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) (i : ι) :
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
theorem MixedIIDWith.iIndepFun_of_const {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → α}
    {p : ProbabilityMeasure α} (h : MixedIIDWith μ X fun _ => p) : iIndepFun X μ := by
  have hX : ∀ i, AEMeasurable (X i) μ := h.aemeasurable_of_const
  rw [iIndepFun_iff_finset]
  intro s
  -- `Finset.restrict` is the coordinate restriction `fun i : s => X i`; unfold it so that the
  -- finite subfamily is presented as an honest lambda for `iIndepFun_iff_map_fun_eq_pi_map`.
  simp only [Finset.restrict_def]
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i : s => hX i]
  -- Enumerate `s` as a `Fin s.card`-indexed injective selection. Any bijection serves:
  -- only injectivity and the round trip are used, never an order on the index type.
  set e : Fin s.card ≃ s := (Finset.equivFin s).symm
  have hk : Function.Injective fun i : Fin s.card => ((e i : s) : ι) :=
    Subtype.val_injective.comp e.injective
  have hblock := h.blockLaw_eq_pi_of_const (fun i : Fin s.card => ((e i : s) : ι)) hk
  have hcomp : (fun ω (j : s) => X (j : ι) ω) =
      (fun g (j : s) => g (e.symm j)) ∘ fun ω (i : Fin s.card) => X ((e i : s) : ι) ω := by
    funext ω j
    simp [e.apply_symm_apply j]
  have hae : AEMeasurable (fun ω (i : Fin s.card) => X ((e i : s) : ι) ω) μ :=
    aemeasurable_pi_lambda _ fun i => hX _
  calc μ.map (fun ω (j : s) => X (j : ι) ω)
      = (μ.map fun ω (i : Fin s.card) => X ((e i : s) : ι) ω).map
          (fun g (j : s) => g (e.symm j)) := by
        rw [(measurable_pi_lambda _ fun j => measurable_pi_apply
          (e.symm j)).aemeasurable.map_map_of_aemeasurable hae, hcomp]
    _ = (Measure.pi fun _ : Fin s.card => (p : Measure α)).map fun g (j : s) => g (e.symm j) := by
        rw [← blockLaw_def, hblock]
    _ = Measure.pi fun _ : s => (p : Measure α) := by
      -- `Measure.pi_map_piCongrLeft` transports along `MeasurableEquiv.piCongrLeft`, which
      -- reindexes by `e.symm` *and* casts each coordinate along the resulting type equality.
      -- Here the family `fun _ : s => α` is constant, so that cast is the identity and the
      -- equiv is just reindexing — but only propositionally, so neither `rw` nor `convert`
      -- aligns the two map functions on its own. Name the identification instead.
      have hpiCongrLeft : ⇑(MeasurableEquiv.piCongrLeft (fun _ : s => α) e) =
          fun g (j : s) => g (e.symm j) := by
        funext g j
        rw [MeasurableEquiv.coe_piCongrLeft]
        simpa using Equiv.piCongrLeft_apply_apply (fun _ : s => α) e g (e.symm j)
      rw [← hpiCongrLeft]
      exact Measure.pi_map_piCongrLeft e fun _ : s => (p : Measure α)
    _ = Measure.pi fun j : s => μ.map (X (j : ι)) :=
        congrArg Measure.pi (funext fun j => (h.map_eq_of_const j).symm)

/-- **A constant mixing representative means plain i.i.d.**: `fun _ => p` witnesses `MixedIIDWith`
exactly when the coordinates are independent and each has law `p`. -/
theorem mixedIIDWith_const_iff_iIndepFun_and_map_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → α} {p : ProbabilityMeasure α} :
    (MixedIIDWith μ X fun _ => p) ↔ iIndepFun X μ ∧ ∀ i, μ.map (X i) = (p : Measure α) :=
  ⟨fun h => ⟨h.iIndepFun_of_const, h.map_eq_of_const⟩,
    fun ⟨hindep, hlaw⟩ => MixedIIDWith.of_iIndepFun_map_eq hindep hlaw⟩

end Probability

end TauCeti
