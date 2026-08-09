/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Gluing
public import TauCeti.MeasureTheory.OptimalTransport.MultiMarginal.Basic

/-!
# Replacing one marginal of a multi-marginal coupling

This file constructs a new multi-marginal coupling by replacing one coordinate according to a
two-coordinate transport plan. Given a joint law `π` of a family `(X j)`, an index `i`, and a plan
`σ` whose first marginal is the `i`th marginal of `π`, first glue `π` to `σ` along coordinate `i`.
Then discard the old `i`th coordinate and retain the new one. All other coordinates keep their
joint distribution, while the `i`th marginal becomes the second marginal of `σ`.

This is the marginal-replacement operation requested in Layer 0 of the optimal-transport roadmap.
The construction is stated first for an unbundled joint probability law and then bundled as
`TauCeti.MultiCoupling.replaceMarginal`.

## Main statements

* `TauCeti.Measure.replaceMarginal` performs the gluing-and-update construction on a raw measure;
* `TauCeti.Measure.map_eval_replaceMarginal_same` identifies the replaced marginal;
* `TauCeti.Measure.map_eval_replaceMarginal_of_ne` shows that every other marginal is unchanged;
* `TauCeti.MultiCoupling.replaceMarginal` packages the construction as a multi-marginal coupling.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

universe u v w

namespace Measure

variable {ι : Type u} {X : ι → Type v} [∀ j, MeasurableSpace (X j)]

/-- Replace coordinate `i` of a joint probability law according to a two-coordinate plan `σ`.

The construction glues the law of `(x, x i)` under `π` to `σ`, then maps the resulting triple
`(x, x i, y)` to `Function.update x i y`. The first marginal of `σ` is not constrained in the
definition; `map_eval_replaceMarginal_same` assumes the compatibility needed to identify the new
`i`th marginal. -/
def replaceMarginal (π : ProbabilityMeasure (∀ j, X j)) (i : ι)
    [StandardBorelSpace (X i)] (σ : ProbabilityMeasure (X i × X i)) :
    ProbabilityMeasure (∀ j, X j) := by
  let _ : Nonempty (X i) := σ.nonempty.map Prod.fst
  let ρ : Measure ((∀ j, X j) × X i) :=
    π.toMeasure.map fun x ↦ (x, x i)
  let γ : Measure ((∀ j, X j) × X i × X i) := glue ρ σ.toMeasure.condKernel
  letI : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    exact Measure.isProbabilityMeasure_map
      (measurable_id.prodMk (measurable_pi_apply i)).aemeasurable
  letI : IsProbabilityMeasure γ := by
    dsimp only [γ]
    infer_instance
  letI := Classical.decEq ι
  let hu : AEMeasurable (fun q : (∀ j, X j) × X i × X i ↦
      Function.update q.1 i q.2.2) γ :=
    (measurable_update'.comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).aemeasurable
  exact (⟨γ.map (fun q ↦ Function.update q.1 i q.2.2),
    Measure.isProbabilityMeasure_map hu⟩ : ProbabilityMeasure (∀ j, X j))

private theorem toMeasure_replaceMarginal (π : ProbabilityMeasure (∀ j, X j)) (i : ι)
    [DecidableEq ι] [StandardBorelSpace (X i)] [Nonempty (X i)]
    (σ : ProbabilityMeasure (X i × X i)) :
    (replaceMarginal π i σ).toMeasure =
      (glue (π.toMeasure.map fun x ↦ (x, x i)) σ.toMeasure.condKernel).map
        (fun q ↦ Function.update q.1 i q.2.2) := by
  unfold replaceMarginal
  dsimp only
  simp only [ProbabilityMeasure.toMeasure]
  congr
  funext q j
  by_cases h : j = i <;> simp [Function.update, h]

/-- The coordinate used to glue the original joint law has the original `i`th marginal. -/
private theorem snd_map_duplicateAt (π : ProbabilityMeasure (∀ j, X j)) (i : ι) :
    (π.toMeasure.map fun x ↦ (x, x i)).snd = π.toMeasure.map (Function.eval i) := by
  rw [Measure.snd_map_prodMk]
  exact measurable_id

/-- Replacing coordinate `i` changes its marginal to the second marginal of the replacement plan,
provided the plan's first marginal agrees with the old `i`th marginal. -/
theorem map_eval_replaceMarginal_same (π : ProbabilityMeasure (∀ j, X j)) (i : ι)
    [StandardBorelSpace (X i)] (σ : ProbabilityMeasure (X i × X i))
    (hσ : σ.toMeasure.fst = π.toMeasure.map (Function.eval i)) :
    (replaceMarginal π i σ).toMeasure.map (Function.eval i) = σ.toMeasure.snd := by
  classical
  let _ : Nonempty (X i) := σ.nonempty.map Prod.fst
  let ρ : Measure ((∀ j, X j) × X i) :=
    π.toMeasure.map fun x ↦ (x, x i)
  have hρσ : ρ.snd = σ.toMeasure.fst := by
    dsimp only [ρ]
    rw [snd_map_duplicateAt, ← hσ]
  rw [toMeasure_replaceMarginal]
  have hcomp : (Function.eval i) ∘ (fun q : (∀ j, X j) × X i × X i ↦
      Function.update q.1 i q.2.2) = Prod.snd ∘ Prod.snd := by
    funext q
    simp
  rw [Measure.map_map (measurable_pi_apply i) (by fun_prop), hcomp,
    ← Measure.map_map measurable_snd measurable_snd, ← Measure.snd, ← Measure.snd,
    snd_glue_condKernel ρ σ.toMeasure hρσ]

/-- Replacing coordinate `i` leaves the law of every measurable statistic that does not depend on
that coordinate unchanged. -/
theorem map_replaceMarginal_eq_of_update_eq {Y : Type w} [MeasurableSpace Y]
    (π : ProbabilityMeasure (∀ j, X j)) (i : ι) [DecidableEq ι] [StandardBorelSpace (X i)]
    (σ : ProbabilityMeasure (X i × X i)) (f : (∀ j, X j) → Y) (hf : Measurable f)
    (hfi : ∀ x y, f (Function.update x i y) = f x) :
    (replaceMarginal π i σ).toMeasure.map f = π.toMeasure.map f := by
  classical
  let _ : Nonempty (X i) := σ.nonempty.map Prod.fst
  rw [toMeasure_replaceMarginal]
  have hcomp : f ∘ (fun q : (∀ j, X j) × X i × X i ↦
      Function.update q.1 i q.2.2) = f ∘ Prod.fst := by
    funext q
    exact hfi q.1 q.2.2
  rw [Measure.map_map hf (by fun_prop), hcomp,
    ← Measure.map_map hf measurable_fst, ← Measure.fst,
    fst_glue, Measure.fst_map_prodMk (measurable_pi_apply i)]
  convert Measure.map_map (μ := π.toMeasure) hf measurable_id using 1
  all_goals congr 2

/-- Replacing coordinate `i` leaves the marginal at every different coordinate `j` unchanged. -/
theorem map_eval_replaceMarginal_of_ne (π : ProbabilityMeasure (∀ j, X j)) (i : ι)
    [StandardBorelSpace (X i)] (σ : ProbabilityMeasure (X i × X i)) {j : ι} (hji : j ≠ i) :
    (replaceMarginal π i σ).toMeasure.map (Function.eval j) =
      π.toMeasure.map (Function.eval j) := by
  classical
  apply map_replaceMarginal_eq_of_update_eq π i σ (Function.eval j) (measurable_pi_apply j)
  intro x y
  simp [hji]

/-- Every joint projection avoiding the replaced coordinate has the same law before and after
marginal replacement. -/
theorem map_project_replaceMarginal_of_forall_ne {κ : Type w}
    (π : ProbabilityMeasure (∀ j, X j)) (i : ι) [StandardBorelSpace (X i)]
    (σ : ProbabilityMeasure (X i × X i)) (e : κ → ι) (he : ∀ k, e k ≠ i) :
    (replaceMarginal π i σ).toMeasure.map (fun x k ↦ x (e k)) =
      π.toMeasure.map (fun x k ↦ x (e k)) := by
  classical
  apply map_replaceMarginal_eq_of_update_eq π i σ (fun x k ↦ x (e k))
    (measurable_pi_lambda _ fun k ↦ measurable_pi_apply (e k))
  intro x y
  funext k
  simp [he k]

end Measure

namespace MultiCoupling

variable {ι : Type u} {X : ι → Type v} [∀ j, MeasurableSpace (X j)]
  {μ : ∀ j, ProbabilityMeasure (X j)}

/-- Replace one entry of a family of probability measures. This hides the irrelevant choice of a
decidable equality on the index type from the marginal-replacement API. -/
def replaceFamily (μ : ∀ j, ProbabilityMeasure (X j)) (i : ι)
    (ν : ProbabilityMeasure (X i)) : ∀ j, ProbabilityMeasure (X j) := by
  classical
  exact Function.update μ i ν

/-- The selected entry of `replaceFamily` is the replacement measure. -/
@[simp]
theorem replaceFamily_same (μ : ∀ j, ProbabilityMeasure (X j)) (i : ι)
    (ν : ProbabilityMeasure (X i)) : replaceFamily μ i ν i = ν := by
  classical
  simp [replaceFamily]

/-- Every unselected entry of `replaceFamily` is unchanged. -/
@[simp]
theorem replaceFamily_of_ne (μ : ∀ j, ProbabilityMeasure (X j)) (i : ι)
    (ν : ProbabilityMeasure (X i)) {j : ι} (hji : j ≠ i) :
    replaceFamily μ i ν j = μ j := by
  classical
  simp [replaceFamily, hji]

/-- Replace the `i`th marginal of a multi-marginal coupling according to a two-coordinate plan.

The replacement plan must start at the prescribed marginal `μ i`. Its second marginal becomes the
new prescribed marginal, while every other prescribed marginal remains unchanged. -/
def replaceMarginal (π : MultiCoupling μ) (i : ι) [StandardBorelSpace (X i)]
    (σ : ProbabilityMeasure (X i × X i))
    (hσ : σ.toMeasure.fst = (μ i).toMeasure) :
    MultiCoupling (replaceFamily μ i (σ.map measurable_snd.aemeasurable)) := by
  refine ⟨Measure.replaceMarginal π.1 i σ, ?_⟩
  constructor
  intro j
  by_cases hji : j = i
  · subst j
    rw [Measure.map_eval_replaceMarginal_same]
    · simp only [replaceFamily_same, ProbabilityMeasure.toMeasure_map]
      rw [← Measure.snd]
    · rw [hσ]
      exact (π.2.marginal_eq i).symm
  · rw [Measure.map_eval_replaceMarginal_of_ne π.1 i σ hji, π.2.marginal_eq,
      replaceFamily_of_ne μ i _ hji]

/-- The underlying probability measure of a bundled marginal replacement is the raw
gluing-and-update construction. -/
@[simp]
theorem coe_replaceMarginal (π : MultiCoupling μ) (i : ι) [StandardBorelSpace (X i)]
    (σ : ProbabilityMeasure (X i × X i))
    (hσ : σ.toMeasure.fst = (μ i).toMeasure) :
    (π.replaceMarginal i σ hσ : ProbabilityMeasure (∀ j, X j)) =
      Measure.replaceMarginal π.1 i σ :=
  by
    apply ProbabilityMeasure.toMeasure_injective
    rfl

/-- The replaced coordinate has the second marginal of the replacement plan. -/
theorem marginal_replaceMarginal_same (π : MultiCoupling μ) (i : ι)
    [StandardBorelSpace (X i)] (σ : ProbabilityMeasure (X i × X i))
    (hσ : σ.toMeasure.fst = (μ i).toMeasure) :
    (π.replaceMarginal i σ hσ).marginal i = σ.map measurable_snd.aemeasurable := by
  simp

/-- Every coordinate different from the replaced one keeps its original marginal. -/
theorem marginal_replaceMarginal_of_ne (π : MultiCoupling μ) (i : ι)
    [StandardBorelSpace (X i)] (σ : ProbabilityMeasure (X i × X i))
    (hσ : σ.toMeasure.fst = (μ i).toMeasure) {j : ι} (hji : j ≠ i) :
    (π.replaceMarginal i σ hσ).marginal j = μ j := by
  simp [hji]

end MultiCoupling

end TauCeti
