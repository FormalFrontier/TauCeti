/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite evaluation laws determine a measure on `ProbabilityMeasure α`

A finite measure on `ProbabilityMeasure α` is determined by the laws of its finite evaluation
families `P ↦ (P (B 0), …, P (B (n-1)))`.

## Main results

* `Measure.ext_of_forall_map_probabilityMeasure_eval_eq` — two measures on `ProbabilityMeasure α`
  agree as soon as every finite family of measurable sets induces the same pushforward law.

## Implementation

The Giry σ-algebra on `Measure α` is *defined* as an `iSup` of comaps of the individual
evaluations `μ ↦ μ s`, so it is already the pullback of a product σ-algebra along the
all-evaluations map; `comap_iSup` is all that is needed to see this. Transporting along
`Subtype.val` and replacing the `ℝ≥0∞`-valued evaluations by their real-valued counterparts —
each is measurable in terms of the other, so the two pullbacks coincide — puts the σ-algebra on
`ProbabilityMeasure α` in the same form.

Once the σ-algebra is a pullback, equality of the two measures reduces to equality of their
pushforwards under the all-evaluations map. Those pushforwards live on a product space, and the
hypothesis says exactly that their restrictions to every finite set of coordinates agree — so both
are projective limits of the same family and `MeasureTheory.IsProjectiveLimit.unique` concludes.
No π-system is built here: that lemma already performs the `measurableCylinders` argument. The only
work is reindexing a `Finset` of coordinates by `Fin` via `Finset.equivFin`.
-/

public section

noncomputable section

open MeasureTheory Set MeasurableSpace

namespace TauCeti

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The index type for the all-evaluations map: the measurable subsets of `α`. -/
private abbrev MeasIdx (α : Type*) [MeasurableSpace α] := {s : Set α // MeasurableSet s}

/-- The all-evaluations map, sending a probability measure to its vector of real-valued
measures of the measurable sets. -/
private def evalReal (P : ProbabilityMeasure α) : MeasIdx α → ℝ := fun s => (P s.1 : ℝ)

private theorem measurable_evalReal_apply (s : MeasIdx α) :
    Measurable fun P : ProbabilityMeasure α => evalReal P s :=
  ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe s.2).comp measurable_subtype_coe)

private theorem measurable_evalReal : Measurable (evalReal (α := α)) :=
  measurable_pi_lambda _ measurable_evalReal_apply

private theorem measurable_eval_family {n : ℕ} (B : Fin n → Set α)
    (hB : ∀ i, MeasurableSet (B i)) :
    Measurable fun P : ProbabilityMeasure α => fun i => (P (B i) : ℝ) :=
  measurable_pi_lambda _ fun i => measurable_evalReal_apply ⟨B i, hB i⟩

/-- The Giry σ-algebra on `Measure α` is the pullback of the product σ-algebra along the
all-evaluations map. This is a repackaging of the definition: the instance is already an `iSup`
of comaps of the individual evaluations. -/
private theorem measurableSpace_measure_eq_comap_eval :
    (Measure.instMeasurableSpace : MeasurableSpace (Measure α))
      = MeasurableSpace.comap (fun μ : Measure α => fun s : MeasIdx α => μ s.1)
          MeasurableSpace.pi := by
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def]
  rw [Measure.instMeasurableSpace, iSup_subtype]
  simp only [← BorelSpace.measurable_eq (α := ENNReal)]

/-- Expresses the `ℝ≥0∞`-valued evaluation `P ↦ (P : Measure α) s` as `ENNReal.ofReal` of its
real-valued counterpart `evalReal`. -/
private theorem coe_apply_eq_ofReal_evalReal (s : MeasIdx α) :
    (fun P : ProbabilityMeasure α => (P : Measure α) s.1)
      = fun P => ENNReal.ofReal (evalReal P s) := by
  funext P
  rw [evalReal, ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  simp

/-- The σ-algebra on `ProbabilityMeasure α` is the pullback of the product σ-algebra along
`evalReal`. The real-valued evaluations generate the same σ-algebra as the `ℝ≥0∞`-valued ones
defining the Giry structure, since each is measurable in terms of the other. -/
private theorem measurableSpace_probabilityMeasure_eq_comap :
    (inferInstance : MeasurableSpace (ProbabilityMeasure α))
      = MeasurableSpace.comap (evalReal (α := α)) MeasurableSpace.pi := by
  refine le_antisymm ?_ measurable_evalReal.comap_le
  -- `ProbabilityMeasure α` is a subtype of `Measure α`, and its instance is
  -- `inferInstanceAs (MeasurableSpace (Subtype _))`, i.e. `Subtype.instMeasurableSpace`, which is
  -- itself `Measure.instMeasurableSpace.comap Subtype.val`. Neither is accompanied by an equation
  -- lemma in Mathlib, so the unfolding is available only definitionally; naming it as an explicit
  -- `rfl` confines that to one step and keeps the rest of the proof propositional.
  have hinst : (inferInstance : MeasurableSpace (ProbabilityMeasure α))
      = MeasurableSpace.comap Subtype.val Measure.instMeasurableSpace := rfl
  rw [hinst]
  rw [measurableSpace_measure_eq_comap_eval, MeasurableSpace.comap_comp, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_comp]
  refine (measurable_iff_comap_le (f := fun P : ProbabilityMeasure α => (P : Measure α) s.1)).1 ?_
  rw [coe_apply_eq_ofReal_evalReal]
  have hev : Measurable[MeasurableSpace.comap (evalReal (α := α)) MeasurableSpace.pi]
      (evalReal (α := α)) := Measurable.of_comap_le le_rfl
  exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply s).comp hev)

/-- **Finite evaluation laws determine the measure.** Two measures on `ProbabilityMeasure α` are
equal as soon as, for every finite family `B` of measurable subsets of `α`, the pushforwards under
the evaluation map `P ↦ (P (B 0), …, P (B (n-1)))` agree.

Only `π₁` need be assumed finite: the `n = 0` instance of the hypothesis equates the total
masses. -/
theorem Measure.ext_of_forall_map_probabilityMeasure_eval_eq
    {π₁ π₂ : Measure (ProbabilityMeasure α)} [IsFiniteMeasure π₁]
    (h : ∀ (n : ℕ) (B : Fin n → Set α), (∀ i, MeasurableSet (B i)) →
      π₁.map (fun P => fun i => (P (B i) : ℝ))
        = π₂.map (fun P => fun i => (P (B i) : ℝ))) :
    π₁ = π₂ := by
  have key : π₁.map (evalReal (α := α)) = π₂.map (evalReal (α := α)) := by
    haveI : ∀ I : Finset (MeasIdx α),
        IsFiniteMeasure ((π₁.map (evalReal (α := α))).map I.restrict) :=
      fun I => Measure.isFiniteMeasure_map _ _
    -- Each finite restriction of the two pushforwards agrees, so both are projective limits of
    -- the same family and `IsProjectiveLimit.unique` finishes.
    have hstep : ∀ I : Finset (MeasIdx α),
        (π₂.map (evalReal (α := α))).map I.restrict
          = (π₁.map (evalReal (α := α))).map I.restrict := by
      intro I
      set e := I.equivFin
      set B : Fin I.card → Set α := fun j => ((e.symm j : MeasIdx α) : Set α) with hB
      have hBm : ∀ j, MeasurableSet (B j) := fun j => (e.symm j : MeasIdx α).2
      set Φ : (Fin I.card → ℝ) → (I → ℝ) := fun x i => x (e i) with hΦ
      have hΦm : Measurable Φ := measurable_pi_lambda _ fun i => measurable_pi_apply _
      have hfam := measurable_eval_family B hBm
      have hfun : I.restrict ∘ (evalReal (α := α))
          = Φ ∘ fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ) := by
        funext P i
        simp [Finset.restrict, evalReal, hΦ, hB]
      have hcomp : ∀ π : Measure (ProbabilityMeasure α),
          (π.map (evalReal (α := α))).map I.restrict
            = (π.map fun P : ProbabilityMeasure α => fun j => (P (B j) : ℝ)).map Φ := by
        intro π
        rw [Measure.map_map (Finset.measurable_restrict I) measurable_evalReal,
          Measure.map_map hΦm hfam, hfun]
      rw [hcomp, hcomp, h _ B hBm]
    exact (IsProjectiveLimit.unique
      (P := fun I => (π₁.map (evalReal (α := α))).map I.restrict) hstep fun _ => rfl).symm
  refine Measure.ext fun T hT => ?_
  obtain ⟨U, hU, rfl⟩ : ∃ U, MeasurableSet U ∧ (evalReal (α := α)) ⁻¹' U = T := by
    have hT' : MeasurableSet[MeasurableSpace.comap (evalReal (α := α)) MeasurableSpace.pi] T := by
      rwa [← measurableSpace_probabilityMeasure_eq_comap]
    exact MeasurableSpace.measurableSet_comap.1 hT'
  rw [← Measure.map_apply measurable_evalReal hU, ← Measure.map_apply measurable_evalReal hU, key]


end MeasureTheory

end TauCeti
