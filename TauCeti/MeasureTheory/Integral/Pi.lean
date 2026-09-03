/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.MeasureTheory.Constructions.Pi

/-!
# Integrals over finite product measures

This file collects integration results for finite product measures. In addition to the lower
integral product formula, it gives a Fubini identity obtained by refreshing two coordinates with
independent samples.

The `ℝ≥0∞`-valued companion of Mathlib's `MeasureTheory.integral_fintype_prod_eq_prod`: over
`MeasureTheory.Measure.pi`, the lower integral of a product `∏ i, f i (x i)` of functions each
depending on a single coordinate is the product of the one-dimensional lower integrals.

Mathlib proves the Bochner version (and the matching integrability statements) but not this one,
even though the `ℝ≥0∞` version needs no integrability hypothesis at all, since every factor is
automatically "integrable" in the lower-integral sense. The proof is the same induction as
Mathlib's: reduce a `Fin (n + 1)`-indexed product to a binary product measure along
`MeasureTheory.measurePreserving_piFinSuccAbove`, split it with
`MeasureTheory.lintegral_prod_mul`, and transfer an arbitrary `Fintype` index to `Fin` along
`MeasureTheory.measurePreserving_piCongrLeft`.

## Main statements

* `TauCeti.lintegral_fintype_prod_eq_prod`: the product formula, for measurable factors.
* `TauCeti.lintegral_fintype_prod_eq_prod₀`: the same for almost everywhere measurable factors.
* `TauCeti.integral_pi_eq_integral_integral_update`: the two-coordinate Fubini
  identity.
-/

public section

open Function MeasureTheory MeasureTheory.Measure

open scoped ENNReal

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

/-- **Fubini after a two-coordinate refresh.** An integral against a finite product of sigma-finite
measures is an outer integral over the assignment and an inner integral over a fresh independent
pair placed at the two distinct probability coordinates `a` and `b`. -/
theorem integral_pi_eq_integral_integral_update {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] {a b : ι}
    [IsProbabilityMeasure (μ a)] [IsProbabilityMeasure (μ b)] (hab : a ≠ b)
    {f : (∀ i, α i) → E} (hf : Integrable f (Measure.pi μ)) :
    ∫ x, f x ∂(Measure.pi μ) =
      ∫ z, (∫ p : α a × α b, f (update (update z a p.1) b p.2) ∂(μ a).prod (μ b))
        ∂(Measure.pi μ) := by
  set g : ((∀ i, α i) × α a × α b) → (∀ i, α i) :=
    fun w => update (update w.1 a w.2.1) b w.2.2 with hg
  have hmp := measurePreserving_update_update μ hab
  have hcomp : Integrable (fun w => f (g w)) ((Measure.pi μ).prod ((μ a).prod (μ b))) :=
    hmp.integrable_comp_of_integrable hf
  have hae : AEStronglyMeasurable f
      (Measure.map g ((Measure.pi μ).prod ((μ a).prod (μ b)))) := by
    rw [hmp.map_eq]
    exact hf.aestronglyMeasurable
  calc ∫ x, f x ∂(Measure.pi μ)
      = ∫ x, f x ∂(Measure.map g ((Measure.pi μ).prod ((μ a).prod (μ b)))) := by
        rw [hmp.map_eq]
    _ = ∫ w, f (g w) ∂((Measure.pi μ).prod ((μ a).prod (μ b))) :=
        integral_map hmp.measurable.aemeasurable hae
    _ = ∫ z, (∫ p : α a × α b, f (update (update z a p.1) b p.2) ∂(μ a).prod (μ b))
          ∂(Measure.pi μ) := integral_prod _ hcomp

/-- The product formula for a `Fin n`-indexed product measure, by induction on `n`. -/
private theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {α : Fin n → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} {μ : ∀ i, Measure (α i)} [∀ i, SigmaFinite (μ i)]
    {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      -- Peel off the zeroth coordinate: `Measure.pi μ` becomes a binary product measure.
      have hprodm : Measurable fun z : ∀ j : Fin n, α ((0 : Fin (n + 1)).succAbove j) =>
          ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z j) :=
        Finset.measurable_prod _ fun j _ => (hf _).comp (measurable_pi_apply j)
      calc ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ
          = ∫⁻ x : ∀ i, α i, f 0 ((MeasurableEquiv.piFinSuccAbove α 0 x).1)
              * ∏ j, f ((0 : Fin (n + 1)).succAbove j)
                  ((MeasurableEquiv.piFinSuccAbove α 0 x).2 j) ∂Measure.pi μ :=
            lintegral_congr fun x => Fin.prod_univ_succAbove (fun i => f i (x i)) 0
        _ = ∫⁻ z, f 0 z.1 * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z.2 j)
              ∂(μ 0).prod (Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j)) :=
            ((measurePreserving_piFinSuccAbove μ 0).lintegral_map_equiv
              (fun z : α 0 × ∀ j : Fin n, α ((0 : Fin (n + 1)).succAbove j) =>
                f 0 z.1 * ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z.2 j))
              (MeasurableEquiv.piFinSuccAbove α 0)).symm
        _ = (∫⁻ y, f 0 y ∂μ 0)
              * ∫⁻ z, ∏ j, f ((0 : Fin (n + 1)).succAbove j) (z j)
                  ∂Measure.pi fun j => μ ((0 : Fin (n + 1)).succAbove j) :=
            lintegral_prod_mul (hf 0).aemeasurable hprodm.aemeasurable
        _ = (∫⁻ y, f 0 y ∂μ 0) * ∏ j, ∫⁻ y, f ((0 : Fin (n + 1)).succAbove j) y
              ∂μ ((0 : Fin (n + 1)).succAbove j) := by rw [ih fun j => hf _]
        _ = ∏ i, ∫⁻ y, f i y ∂μ i :=
            (Fin.prod_univ_succAbove (fun i => ∫⁻ y, f i y ∂μ i) 0).symm

/-- **The product formula for lower integrals over a finite product measure.** The lower integral
of `∏ i, f i (x i)` against `MeasureTheory.Measure.pi μ` is `∏ i, ∫⁻ y, f i y ∂μ i`.

This is the `ℝ≥0∞` analogue of `MeasureTheory.integral_fintype_prod_eq_prod`; unlike the Bochner
statement it needs no integrability of the factors. See
`TauCeti.lintegral_fintype_prod_eq_prod₀` for the almost everywhere measurable version, which is
obtained from this one by passing to measurable representatives. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι]
    {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  -- Transfer the index type to `Fin (card ι)` and apply the `Fin`-indexed statement.
  let e := (Fintype.equivFin ι).symm
  calc ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ
      = ∫⁻ y : ∀ j, α (e j), ∏ i, f i (MeasurableEquiv.piCongrLeft α e y i)
          ∂Measure.pi fun j => μ (e j) :=
        (measurePreserving_piCongrLeft μ e).lintegral_map_equiv _
          (MeasurableEquiv.piCongrLeft α e)
    _ = ∫⁻ y : ∀ j, α (e j), ∏ j, f (e j) (y j) ∂Measure.pi fun j => μ (e j) := by
        refine lintegral_congr fun y => ?_
        rw [← e.prod_comp fun i => f i (MeasurableEquiv.piCongrLeft α e y i)]
        exact Finset.prod_congr rfl fun j _ => by
          simp [MeasurableEquiv.piCongrLeft_apply_apply]
    _ = ∏ j, ∫⁻ z, f (e j) z ∂μ (e j) := lintegral_fin_nat_prod_eq_prod fun j => hf _
    _ = ∏ i, ∫⁻ y, f i y ∂μ i := e.prod_comp fun i => ∫⁻ y, f i y ∂μ i

/-- **The product formula for lower integrals over a finite product measure**, for almost
everywhere measurable factors; see `TauCeti.lintegral_fintype_prod_eq_prod` for the measurable
version. -/
theorem lintegral_fintype_prod_eq_prod₀ {ι : Type*} [Fintype ι] {α : ι → Type*}
    {mα : ∀ i, MeasurableSpace (α i)} (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)]
    {f : ∀ i, α i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, α i, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  -- Each factor may be replaced by a measurable representative: a `μ i`-null exceptional set
  -- pulls back to a `Measure.pi μ`-null one along the `i`-th coordinate.
  have hae : ∀ᵐ x : ∀ i, α i ∂Measure.pi μ, ∀ i, f i (x i) = (hf i).mk (f i) (x i) :=
    Filter.eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (hf i).ae_eq_mk
  rw [lintegral_congr_ae (hae.mono fun x hx => Finset.prod_congr rfl fun i _ => hx i),
    lintegral_fintype_prod_eq_prod μ fun i => (hf i).measurable_mk]
  exact Finset.prod_congr rfl fun i _ => (lintegral_congr_ae (hf i).ae_eq_mk).symm

end TauCeti
