/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.Decoupling

/-!
# Factorizing a whole block over an invariant event

Iterating the one-coordinate decoupling across a block of length `r`.

Each step peels the last coordinate off the block, replacing `𝟙_{B_r}(x_r)` by its conditional
expectation given the shift-invariant σ-algebra. The factors already peeled do not vanish: they
accumulate as an invariants-measurable weight, which is exactly what the weighted decoupling chain
carries.

## Main results

* `ContractableLaw.setIntegral_weight_mul_prefixIndicatorProd_eq_prod_condExp` — the induction, in
  conditional-expectation form;
* `ContractableLaw.setIntegral_prefixIndicatorProd_eq_prod_invariantConditional` — the same with
  the weight specialised to `1` and the factors named as the invariant conditional law.

## Why the conditional expectation, not the witness

The induction carries its accumulated factors as the *weight* of the next step, and the weighted
transport demands a weight that is strictly measurable for `MeasurableSpace.invariants (shift α)`.
A conditional expectation is, by `stronglyMeasurable_condExp`. The invariant conditional law `ν(B)`
is only characterised up to a null set, so it cannot serve. Conversion happens once, at the end.

Everything stays in `ℝ`; the crossing to `ℝ≥0∞` belongs to the common ending, not here.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

private theorem coordCondExp_nonneg {ρ : Measure (ℕ → α)} (B : Set α) (j : ℕ) :
    0 ≤ᵐ[ρ] ρ[fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y j) |
      MeasurableSpace.invariants (shift α)] :=
  condExp_nonneg (Filter.Eventually.of_forall fun _ =>
    Set.indicator_apply_nonneg fun _ => zero_le_one)

private theorem integrable_coordIndicator {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    {B : Set α} (hB : MeasurableSet B) (j : ℕ) :
    Integrable (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y j)) ρ := by
  have hmeas : Measurable fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y j) :=
    (measurable_const.indicator hB).comp (measurable_pi_apply j)
  refine ⟨hmeas.aestronglyMeasurable,
    .of_bounded (C := 1) (Filter.Eventually.of_forall fun y => ?_)⟩
  have h0 : (0 : ℝ) ≤ B.indicator (fun _ => (1 : ℝ)) (y j) :=
    Set.indicator_apply_nonneg fun _ => zero_le_one
  have h1 : B.indicator (fun _ => (1 : ℝ)) (y j) ≤ 1 :=
    Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

private theorem coordCondExp_le_one {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ]
    {B : Set α} (hB : MeasurableSet B) (j : ℕ) :
    ρ[fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y j) |
        MeasurableSpace.invariants (shift α)] ≤ᵐ[ρ] fun _ => (1 : ℝ) := by
  have hle : (fun y : ℕ → α => B.indicator (fun _ => (1 : ℝ)) (y j))
      ≤ᵐ[ρ] fun _ : ℕ → α => (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ =>
      Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
  have hmono := condExp_mono (m := MeasurableSpace.invariants (shift α))
    (integrable_coordIndicator hB j) (integrable_const (1 : ℝ)) hle
  rwa [condExp_const (MeasurableSpace.invariants_le (shift α)) (1 : ℝ)] at hmono

/-- **A block factorizes over an invariant event**, in conditional-expectation form.

Peeling the last coordinate replaces `𝟙_{B_r}(x_r)` by its conditional expectation given the
shift-invariant σ-algebra; the factors already peeled ride along as the weight of the next step,
which is why the whole chain is stated against one. -/
theorem ContractableLaw.setIntegral_weight_mul_prefixIndicatorProd_eq_prod_condExp
    {ρ : Measure (ℕ → α)} [IsProbabilityMeasure ρ] (hρ : ContractableLaw ρ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    ∀ (r : ℕ) (B : Fin r → Set α), (∀ i, MeasurableSet (B i)) →
      ∀ w : (ℕ → α) → ℝ, Measurable[MeasurableSpace.invariants (shift α)] w →
        (∀ᵐ x ∂ρ, |w x| ≤ 1) →
        ∫ x in A, w x * ∏ i : Fin r, (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ
          = ∫ x in A, w x * ∏ i : Fin r,
              ρ[fun y : ℕ → α => (B i).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
                MeasurableSpace.invariants (shift α)] x ∂ρ := by
  intro r
  induction r with
  | zero => intro B _ w _ _; simp
  | succ r ih =>
    intro B hB w hw hw_bdd
    set E : (ℕ → α) → ℝ :=
      ρ[fun y : ℕ → α => (B (Fin.last r)).indicator (fun _ => (1 : ℝ)) (y r) |
        MeasurableSpace.invariants (shift α)] with hEdef
    -- The prefix observable: the factors before the last.
    set g : (Fin r → α) → ℝ := fun y =>
      ∏ i : Fin r, (B i.castSucc).indicator (fun _ => (1 : ℝ)) (y i) with hgdef
    have hg_meas : Measurable g :=
      Finset.measurable_prod _ fun i _ =>
        (measurable_const.indicator (hB _)).comp (measurable_pi_apply i)
    have hg_bdd : ∀ y, |g y| ≤ 1 := by
      intro y
      have h0 : (0 : ℝ) ≤ ∏ i : Fin r, (B i.castSucc).indicator (fun _ => (1 : ℝ)) (y i) :=
        Finset.prod_nonneg fun i _ => Set.indicator_apply_nonneg fun _ => zero_le_one
      have h1 : ∏ i : Fin r, (B i.castSucc).indicator (fun _ => (1 : ℝ)) (y i) ≤ 1 :=
        Finset.prod_le_one (fun i _ => Set.indicator_apply_nonneg fun _ => zero_le_one)
          fun i _ => Set.indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le_one
      rw [hgdef, abs_of_nonneg h0]
      exact h1
    -- The weight for the inductive step: the peeled factor joins it.
    have hwE : Measurable[MeasurableSpace.invariants (shift α)] fun x => w x * E x :=
      hw.mul (stronglyMeasurable_condExp).measurable
    have hwE_bdd : ∀ᵐ x ∂ρ, |w x * E x| ≤ 1 := by
      filter_upwards [hw_bdd, coordCondExp_nonneg (ρ := ρ) (B (Fin.last r)) r,
        coordCondExp_le_one (ρ := ρ) (hB (Fin.last r)) r] with x hwx hE0 hE1
      rw [abs_mul, abs_of_nonneg hE0]
      exact (mul_le_mul hwx hE1 hE0 zero_le_one).trans_eq (one_mul 1)
    calc ∫ x in A, w x * ∏ i : Fin (r + 1),
          (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ
        = ∫ x in A, w x * (g (prefixProj α r x)
            * (B (Fin.last r)).indicator (fun _ => (1 : ℝ)) (x r)) ∂ρ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [Fin.prod_univ_castSucc, hgdef, Fin.val_castSucc, Fin.val_last,
            prefixProj_apply]
      _ = ∫ x in A, w x * (g (prefixProj α r x) * E x) ∂ρ :=
          hρ.setIntegral_weight_mul_prefix_mul_indicator_eq_condExp hw hw_bdd hg_meas hg_bdd
            (hB (Fin.last r)) hA
      _ = ∫ x in A, (fun x => w x * E x) x
            * ∏ i : Fin r, (B i.castSucc).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [hgdef, prefixProj_apply]
          ring
      _ = ∫ x in A, (fun x => w x * E x) x * ∏ i : Fin r,
            ρ[fun y : ℕ → α => (B i.castSucc).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
              MeasurableSpace.invariants (shift α)] x ∂ρ :=
          ih (fun i => B i.castSucc) (fun i => hB _) (fun x => w x * E x) hwE hwE_bdd
      _ = ∫ x in A, w x * ∏ i : Fin (r + 1),
            ρ[fun y : ℕ → α => (B i).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
              MeasurableSpace.invariants (shift α)] x ∂ρ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only [Fin.prod_univ_castSucc, hEdef, Fin.val_castSucc, Fin.val_last]
          ring

end Probability

end TauCeti

end
