/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.Decoupling

/-!
# Factorizing a whole block over an invariant event

Iterating the one-coordinate decoupling across a block of length `r`.

The inductive step takes a block of length `r + 1` and peels its last coordinate, replacing
`𝟙_{B_r}(x_r)` — the factor at index `Fin.last r` — by its conditional expectation given the
shift-invariant σ-algebra, leaving a block of length `r`. The factors already peeled do not vanish:
they accumulate as an invariants-measurable weight, which is exactly what the weighted decoupling
chain carries.

## Main results

All three in the `ContractableLaw` namespace:

* `setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_condExp` — the induction, in
  conditional-expectation form, against an invariants-measurable weight;
* `setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure`
  — the same with each conditional expectation replaced by the invariant conditional law it
  computes;
* `setIntegral_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure`
  — its `w = 1` specialisation, which is the form a cylinder-mass computation consumes.

## Why the conditional expectation, not the witness

The induction carries its accumulated factors as the *weight* of the next step, and the weighted
transport demands a weight that is strictly measurable for `MeasurableSpace.invariants (shift α)`.
A conditional expectation is, by `stronglyMeasurable_condExp`. The invariant conditional law `ν(B)`
is only characterised up to a null set, so it cannot serve. Conversion happens once, at the end.

Everything stays in `ℝ`; the crossing to `ℝ≥0∞` belongs to the common ending, not here.

## Relation to the other `BlockFactorization` files

`DeFinetti/BlockFactorization.lean` and `DeFinetti/ViaL2/BlockFactorization.lean` prove the
corresponding step for the martingale and `L²` routes, conditioning on the tail rather than on the
shift-invariant σ-algebra. Nothing is shared: the two σ-algebras can differ, with
`invariants_shift_lt_pathTail` witnessing strictness over `Bool`-valued paths, and this file
imports neither.

## Source

The Koopman route follows Kallenberg's first proof (see References). No material is adapted from
`cameronfreer/exchangeability`; the induction here is assembled from this repository's own weighted
decoupling chain in `ViaKoopman/Decoupling.lean`.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  Theorem 1.1.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 5** (Koopman operators and
  invariant σ-algebras), whose milestone is `deFinetti_viaKoopman`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

namespace ContractableLaw

/-- **A block factorizes over an invariant event**, in conditional-expectation form.

Peeling the last coordinate replaces `𝟙_{B_r}(x_r)` by its conditional expectation given the
shift-invariant σ-algebra; the factors already peeled ride along as the weight of the next step,
which is why the whole chain is stated against one. -/
theorem setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_condExp
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
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
    have hE_bdd : ∀ᵐ x ∂ρ, ‖E x‖ ≤ 1 :=
      ae_bdd_norm_condExp_of_ae_bdd_norm (Filter.Eventually.of_forall fun y => by
        simpa only [norm_one] using
          norm_indicator_le_norm_self (fun _ => (1 : ℝ)) (y r))
    have hwE_bdd : ∀ᵐ x ∂ρ, |w x * E x| ≤ 1 := by
      filter_upwards [hw_bdd, hE_bdd] with x hwx hEx
      rw [abs_mul]
      exact (mul_le_mul hwx ((Real.norm_eq_abs _) ▸ hEx) (abs_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
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

/-- **The block factorization, with the factors named as the invariant conditional law.**

The conditional expectations of the theorem above are replaced by the invariant conditional law
they compute. The weight is unchanged: the conversion is a pointwise a.e. identity between the
factors, so it does not care what multiplies them. -/
theorem
    setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    (r : ℕ) (B : Fin r → Set α) (hB : ∀ i, MeasurableSet (B i))
    (w : (ℕ → α) → ℝ) (hw : Measurable[MeasurableSpace.invariants (shift α)] w)
    (hw_bdd : ∀ᵐ x ∂ρ, |w x| ≤ 1) :
    ∫ x in A, w x * ∏ i : Fin r, (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ
      = ∫ x in A, w x * ∏ i : Fin r,
          ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) ∂ρ := by
  rw [hρ.setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_condExp hA r B hB w hw hw_bdd]
  refine integral_congr_ae ?_
  have hall : ∀ᵐ x ∂ρ, ∀ i : Fin r,
      ρ[fun y : ℕ → α => (B i).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
        MeasurableSpace.invariants (shift α)] x
        = ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) :=
    ae_all_iff.2 fun i =>
      hρ.condExp_indicator_coord_ae_eq_invariantConditionalProbabilityMeasure (hB i) (i : ℕ)
  filter_upwards [ae_restrict_of_ae hall] with x hx
  exact congrArg _ (Finset.prod_congr rfl fun i _ => hx i)

/-- **The unweighted form**, which is what a cylinder-mass computation consumes: the `w = 1`
specialisation of the theorem above. -/
theorem setIntegral_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    (r : ℕ) (B : Fin r → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    ∫ x in A, ∏ i : Fin r, (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ
      = ∫ x in A, ∏ i : Fin r,
          ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) ∂ρ := by
  have hweighted :=
    setIntegral_weight_mul_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure
      hρ hA r B hB (fun _ => (1 : ℝ)) measurable_const
      (Filter.Eventually.of_forall fun _ => by norm_num)
  simpa only [one_mul] using hweighted

end ContractableLaw

end Probability

end TauCeti

end
