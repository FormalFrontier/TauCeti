/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.DeFinetti.ViaKoopman.BlockFactorization
public import TauCeti.Probability.Exchangeability.Cylinder
import TauCeti.Probability.Exchangeability.PathSpace.Invariant.BlockTransport
import TauCeti.MeasureTheory.Integral.ENNRealProd

/-!
# The block-cylinder mass, in the shape the common ending consumes

The Koopman route's pieces assembled into the single hypothesis that
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral` asks for.

The block reduction moves an arbitrary strictly increasing selection onto the prefix; the block
factorization turns the prefix cylinder's mass into an integral of a product of conditional
expectations; naming those as the invariant conditional law and crossing once into `ℝ≥0∞` gives
the identity.

## Main results

* `ContractableLaw.measure_inter_blockCylinder_eq_setLIntegral_of_measurableSet_invariants` — over
  any shift-invariant event, the block-cylinder mass is the integral of the product of the
  invariant conditional law's values.

A consumer wanting the `hcore` hypothesis of
`conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral` applies this to a witness
event, whose invariance is `measurable_invariants_invariantConditionalProbabilityMeasure`.

The crossing to `ℝ≥0∞` happens exactly once, here, through the route-neutral
`TauCeti.MeasureTheory.ofReal_integral_prod_toReal_eq_lintegral_prod`; everything upstream is
real-valued. Integrability of the witness product is obtained from the conditional-expectation
product it is a.e. equal to, which avoids needing measurability of the witness evaluation
directly.

## Source

The Koopman route follows Kallenberg's first proof (see References). No material is adapted from
`cameronfreer/exchangeability`; this assembles Tau Ceti's own block reduction, block factorization
and `ℝ≥0∞` bridge.

## References

* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 1,
  Theorem 1.1.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 5** (Koopman operators and
  invariant σ-algebras), whose milestone is `deFinetti_viaKoopman`.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

namespace ContractableLaw

/-- **The block-cylinder mass over an invariant event.** Over any shift-invariant event, the mass
of a block cylinder is the integral of the product of the invariant conditional law's values on the
coordinate sets. -/
theorem measure_inter_blockCylinder_eq_setLIntegral_of_measurableSet_invariants
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
    {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k)
    {A : Set (ℕ → α)} (hA_inv : MeasurableSet[MeasurableSpace.invariants (shift α)] A)
    {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    ρ (A ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = ∫⁻ x in A, ∏ i, (invariantConditionalProbabilityMeasure ρ x : Measure α) (B i) ∂ρ := by
  -- The two products, real-valued.
  set P : (ℕ → α) → ℝ := fun x =>
    ∏ i : Fin r, ρ[fun y : ℕ → α => (B i).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
      MeasurableSpace.invariants (shift α)] x with hPdef
  set Q : (ℕ → α) → ℝ := fun x =>
    ∏ i : Fin r, ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) with hQdef
  -- Naming each conditional expectation as the witness, all `r` at once.
  have hPQ : P =ᵐ[ρ] Q := by
    have hall : ∀ᵐ x ∂ρ, ∀ i : Fin r,
        ρ[fun y : ℕ → α => (B i).indicator (fun _ => (1 : ℝ)) (y (i : ℕ)) |
          MeasurableSpace.invariants (shift α)] x
          = ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) :=
      ae_all_iff.2 fun i =>
        hρ.condExp_indicator_coord_ae_eq_invariantConditionalProbabilityMeasure (hB i) (i : ℕ)
    filter_upwards [hall] with x hx
    simp only [hPdef, hQdef]
    exact Finset.prod_congr rfl fun i _ => hx i
  -- `Q` is bounded by one, pointwise: each factor is a probability of a set.
  have hQ_bdd : ∀ x, ‖Q x‖ ≤ 1 := by
    intro x
    have h0 : ∀ i : Fin r, (0 : ℝ) ≤
        ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) :=
      fun i => measureReal_nonneg
    have h1 : ∀ i : Fin r,
        ((invariantConditionalProbabilityMeasure ρ x : Measure α)).real (B i) ≤ 1 :=
      fun i => measureReal_le_one
    rw [Real.norm_eq_abs, hQdef, abs_of_nonneg (Finset.prod_nonneg fun i _ => h0 i)]
    exact Finset.prod_le_one (fun i _ => h0 i) fun i _ => h1 i
  have hP_meas : Measurable P := by
    refine Finset.measurable_prod _ fun i _ => ?_
    exact (stronglyMeasurable_condExp.measurable).mono
      (MeasurableSpace.invariants_le (shift α)) le_rfl
  have hQ_int : Integrable Q (ρ.restrict A) :=
    ⟨((hP_meas.aestronglyMeasurable).congr hPQ).restrict,
      .of_bounded (C := 1) (Filter.Eventually.of_forall hQ_bdd)⟩
  -- Move the block onto the prefix.
  rw [hρ.measure_inter_blockCylinder_eq_prefix_of_strictMono_of_measurableSet_invariants
    hk hB hA_inv]
  set C : Set (ℕ → α) :=
    blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin r => (i : ℕ)) B with hCdef
  have hcyl : MeasurableSet C :=
    measurableSet_blockCylinder (fun i => measurable_pi_apply _) hB
  -- The prefix cylinder's mass, as a real integral of the indicator product.
  have hstep3 : (ρ (A ∩ C)).toReal
      = ∫ x in A, ∏ i : Fin r, (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ)) ∂ρ := by
    have hrw : ∀ x : ℕ → α,
        ∏ i : Fin r, (B i).indicator (fun _ => (1 : ℝ)) (x (i : ℕ))
          = C.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      rw [hCdef, ← blockIndicatorProd_eq_indicator (fun j (y : ℕ → α) => y j)
        (fun i : Fin r => (i : ℕ)) B, blockIndicatorProd_apply]
    simp only [hrw]
    rw [setIntegral_indicator hcyl, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- The block factorization, already specialised to weight one and named as the witness.
  have hmass : (ρ (A ∩ C)).toReal = ∫ x in A, Q x ∂ρ :=
    hstep3.trans
      (hρ.setIntegral_blockIndicatorProd_prefix_eq_prod_invariantConditionalProbabilityMeasure
        hA_inv r B hB)
  -- Cross to `ℝ≥0∞`, once.
  have hne : ∀ᵐ x ∂ρ.restrict A,
      (∏ i : Fin r, (invariantConditionalProbabilityMeasure ρ x : Measure α) (B i)) ≠ ∞ :=
    Filter.Eventually.of_forall fun x =>
      ENNReal.prod_ne_top fun i _ => measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ (A ∩ C)), hmass]
  exact TauCeti.MeasureTheory.ofReal_integral_prod_toReal_eq_lintegral_prod hne hQ_int

end ContractableLaw

end Probability

end TauCeti

end
