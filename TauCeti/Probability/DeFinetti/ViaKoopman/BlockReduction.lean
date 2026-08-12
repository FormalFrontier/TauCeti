/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.PathSpace.Invariant.BlockTransport
public import TauCeti.Probability.DeFinetti.ViaKoopman.InvariantConditionalLaw
public import TauCeti.Probability.Exchangeability.Cylinder

/-!
# Reducing a block to the prefix over an invariant-conditional-law event

The Koopman route's first reduction. A test event cut out by the invariant conditional law is
shift-invariant, so `ContractableLaw.setLIntegral_block_eq_prefix_of_measurableSet_invariants`
applies to it: the mass of a block cylinder met with such an event does not depend on which
strictly increasing selection is used, and may be computed at the prefix `0, 1, …, r - 1`.

## Main results

* `measurableSet_invariants_preimage_invariantConditionalProbabilityMeasure` — a test event cut out
  by the witness is invariants-measurable;
* `ContractableLaw.measure_inter_blockCylinder_eq_prefix_of_invariantConditional` — over such an
  event, an arbitrary strictly increasing block has the same mass as the prefix block.

## Why this route does not need conditional expectations here

The `L²` route reaches the corresponding statement through
`Contractable.condExp_block_comp_tailProcess_ae_eq`, an a.e. identity of *conditional
expectations*: two selections have the same conditional law given the tail, which is a
distributional statement about real-valued observables.

Here the test event is genuinely invariant — `shift ⁻¹' A = A` — so the block may be displaced
inside the integral itself, and the whole reduction stays in `ℝ≥0∞` with no conditional
expectation and no integrability side conditions. That is the concrete form of the difference
between the two routes; they are deliberately not unified into a σ-algebra-parametric statement,
since `invariants_shift_lt_pathTail` shows the underlying σ-algebras genuinely differ.

## References

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

/-- **A test event cut out by the invariant conditional law is invariant.** The witness is
measurable for `MeasurableSpace.invariants (shift α)`, so preimages of measurable sets of
probability measures are invariants-measurable — which is exactly the hypothesis the block
transport wants. -/
theorem measurableSet_invariants_preimage_invariantConditionalProbabilityMeasure
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] {S : Set (ProbabilityMeasure α)}
    (hS : MeasurableSet S) :
    MeasurableSet[MeasurableSpace.invariants (shift α)]
      (invariantConditionalProbabilityMeasure ρ ⁻¹' S) :=
  measurable_invariants_invariantConditionalProbabilityMeasure hS

/-- **An arbitrary strictly increasing block may be read at the prefix**, over a test event cut out
by the invariant conditional law.

No conditional expectation appears: the event is invariant, so the block is displaced inside the
integral by `ContractableLaw.setLIntegral_block_eq_prefix_of_measurableSet_invariants`. -/
theorem ContractableLaw.measure_inter_blockCylinder_eq_prefix_of_invariantConditional
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
    {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    ρ ((invariantConditionalProbabilityMeasure ρ ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = ρ ((invariantConditionalProbabilityMeasure ρ ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin r => (i : ℕ)) B) := by
  classical
  set A : Set (ℕ → α) := invariantConditionalProbabilityMeasure ρ ⁻¹' S with hA
  have hA_inv : MeasurableSet[MeasurableSpace.invariants (shift α)] A :=
    measurableSet_invariants_preimage_invariantConditionalProbabilityMeasure hS
  -- The cylinder indicator is a block observable of the coordinates, in `ℝ≥0∞`.
  set g : (Fin r → α) → ℝ≥0∞ := fun y => ∏ i, (B i).indicator (fun _ => (1 : ℝ≥0∞)) (y i) with hg
  have hg_meas : Measurable g :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_const.indicator (hB i)).comp (measurable_pi_apply i)
  -- On each side the indicator of the cylinder is that observable read along the selection.
  have hind : ∀ (s : Fin r → ℕ) (x : ℕ → α),
      (blockCylinder (fun j (y : ℕ → α) => y j) s B).indicator (fun _ => (1 : ℝ≥0∞)) x
        = g (fun i => x (s i)) := by
    intro s x
    by_cases hx : x ∈ blockCylinder (fun j (y : ℕ → α) => y j) s B
    · rw [Set.indicator_of_mem hx, hg]
      exact (Finset.prod_eq_one fun i _ =>
        Set.indicator_of_mem (mem_blockCylinder.mp hx i) _).symm
    · rw [Set.indicator_of_notMem hx, hg]
      simp only [mem_blockCylinder, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  have hcyl : ∀ s : Fin r → ℕ,
      MeasurableSet (blockCylinder (fun j (y : ℕ → α) => y j) s B) := fun s =>
    measurableSet_blockCylinder (fun i => measurable_pi_apply _) hB
  -- The mass of the intersection is the set-integral of the block observable over `A`.
  have hmass : ∀ s : Fin r → ℕ,
      ρ (A ∩ blockCylinder (fun j (y : ℕ → α) => y j) s B)
        = ∫⁻ x in A, g (fun i => x (s i)) ∂ρ := by
    intro s
    have hrw : ∀ x : ℕ → α, g (fun i => x (s i))
        = (blockCylinder (fun j (y : ℕ → α) => y j) s B).indicator (fun _ => (1 : ℝ≥0∞)) x :=
      fun x => (hind s x).symm
    simp only [hrw]
    rw [lintegral_indicator (hcyl s), setLIntegral_one, Measure.restrict_apply (hcyl s),
      Set.inter_comm]
  rw [hmass k, hmass (fun i : Fin r => (i : ℕ)),
    hρ.setLIntegral_block_eq_prefix_of_measurableSet_invariants hk hA_inv hg_meas,
    hρ.setLIntegral_block_eq_prefix_of_measurableSet_invariants
      (k := fun i : Fin r => (i : ℕ)) Fin.val_strictMono hA_inv hg_meas]

end Probability

end TauCeti

end
