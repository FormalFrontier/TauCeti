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
shift-invariant, so the block transport of
`ContractableLaw.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants` applies to it:
the mass of a block cylinder met with such an event does not depend on which
strictly increasing selection is used, and may be computed at the prefix `0, 1, …, r - 1`.

## Main results

* `ContractableLaw.measure_inter_blockCylinder_eq_prefix_of_invariantConditional` — over such an
  event, an arbitrary strictly increasing block has the same mass as the prefix block.

## Why this route does not need conditional expectations here

The `L²` route reaches the corresponding statement through
`Contractable.condExp_block_comp_tailProcess_ae_eq`, an a.e. identity of *conditional
expectations*: two selections have the same conditional law given the tail, which is a
distributional statement about real-valued observables.

Here the test event is genuinely invariant — `shift ⁻¹' A = A` — so the block may be displaced at
the level of the measure itself: both selections push `ρ.restrict A` to the same law on
`Fin r → α`, and the cylinder is read on that law as a rectangle. No conditional expectation and no
integrability side condition appears. That is the concrete form of the difference
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

/-- **An arbitrary strictly increasing block may be read at the prefix**, over a test event cut out
by the invariant conditional law.

No conditional expectation appears: the event is invariant, so the block is displaced inside the
integral: both selections push `ρ.restrict A` to the same measure on `Fin r → α`, by
`ContractableLaw.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants`. -/
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
    measurable_invariants_invariantConditionalProbabilityMeasure hS
  have hpi : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  have hsel : ∀ s : Fin r → ℕ, Measurable fun (x : ℕ → α) (i : Fin r) => x (s i) :=
    fun s => measurable_pi_lambda _ fun i => measurable_pi_apply (s i)
  -- Each side is the pushforward of the restricted law, read on the rectangle.
  have hkey : ∀ s : Fin r → ℕ,
      ρ (A ∩ blockCylinder (fun j (x : ℕ → α) => x j) s B)
        = ((ρ.restrict A).map fun (x : ℕ → α) (i : Fin r) => x (s i)) (Set.univ.pi B) := by
    intro s
    rw [Measure.map_apply (hsel s) hpi, Measure.restrict_apply ((hsel s) hpi),
      blockCylinder_eq_preimage_univ_pi, Set.inter_comm]
  rw [hkey k, hkey (fun i : Fin r => (i : ℕ))]
  exact congrArg (fun μ : Measure (Fin r → α) => μ (Set.univ.pi B))
    (hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants hk hA_inv)

end Probability

end TauCeti

end
