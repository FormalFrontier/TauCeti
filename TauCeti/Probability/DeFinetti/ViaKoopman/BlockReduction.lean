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

Both in the `ContractableLaw` namespace:

* `measure_inter_blockCylinder_eq_prefix_of_strictMono` — over any shift-invariant event, an
  arbitrary strictly increasing block has the same mass as the prefix block;
* `measure_preimage_invariantConditionalProbabilityMeasure_inter_blockCylinder_eq_prefix` — the
  specialisation to a test event cut out by the witness.

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

## Source

No material is adapted from `cameronfreer/exchangeability`. That development carries its own
`DeFinetti/ViaKoopman` material covering this step; the reduction here is assembled from Tau Ceti's
own pieces — the block transport of `PathSpace/Invariant/BlockTransport.lean` and the
cylinder-rectangle bridge `blockCylinder_eq_preimage_univ_pi`.

## References

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

/-- **An arbitrary strictly increasing block may be read at the prefix**, over any shift-invariant
event.

The event being invariant, the identity holds at the level of the measure itself: both selections
push `ρ.restrict A` to the same law on `Fin r → α`, by
`ContractableLaw.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants`. No conditional
expectation and no integrability hypothesis appears. -/
theorem measure_inter_blockCylinder_eq_prefix_of_strictMono
    {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ)
    {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i))
    {A : Set (ℕ → α)} (hA : MeasurableSet[MeasurableSpace.invariants (shift α)] A) :
    ρ (A ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = ρ (A ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin r => (i : ℕ)) B) := by
  have hpi : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  have hsel : ∀ s : Fin r → ℕ, Measurable fun (x : ℕ → α) (i : Fin r) => x (s i) :=
    fun s => measurable_pi_lambda _ fun i => measurable_pi_apply (s i)
  -- Cross the `prefixProj` wrapper through its API, not by unfolding the definition.
  have hprefix : (fun (x : ℕ → α) (i : Fin r) => x (i : ℕ)) = prefixProj α r :=
    funext fun x => funext fun i => (prefixProj_apply r x i).symm
  -- Each side is the pushforward of the restricted law, read on the rectangle.
  have hkey : ∀ s : Fin r → ℕ,
      ρ (A ∩ blockCylinder (fun j (x : ℕ → α) => x j) s B)
        = ((ρ.restrict A).map fun (x : ℕ → α) (i : Fin r) => x (s i)) (Set.univ.pi B) := by
    intro s
    rw [Measure.map_apply (hsel s) hpi, Measure.restrict_apply ((hsel s) hpi),
      blockCylinder_eq_preimage_univ_pi, Set.inter_comm]
  rw [hkey k, hkey (fun i : Fin r => (i : ℕ)), hprefix]
  exact congrArg (fun μ : Measure (Fin r → α) => μ (Set.univ.pi B))
    (hρ.map_restrict_prefixProj_of_strictMono_of_measurableSet_invariants hk hA)

/-- The same, over a test event cut out by the invariant conditional law. -/
theorem measure_preimage_invariantConditionalProbabilityMeasure_inter_blockCylinder_eq_prefix
    [StandardBorelSpace α] [Nonempty α]
    {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ] (hρ : ContractableLaw ρ)
    {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    ρ ((invariantConditionalProbabilityMeasure ρ ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) k B)
      = ρ ((invariantConditionalProbabilityMeasure ρ ⁻¹' S)
        ∩ blockCylinder (fun j (x : ℕ → α) => x j) (fun i : Fin r => (i : ℕ)) B) :=
  hρ.measure_inter_blockCylinder_eq_prefix_of_strictMono hk hB
    (measurable_invariants_invariantConditionalProbabilityMeasure hS)

end ContractableLaw

end Probability

end TauCeti

end
