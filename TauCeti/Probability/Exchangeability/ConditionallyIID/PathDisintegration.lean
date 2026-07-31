/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic
import TauCeti.MeasureTheory.Measure.ProductKernel
import TauCeti.MeasureTheory.Measure.GiryMonad

/-!
# The full-path joint disintegration

`ConditionallyIIDWith μ X ν` constrains the joint law of `(ν, block)` along each *finite* selection
of coordinates. This file upgrades that to the whole path at once: the joint law of the directing
measure together with the entire process is the disintegration `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

## Main results

* `TauCeti.Probability.ConditionallyIIDWith.jointPathLaw_eq_pathDisintegration`

## Implementation

Both measures live on `ProbabilityMeasure α × (ℕ → α)`, and they agree on every finite prefix: the
joint law by the defining identity at the selection `Fin n → ℕ`, the disintegration by projecting
each fibre `δ_Q ⊗ Q^{⊗ℕ}` through `map_prefixProj_infinitePi_const`. Extensionality then comes from
`ext_of_generate_finite` against the π-system `prefixSets` of preimages under the prefix maps
`prefixPair`:

* it is a π-system because two such sets can be re-presented at the longer of their two prefixes
  (`prefixPair_comp`);
* it generates the product σ-algebra, the first factor read off the empty prefix and the path factor
  through `MeasurableSpace.comap_iSup` on the coordinate evaluations.

Mathlib's `IsProjectiveLimit` is stated for pure dependent products `∀ i, α i`, so it does not apply
to this product directly; the π-system argument avoids reindexing the pair through `Option ℕ`.

The path-level form is what downstream work consumes — empirical measures as objects, the
affine/barycenter representation, and ergodic decomposition all read the joint law of `(ν, X)` in
one piece rather than block by block.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint path law: the law of the directing measure together with the whole path. -/
@[expose]
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.map fun ω => (ν ω, fun i => X i ω)

/-- The full-path disintegration measure `∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`. -/
@[expose]
def pathDisintegration (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.bind fun ω =>
    (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))

theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    jointPathLaw μ X ν = μ.map fun ω => (ν ω, fun i => X i ω) := rfl

theorem pathDisintegration_def (μ : Measure Ω) (ν : Ω → ProbabilityMeasure α) :
    pathDisintegration μ ν = μ.bind fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α)) := rfl

/-- The prefix map onto the first `n` path coordinates, with the directing measure carried along. -/
@[expose]
def prefixPair (α : Type*) [MeasurableSpace α] (n : ℕ) :
    ProbabilityMeasure α × (ℕ → α) → ProbabilityMeasure α × (Fin n → α) :=
  fun q => (q.1, fun i : Fin n => q.2 i)

theorem measurable_prefixPair (α : Type*) [MeasurableSpace α] (n : ℕ) :
    Measurable (prefixPair α n) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (i : ℕ)).comp measurable_snd)

/-- The prefix pushforward of the joint path law is the joint block law of the first `n`
coordinates. -/
theorem map_prefix_jointPathLaw (hX : ∀ i, Measurable (X i)) (hν : Measurable ν) (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixPair α n)
      = μ.map fun ω => (ν ω, fun i : Fin n => X i ω) := by
  have hpath : Measurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) :=
    hν.prodMk (measurable_pi_lambda _ hX)
  rw [jointPathLaw_def, Measure.map_map (measurable_prefixPair α n) hpath]
  rfl

/-- The prefix pushforward of the joint path law is the block-level disintegration, by the defining
identity at the first `n` coordinates. -/
theorem map_prefix_jointPathLaw_eq (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i))
    (n : ℕ) :
    (jointPathLaw μ X ν).map (prefixPair α n)
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  rw [map_prefix_jointPathLaw hX h.measurable_directing n]
  exact h.jointLaw_eq_disintegration (fun i : Fin n => (i : ℕ)) Fin.val_injective

/-- The prefix pushforward of the full-path disintegration is the block-level disintegration:
projecting `δ_{ν ω} ⊗ (ν ω)^{⊗ℕ}` onto the first `n` path coordinates leaves
`δ_{ν ω} ⊗ (ν ω)^{⊗ Fin n}`. -/
theorem map_prefix_pathDisintegration (hν : Measurable ν) (n : ℕ) :
    (pathDisintegration μ ν).map (prefixPair α n)
      = μ.bind fun ω =>
          (Measure.dirac (ν ω)).prod (ProbabilityMeasure.pi fun _ : Fin n => ν ω).toMeasure := by
  have hker : Measurable (fun ω =>
      (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))) :=
    (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const (ι' := ℕ)
      (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).comp hν
  -- Projecting one fibre `δ_Q ⊗ Q^{⊗ℕ}` onto the first `n` path coordinates.
  have hfibre : ∀ Q : ProbabilityMeasure α,
      ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
          (prefixPair α n)
        = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
    intro Q
    have hpref : Measurable (fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) :=
      measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
    calc ((Measure.dirac Q).prod (Measure.infinitePi fun _ : ℕ => (Q : Measure α))).map
            (prefixPair α n)
        = ((Measure.dirac Q).map id).prod
            ((Measure.infinitePi fun _ : ℕ => (Q : Measure α)).map
              fun x : ℕ → α => fun i : Fin n => x (i : ℕ)) := by
          rw [Measure.map_prod_map _ _ measurable_id hpref]
          rfl
      _ = (Measure.dirac Q).prod (ProbabilityMeasure.pi fun _ : Fin n => Q).toMeasure := by
          rw [Measure.map_id, TauCeti.MeasureTheory.map_prefixProj_infinitePi_const Q n,
            ProbabilityMeasure.toMeasure_pi]
  rw [pathDisintegration_def,
    TauCeti.MeasureTheory.map_bind hker.aemeasurable (measurable_prefixPair α n)]
  congr 1
  funext ω
  exact hfibre (ν ω)

/-! ### The prefix π-system -/

/-- Longer prefixes refine shorter ones. -/
theorem prefixPair_comp {α : Type*} [MeasurableSpace α] {m n : ℕ} (hmn : m ≤ n) :
    prefixPair α m
      = (fun r : ProbabilityMeasure α × (Fin n → α) =>
          (r.1, fun i : Fin m => r.2 (Fin.castLE hmn i))) ∘ prefixPair α n := by
  funext q
  simp only [prefixPair, Function.comp_apply, Fin.val_castLE]

/-- Sets pulled back from a finite prefix, with the directing measure carried along. -/
def prefixSets (α : Type*) [MeasurableSpace α] :
    Set (Set (ProbabilityMeasure α × (ℕ → α))) :=
  {C | ∃ (n : ℕ) (A : Set (ProbabilityMeasure α × (Fin n → α))),
        MeasurableSet A ∧ C = prefixPair α n ⁻¹' A}

theorem isPiSystem_prefixSets (α : Type*) [MeasurableSpace α] :
    IsPiSystem (prefixSets α) := by
  rintro _ ⟨m, A, hA, rfl⟩ _ ⟨n, B, hB, rfl⟩ -
  -- Re-present both sets at the longer prefix, where the intersection is a single preimage.
  refine ⟨max m n,
    (fun r : ProbabilityMeasure α × (Fin (max m n) → α) =>
        (r.1, fun i : Fin m => r.2 (Fin.castLE (le_max_left m n) i))) ⁻¹' A ∩
      (fun r : ProbabilityMeasure α × (Fin (max m n) → α) =>
        (r.1, fun i : Fin n => r.2 (Fin.castLE (le_max_right m n) i))) ⁻¹' B, ?_, ?_⟩
  · exact ((measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
      (measurable_pi_apply _).comp measurable_snd)) hA).inter
      ((measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply _).comp measurable_snd)) hB)
  · rw [Set.preimage_inter, ← Set.preimage_comp, ← Set.preimage_comp,
      ← prefixPair_comp (le_max_left m n), ← prefixPair_comp (le_max_right m n)]

theorem generateFrom_prefixSets (α : Type*) [MeasurableSpace α] :
    MeasurableSpace.generateFrom (prefixSets α)
      = (inferInstance : MeasurableSpace (ProbabilityMeasure α × (ℕ → α))) := by
  refine le_antisymm ?_ ?_
  · -- Every prefix preimage is measurable.
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, A, hA, rfl⟩
    exact measurable_prefixPair α n hA
  · -- The product σ-algebra is the sup of the two coordinate comaps; catch each.
    rw [Prod.instMeasurableSpace]
    refine sup_le ?_ ?_
    · -- First factor: read it off the empty prefix.
      rintro _ ⟨S, hS, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨0, S ×ˢ Set.univ, hS.prod .univ, ?_⟩
      ext q
      simp [prefixPair]
    · -- Second factor: the path σ-algebra is the sup of the coordinate comaps, so the comap of
      -- `snd` is the sup of the comaps of the coordinate readings.
      have hpi : (MeasurableSpace.pi : MeasurableSpace (ℕ → α))
          = ⨆ k : ℕ, MeasurableSpace.comap (fun x : ℕ → α => x k) inferInstance := rfl
      rw [hpi, MeasurableSpace.comap_iSup]
      refine iSup_le fun k => ?_
      rintro _ ⟨_, ⟨U, hU, rfl⟩, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom
        ⟨k + 1, (fun r : ProbabilityMeasure α × (Fin (k + 1) → α) =>
          r.2 ⟨k, Nat.lt_succ_self k⟩) ⁻¹' U, ?_, ?_⟩
      · exact ((measurable_pi_apply _).comp measurable_snd) hU
      · ext q
        simp [prefixPair]

/-! ### The full-path disintegration -/

/-- **The full-path joint disintegration.** For a conditionally i.i.d. process the joint law of the
directing measure together with the *whole* path is the disintegration
`∫ δ_{ν ω} ⊗ (ν ω)^{⊗ℕ} dμ(ω)`.

The definition of `ConditionallyIIDWith` gives this along each finite selection of coordinates; this
upgrades it to the entire path at once. -/
theorem ConditionallyIIDWith.jointPathLaw_eq_pathDisintegration [IsFiniteMeasure μ]
    (h : ConditionallyIIDWith μ X ν) (hX : ∀ i, Measurable (X i)) :
    jointPathLaw μ X ν = pathDisintegration μ ν := by
  have hpath : Measurable (fun ω => (ν ω, fun i => X i ω) :
      Ω → ProbabilityMeasure α × (ℕ → α)) :=
    h.measurable_directing.prodMk (measurable_pi_lambda _ hX)
  haveI : IsFiniteMeasure (jointPathLaw μ X ν) := by
    rw [jointPathLaw_def]; exact Measure.isFiniteMeasure_map _ _
  refine ext_of_generate_finite (prefixSets α)
    (generateFrom_prefixSets α).symm (isPiSystem_prefixSets α) ?_ ?_
  · -- Agreement on the π-system: each side is a prefix pushforward evaluated at `A`.
    rintro _ ⟨n, A, hA, rfl⟩
    rw [← Measure.map_apply (measurable_prefixPair α n) hA,
      ← Measure.map_apply (measurable_prefixPair α n) hA,
      map_prefix_jointPathLaw_eq h hX n,
      map_prefix_pathDisintegration h.measurable_directing n]
  · -- Equal total mass: both are `μ univ`.
    have hker : Measurable (fun ω =>
        (Measure.dirac (ν ω)).prod (Measure.infinitePi fun _ : ℕ => (ν ω : Measure α))) :=
      (TauCeti.MeasureTheory.measurable_dirac_prod_infinitePi_const (ι' := ℕ)
        (id : ProbabilityMeasure α → ProbabilityMeasure α) measurable_id).comp
        h.measurable_directing
    rw [jointPathLaw_def, Measure.map_apply hpath MeasurableSet.univ, pathDisintegration_def,
      Measure.bind_apply MeasurableSet.univ hker.aemeasurable]
    simp

end Probability

end TauCeti
