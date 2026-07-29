/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.ConditionallyIID.Basic

/-!
# The conditional rectangle common ending for de Finetti

This file supplies the joint-law companion of the mixture rectangle common ending.  To prove that
a measurable random probability measure `ν : Ω → ProbabilityMeasure α` directs a process, it is
enough to verify the expected disintegration on sets of the form

```text
S ×ˢ Set.univ.pi B
```

where `S` is measurable in `ProbabilityMeasure α` and `B` is a measurable finite rectangle in the
block coordinates.  These sets form a π-system generating the joint product σ-algebra, so equality
there extends to the full joint-law identity in `ConditionallyIIDWith`.

## Main results

* `conditionallyIID_of_jointRectangles` — the Layer 1 common ending, at a named directing measure;
* `ConditionallyIIDWith.jointLaw_prod_univ_pi` — the converse rectangle identity;
* `conditionallyIIDWith_iff_forall_jointRectangles` and
  `conditionallyIID_iff_exists_forall_jointRectangles` — characteristic forms for the named and
  existential predicates.

This advances `TauCetiRoadmap/Exchangeability/README.md`, Layer 1, the conditional common ending
`conditionallyIID_of_jointRectangles`.  The joint-law formulation is Kallenberg's conditional
i.i.d. identity (*Probabilistic Symmetries and Invariance Principles*, 2005, §1.1, equation (2)).
The rectangle-extension argument is the joint-space analogue of the common-ending strategy in
`cameronfreer/exchangeability` (`DeFinetti/CommonEnding.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`), adapted to Tau Ceti's stronger
`ConditionallyIIDWith` predicate and Mathlib's `generateFrom_eq_prod`, `generateFrom_pi`, and
π-system API.
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace Set

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- Two finite measures on `γ × (∀ i, β i)` agree if they agree on products of a measurable set
in `γ` and a measurable box in the finite product. -/
private theorem measure_eq_of_forall_prod_univ_pi
    {γ ι : Type*} [MeasurableSpace γ] [Finite ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {μ ν : Measure (γ × (∀ i, β i))} [IsFiniteMeasure μ]
    (h : ∀ (S : Set γ), MeasurableSet S →
      ∀ B : ∀ i, Set (β i), (∀ i, MeasurableSet (B i)) →
        μ (S ×ˢ Set.univ.pi B) = ν (S ×ˢ Set.univ.pi B)) :
    μ = ν := by
  letI := Fintype.ofFinite ι
  refine ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) {S : Set γ | MeasurableSet S}
      (Set.pi Set.univ '' Set.pi Set.univ fun i => {B : Set (β i) | MeasurableSet B}))
    ?_ ?_ ?_ ?_
  · exact (generateFrom_eq_prod generateFrom_measurableSet generateFrom_pi
      isCountablySpanning_measurableSet
      (IsCountablySpanning.pi fun _ => isCountablySpanning_measurableSet)).symm
  · exact isPiSystem_measurableSet.prod isPiSystem_pi
  · rintro _ ⟨S, hS, _, ⟨B, hB, rfl⟩, rfl⟩
    exact h S hS B fun i => hB i (Set.mem_univ i)
  · simpa using h Set.univ MeasurableSet.univ (fun _ => Set.univ)
      (fun _ => MeasurableSet.univ)

/-- **Conditional common de Finetti ending.** If the joint law of a measurable random probability
measure `ν` and every injective finite block agrees with
`∫ δ_{ν(ω)} ⊗ (ν(ω))^{⊗m} ∂μ(ω)` on all measurable products of a set in the `ν` coordinate and a
rectangle in the block coordinates, then `ν` directs the process.

No measurability hypothesis on the coordinates of `X` is needed: the rectangle identities are
already exactly the data used to extend the two finite joint measures. -/
theorem conditionallyIID_of_jointRectangles {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α} (hν : Measurable ν)
    (h_rect : ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
      ∀ S : Set (ProbabilityMeasure α), MeasurableSet S →
        ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
          (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)) (S ×ˢ Set.univ.pi B) =
            (μ.bind fun ω =>
              (Measure.dirac (ν ω)).prod
                (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure)
              (S ×ˢ Set.univ.pi B)) :
    ConditionallyIIDWith μ X ν := by
  refine ConditionallyIIDWith.intro hν fun m k hk => ?_
  haveI : IsFiniteMeasure (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)) :=
    inferInstance
  exact measure_eq_of_forall_prod_univ_pi (h_rect m k hk)

/-- A `ConditionallyIIDWith` witness gives the joint disintegration on a product of an arbitrary
set in the directing-measure coordinate and an arbitrary finite block rectangle. -/
@[grind =>]
theorem ConditionallyIIDWith.jointLaw_prod_univ_pi {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} (h : ConditionallyIIDWith μ X ν)
    {m : ℕ} (k : Fin m → ℕ) (hk : Function.Injective k)
    (S : Set (ProbabilityMeasure α)) (B : Fin m → Set α) :
    (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω)) (S ×ˢ Set.univ.pi B) =
      (μ.bind fun ω =>
        (Measure.dirac (ν ω)).prod
          (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure)
        (S ×ˢ Set.univ.pi B) := by
  rw [h.jointLaw_eq_disintegration k hk]

/-- Joint-rectangle factorization characterizes `ConditionallyIIDWith` for a finite base
measure. -/
theorem conditionallyIIDWith_iff_forall_jointRectangles
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} :
    ConditionallyIIDWith μ X ν ↔
      Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          ∀ S : Set (ProbabilityMeasure α), MeasurableSet S →
            ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
              (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω))
                  (S ×ˢ Set.univ.pi B) =
                (μ.bind fun ω =>
                  (Measure.dirac (ν ω)).prod
                    (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure)
                  (S ×ˢ Set.univ.pi B) := by
  constructor
  · intro h
    exact ⟨h.measurable_directing, fun m k hk S _ B _ =>
      h.jointLaw_prod_univ_pi k hk S B⟩
  · rintro ⟨hν, h_rect⟩
    exact conditionallyIID_of_jointRectangles hν h_rect

/-- Joint-rectangle factorization characterizes the existential predicate `ConditionallyIID` for
a finite base measure. -/
theorem conditionallyIID_iff_exists_forall_jointRectangles
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} :
    ConditionallyIID μ X ↔
      ∃ ν : Ω → ProbabilityMeasure α, Measurable ν ∧
        ∀ (m : ℕ) (k : Fin m → ℕ), Function.Injective k →
          ∀ S : Set (ProbabilityMeasure α), MeasurableSet S →
            ∀ B : Fin m → Set α, (∀ i, MeasurableSet (B i)) →
              (μ.map fun ω => (ν ω, fun i : Fin m => X (k i) ω))
                  (S ×ˢ Set.univ.pi B) =
                (μ.bind fun ω =>
                  (Measure.dirac (ν ω)).prod
                    (ProbabilityMeasure.pi fun _ : Fin m => ν ω).toMeasure)
                  (S ×ˢ Set.univ.pi B) := by
  simp_rw [conditionallyIID_iff, conditionallyIIDWith_iff_forall_jointRectangles]

end Probability

end TauCeti
