/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.Basic
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite-dimensional marginal uniqueness

A finite measure on path space `ℕ → α` is determined by its finite prefix marginals: any measure
agreeing with it on every prefix projection (`prefixProj α n`, the projection to the first `n`
coordinates) is equal to it. This is the Layer 0 finite-marginal uniqueness milestone of
`TauCetiRoadmap/Exchangeability`: a thin ℕ-prefix wrapper over Mathlib's projective-limit
machinery (`IsProjectiveLimit.unique`), not new measure theory.

The public API:
* `measure_eq_of_prefixProj_map_eq` — the map-equality form;
* `measure_eq_of_fin_marginals_eq` — the roadmap-named setwise form.

Both apply directly to probability measures, since `IsProbabilityMeasure` provides
`IsFiniteMeasure`, so no separate probability-measure theorem is needed.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- The restriction to a finite index set `I ⊆ {0, …, n-1}` factors through the prefix projection
to the first `n` coordinates. -/
private theorem finsetRestrict_eq_comp_prefixProj (I : Finset ℕ) {n : ℕ}
    (hn : ∀ i ∈ I, i < n) :
    (Finset.restrict I : (ℕ → α) → ((i : I) → α)) =
      (fun y : Fin n → α => fun i : I => y ⟨i.1, hn i.1 i.2⟩) ∘ prefixProj α n := by
  funext x i
  simp [prefixProj_apply]

/-- **Finite-marginal uniqueness.** Two measures on `ℕ → α`, with `μ` finite, that have the same
law under every finite prefix projection `prefixProj α n` are equal. (Finiteness of `ν` is not
needed: projective-limit uniqueness only requires the prefix-marginal family, supplied by `μ`, to
be finite.) -/
theorem measure_eq_of_prefixProj_map_eq {μ ν : Measure (ℕ → α)} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (prefixProj α n) = ν.map (prefixProj α n)) : μ = ν := by
  -- The two `Finset ℕ`-restriction families agree: a finite index set `I` sits inside the
  -- prefix `{0, …, n-1}` for `n = I.sup id + 1`, so its restriction factors through `prefixProj`.
  have key : ∀ I : Finset ℕ, μ.map I.restrict = ν.map I.restrict := by
    intro I
    obtain ⟨n, hn⟩ : ∃ n, ∀ i ∈ I, i < n :=
      ⟨I.sup id + 1, fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)⟩
    let g : (Fin n → α) → ((i : I) → α) := fun y i => y ⟨i.1, hn i.1 i.2⟩
    have hg : Measurable g := measurable_pi_lambda _ fun i => measurable_pi_apply _
    have hcomp : (Finset.restrict I : (ℕ → α) → ((i : I) → α)) = g ∘ prefixProj α n := by
      simpa [g] using finsetRestrict_eq_comp_prefixProj (α := α) I hn
    calc μ.map I.restrict
        = μ.map (g ∘ prefixProj α n) := by rw [hcomp]
      _ = (μ.map (prefixProj α n)).map g := (Measure.map_map hg (measurable_prefixProj n)).symm
      _ = (ν.map (prefixProj α n)).map g := by rw [h n]
      _ = ν.map (g ∘ prefixProj α n) := Measure.map_map hg (measurable_prefixProj n)
      _ = ν.map I.restrict := by rw [hcomp]
  -- `μ` and `ν` are both projective limits of the family `I ↦ μ.map I.restrict`.
  exact IsProjectiveLimit.unique (P := fun I => μ.map I.restrict)
    (fun I => rfl) (fun I => (key I).symm)

/-- **Finite-marginal uniqueness, setwise form** (the roadmap-named milestone): two measures on
`ℕ → α`, with `μ` finite, agreeing on every measurable prefix-cylinder are equal. It assumes only
`μ` is finite; `ν`'s finiteness is forced by the conclusion. -/
theorem measure_eq_of_fin_marginals_eq {μ ν : Measure (ℕ → α)} [IsFiniteMeasure μ]
    (h : ∀ (n : ℕ) (S : Set (Fin n → α)), MeasurableSet S →
      μ.map (prefixProj α n) S = ν.map (prefixProj α n) S) : μ = ν :=
  measure_eq_of_prefixProj_map_eq fun n => Measure.ext fun S hS => h n S hS

/-- The prefix map onto the first `n` path coordinates, with the directing measure carried along. -/
@[expose]
def prefixPair (T α : Type*) (n : ℕ) : T × (ℕ → α) → T × (Fin n → α) :=
  fun q => (q.1, fun i : Fin n => q.2 i)

theorem measurable_prefixPair (T α : Type*) [MeasurableSpace T] [MeasurableSpace α]
    (n : ℕ) : Measurable (prefixPair T α n) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (i : ℕ)).comp measurable_snd)


/-! ## Paired prefix marginals -/


/-- Longer prefixes refine shorter ones. -/
theorem prefixPair_comp {T α : Type*} [MeasurableSpace T] [MeasurableSpace α] {m n : ℕ}
    (hmn : m ≤ n) : prefixPair T α m
      = (fun r : T × (Fin n → α) =>
          (r.1, fun i : Fin m => r.2 (Fin.castLE hmn i))) ∘ prefixPair T α n := by
  funext q
  simp only [prefixPair, Function.comp_apply, Fin.val_castLE]

/-- Sets pulled back from a finite prefix, with the directing measure carried along. -/
def prefixSets (T α : Type*) [MeasurableSpace T] [MeasurableSpace α] :
    Set (Set (T × (ℕ → α))) :=
  {C | ∃ (n : ℕ) (A : Set (T × (Fin n → α))),
        MeasurableSet A ∧ C = prefixPair T α n ⁻¹' A}

theorem isPiSystem_prefixSets (T α : Type*) [MeasurableSpace T] [MeasurableSpace α] :
    IsPiSystem (prefixSets T α) := by
  rintro _ ⟨m, A, hA, rfl⟩ _ ⟨n, B, hB, rfl⟩ -
  -- Re-present both sets at the longer prefix, where the intersection is a single preimage.
  refine ⟨max m n,
    (fun r : T × (Fin (max m n) → α) =>
        (r.1, fun i : Fin m => r.2 (Fin.castLE (le_max_left m n) i))) ⁻¹' A ∩
      (fun r : T × (Fin (max m n) → α) =>
        (r.1, fun i : Fin n => r.2 (Fin.castLE (le_max_right m n) i))) ⁻¹' B, ?_, ?_⟩
  · exact ((measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
      (measurable_pi_apply _).comp measurable_snd)) hA).inter
      ((measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply _).comp measurable_snd)) hB)
  · rw [Set.preimage_inter, ← Set.preimage_comp, ← Set.preimage_comp,
      ← prefixPair_comp (T := T) (le_max_left m n), ← prefixPair_comp (T := T) (le_max_right m n)]

theorem generateFrom_prefixSets (T α : Type*) [MeasurableSpace T] [MeasurableSpace α] :
    MeasurableSpace.generateFrom (prefixSets T α)
      = (inferInstance : MeasurableSpace (T × (ℕ → α))) := by
  refine le_antisymm ?_ ?_
  · -- Every prefix preimage is measurable.
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨n, A, hA, rfl⟩
    exact measurable_prefixPair T α n hA
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
        ⟨k + 1, (fun r : T × (Fin (k + 1) → α) =>
          r.2 ⟨k, Nat.lt_succ_self k⟩) ⁻¹' U, ?_, ?_⟩
      · exact ((measurable_pi_apply _).comp measurable_snd) hU
      · ext q
        simp [prefixPair]


/-- **Paired finite-marginal uniqueness.** Two measures on `T × (ℕ → α)` that agree under every
prefix projection — keeping the `T` coordinate — are equal.

As with `measure_eq_of_prefixProj_map_eq`, only one of the two measures need be assumed finite: the
`n = 0` projection already forces the total masses to agree, since `prefixPair` retains the first
factor even at the empty prefix. -/
theorem measure_eq_of_prefixPair_map_eq {T : Type*} [MeasurableSpace T]
    {μ ν : Measure (T × (ℕ → α))} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (prefixPair T α n) = ν.map (prefixPair T α n)) : μ = ν := by
  have huniv : μ Set.univ = ν Set.univ := by
    have h0 := congrArg (fun ρ : Measure (T × (Fin 0 → α)) => ρ Set.univ) (h 0)
    simpa only [Measure.map_apply (measurable_prefixPair T α 0) MeasurableSet.univ,
      Set.preimage_univ] using h0
  haveI : IsFiniteMeasure ν := ⟨by rw [← huniv]; exact measure_lt_top μ Set.univ⟩
  refine ext_of_generate_finite (prefixSets T α)
    (generateFrom_prefixSets T α).symm (isPiSystem_prefixSets T α) ?_ huniv
  rintro _ ⟨n, A, hA, rfl⟩
  rw [← Measure.map_apply (measurable_prefixPair T α n) hA,
    ← Measure.map_apply (measurable_prefixPair T α n) hA, h n]


end Probability

end TauCeti
