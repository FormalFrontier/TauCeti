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
* `measure_eq_of_fin_marginals_eq` — the roadmap-named setwise form;
* `prefixPair`, `measurable_prefixPair`, `prefixPair_comp` — the same prefix projection carrying an
  extra factor along;
* `measure_eq_of_prefixPair_map_eq` — paired finite-marginal uniqueness on `T × (ℕ → α)`.

The paired form reduces to the unpaired one rather than reproving it. Mathlib's
`IsProjectiveLimit` is stated for dependent products `∀ i, α i`, and `T × (ℕ → α)` is not of that
shape — but replicating the first factor at every coordinate, `(t, x) ↦ fun n => (t, x n)`, embeds
it in `ℕ → T × α`, which is. That map has an explicit measurable left inverse, so it is injective on
measures, and each of its prefix marginals is read off the paired prefix marginal one step longer.

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

/-- The prefix map onto the first `n` path coordinates, keeping the first factor. -/
def prefixPair (T α : Type*) (n : ℕ) : T × (ℕ → α) → T × (Fin n → α) :=
  fun q => (q.1, fun i : Fin n => q.2 i)

/-- Applying the paired prefix map. -/
@[simp]
theorem prefixPair_apply {T α : Type*} (n : ℕ) (q : T × (ℕ → α)) :
    prefixPair T α n q = (q.1, fun i : Fin n => q.2 i) :=
  (rfl)

theorem measurable_prefixPair (T α : Type*) [MeasurableSpace T] [MeasurableSpace α]
    (n : ℕ) : Measurable (prefixPair T α n) :=
  measurable_fst.prodMk (measurable_pi_lambda _ fun i =>
    (measurable_pi_apply (i : ℕ)).comp measurable_snd)


/-! ## Paired prefix marginals -/


/-- Longer prefixes refine shorter ones. -/
theorem prefixPair_comp {T α : Type*} {m n : ℕ} (hmn : m ≤ n) : prefixPair T α m
      = (fun r : T × (Fin n → α) =>
          (r.1, fun i : Fin m => r.2 (Fin.castLE hmn i))) ∘ prefixPair T α n := by
  funext q
  simp only [prefixPair, Function.comp_apply, Fin.val_castLE]

/-- **Paired finite-marginal uniqueness.** Two measures on `T × (ℕ → α)` that agree under every
prefix projection — keeping the `T` coordinate — are equal.

As with `measure_eq_of_prefixProj_map_eq`, only one of the two measures need be assumed finite: the
`n = 0` projection already forces the total masses to agree, since `prefixPair` retains the first
factor even at the empty prefix. -/
theorem measure_eq_of_prefixPair_map_eq {T : Type*} [MeasurableSpace T]
    {μ ν : Measure (T × (ℕ → α))} [IsFiniteMeasure μ]
    (h : ∀ n, μ.map (prefixPair T α n) = ν.map (prefixPair T α n)) : μ = ν := by
  -- Replicate the first factor at every coordinate, turning the pair into an honest path.
  set R : T × (ℕ → α) → (ℕ → T × α) := fun q n => (q.1, q.2 n) with hR
  have hRm : Measurable R := measurable_pi_lambda _ fun n =>
    measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)
  -- `R` has an explicit measurable left inverse, so it is injective on measures.
  have hL : Function.LeftInverse (fun y : ℕ → T × α => ((y 0).1, fun n => (y n).2)) R := by
    intro q; ext <;> rfl
  have hLm : Measurable (fun y : ℕ → T × α => ((y 0).1, fun n => (y n).2)) :=
    (measurable_fst.comp (measurable_pi_apply 0)).prodMk
      (measurable_pi_lambda _ fun n => measurable_snd.comp (measurable_pi_apply n))
  haveI : IsFiniteMeasure (μ.map R) := Measure.isFiniteMeasure_map _ _
  -- Enough to identify the replicated measures: the left inverse recovers the originals.
  suffices hmap : (μ.map R) = (ν.map R) by
    have := congrArg (fun ρ => ρ.map (fun y : ℕ → T × α => ((y 0).1, fun n => (y n).2))) hmap
    simpa only [Measure.map_map hLm hRm, Function.comp_def, hL _, Measure.map_id'] using this
  -- Prefix marginals of the replicated measures come from the paired prefix marginals.
  refine measure_eq_of_prefixProj_map_eq fun n => ?_
  have hstep : ∀ ρ : Measure (T × (ℕ → α)),
      (ρ.map R).map (prefixProj (T × α) n)
        = (ρ.map (prefixPair T α (n + 1))).map
            (fun r : T × (Fin (n + 1) → α) => fun i : Fin n => (r.1, r.2 i.castSucc)) := by
    intro ρ
    have hcut : Measurable (fun r : T × (Fin (n + 1) → α) => fun i : Fin n =>
        (r.1, r.2 i.castSucc)) :=
      measurable_pi_lambda _ fun i =>
        measurable_fst.prodMk ((measurable_pi_apply i.castSucc).comp measurable_snd)
    rw [Measure.map_map (measurable_prefixProj (α := T × α) n) hRm,
      Measure.map_map hcut (measurable_prefixPair T α (n + 1))]
    congr 1
  rw [hstep μ, hstep ν, h (n + 1)]

end Probability

end TauCeti
