/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Process.Tail.Basic

/-!
# Conditional law of a contractable selection given the tail

For a contractable process `X`, the conditional law of a selection of coordinates given the future,
or given the tail, does not depend on *which* coordinates were selected. Four results, stated for
an arbitrary measurable real observable `f`:

* `Contractable.condExp_block_comp_future_ae_eq` — for two strictly monotone *blocks* of the same
  length lying below a cutoff `c`, the conditional expectations of `f` along each block, given the
  future σ-algebra `tailFamily X c`, agree a.e.
* `Contractable.condExp_comp_future_ae_eq` — its single-coordinate case, for heads `j, k` below the
  cutoff.
* `Contractable.condExp_block_comp_tailProcess_ae_eq` — the block form conditioning on the process
  tail `tailProcess X`.
* `Contractable.condExp_comp_tailProcess_ae_eq` — its single-coordinate case, the "extreme members
  agree on the tail" step.

The block forms are what a route needs in order to replace one selection by another *underneath* a
tail conditioning. The mechanism is distributional: both selections are appended to the same
future, and contractability equates the joint laws. Nothing here makes a tail event invariant under
reindexing.

All are facts about contractable processes alone, so they live in the shared exchangeability
layer: the `L²` route's Cesàro bridge consumes the general form, while the indicator
specializations the de Finetti directing-measure construction consumes are in
`TauCeti.Probability.DeFinetti.CondExpConvergence`.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/CondExpConvergence.lean`,
`condexp_convergence` and `extreme_members_equal_on_tail_via_tower`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`).
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The reindexing that reads a strictly monotone block `k` first and then the future from `c` is
`prefixSplitEquiv.symm` applied to that pair: it glues the block onto the tail `n ↦ c + n`. -/
private theorem strictMono_prefixSplitEquiv_symm_block_future {r c : ℕ} {k : Fin r → ℕ}
    (hk : StrictMono k) (hkc : ∀ i, k i < c) :
    StrictMono ((prefixSplitEquiv (α := ℕ) r).symm (k, fun n => c + n)) := by
  intro a b hab
  simp only [prefixSplitEquiv_symm_apply]
  by_cases ha : a < r
  · by_cases hb : b < r
    · rw [dite_eq_left ha, dite_eq_left hb]
      exact hk (by exact_mod_cast hab)
    · rw [dite_eq_left ha, dite_eq_right hb]
      exact Nat.lt_add_right _ (hkc ⟨a, ha⟩)
  · have hb : ¬ b < r := fun h => ha (hab.trans h)
    rw [dite_eq_right ha, dite_eq_right hb]
    exact Nat.add_lt_add_left (Nat.sub_lt_sub_right (Nat.not_lt.mp ha) hab) c

/-- **A strictly monotone block joins a common future exactly as the path law does.** For a
contractable process, a strictly monotone selection `k` lying below a cutoff `c`, the joint law of
the block `(X (k 0), …, X (k (r-1)))` with the future `(X c, X (c+1), …)` is the path law pushed
through `prefixSplitEquiv r`, which is exactly that split.

Two such blocks therefore have the *same* joint law with the *same* future — which is what makes a
conditional statement given that future available. Note the equality is distributional: nothing
here says a tail event is pointwise invariant under reindexing. -/
private theorem map_block_future_eq_pathLaw_map {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_ae : ∀ n, AEMeasurable (X n) μ)
    {r c : ℕ} {k : Fin r → ℕ} (hk : StrictMono k) (hkc : ∀ i, k i < c) :
    μ.map (fun ω => (fun i : Fin r => X (k i) ω, fun n => X (c + n) ω))
      = (pathLaw μ X).map (prefixSplitEquiv r) := by
  set φ := (prefixSplitEquiv (α := ℕ) r).symm (k, fun n => c + n) with hφdef
  have hφ : StrictMono φ := strictMono_prefixSplitEquiv_symm_block_future hk hkc
  have hsplit : Measurable (prefixSplitEquiv (α := α) r) := (prefixSplitEquiv r).measurable
  have hreindex : μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X :=
    hX.map_reindex_pathLaw_eq hX_ae hφ
  have hcomp : ⇑(prefixSplitEquiv (α := α) r) ∘ (fun ω (i : ℕ) => X (φ i) ω)
      = fun ω => (fun i : Fin r => X (k i) ω, fun n => X (c + n) ω) := by
    funext ω
    rw [Function.comp_apply, prefixSplitEquiv_apply]
    refine Prod.ext ?_ ?_
    · funext i
      simp only [hφdef, prefixSplitEquiv_symm_apply, dite_eq_left i.isLt, Fin.eta]
    · funext n
      have hnr : ¬ (r + n < r) := by omega
      simp only [hφdef, prefixSplitEquiv_symm_apply, dite_eq_right hnr]
      congr 1
      omega
  rw [← hcomp, ← AEMeasurable.map_map_of_aemeasurable hsplit.aemeasurable
    (aemeasurable_pi_lambda _ fun i => hX_ae (φ i)), hreindex]

/-- **Future-conditioned selection invariance for finite blocks.** Two strictly monotone selections
of the same length, both lying below a cutoff `c`, have the same conditional law given the future
`tailFamily X c`. -/
theorem Contractable.condExp_block_comp_future_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r c : ℕ} {k l : Fin r → ℕ} (hk : StrictMono k) (hl : StrictMono l)
    (hkc : ∀ i, k i < c) (hlc : ∀ i, l i < c)
    {f : (Fin r → α) → ℝ} (hf : Measurable f) :
    μ[fun ω => f (fun i => X (k i) ω) | tailFamily X c]
      =ᵐ[μ] μ[fun ω => f (fun i => X (l i) ω) | tailFamily X c] := by
  have hX_ae : ∀ n, AEMeasurable (X n) μ := fun n => (hX_meas n).aemeasurable
  have hpair : μ.map (fun ω => ((fun i : Fin r => X (k i) ω), fun n => X (c + n) ω))
      = μ.map (fun ω => ((fun i : Fin r => X (l i) ω), fun n => X (c + n) ω)) := by
    rw [map_block_future_eq_pathLaw_map hX hX_ae hk hkc,
      map_block_future_eq_pathLaw_map hX hX_ae hl hlc]
  rw [tailFamily_eq_comap_shift X c]
  exact TauCeti.MeasureTheory.condExp_comp_ae_eq_of_pair_law_eq
    (fun ω i => X (k i) ω) (fun ω i => X (l i) ω) (fun ω n => X (c + n) ω)
    (measurable_pi_lambda _ fun i => hX_meas (k i))
    (measurable_pi_lambda _ fun i => hX_meas (l i))
    (measurable_pi_lambda _ fun n => hX_meas (c + n)) hpair hf

/-- **Tail-conditioned selection invariance for finite blocks.** For a contractable process, any
two *strictly monotone* selections of the same length have the same conditional law given the
process tail.

The mechanism is distributional, not pointwise: nothing here asserts that a tail event is invariant
under reindexing — it is not. -/
theorem Contractable.condExp_block_comp_tailProcess_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {k l : Fin r → ℕ} (hk : StrictMono k) (hl : StrictMono l)
    {f : (Fin r → α) → ℝ} (hf : Measurable f) :
    μ[fun ω => f (fun i => X (k i) ω) | tailProcess X]
      =ᵐ[μ] μ[fun ω => f (fun i => X (l i) ω) | tailProcess X] := by
  set c := max (Finset.univ.sup fun i => k i) (Finset.univ.sup fun i => l i) + 1 with hc
  have hkc : ∀ i, k i < c := fun i => by
    have := Finset.le_sup (f := fun i => k i) (Finset.mem_univ i)
    have := le_max_left (Finset.univ.sup fun i => k i) (Finset.univ.sup fun i => l i)
    omega
  have hlc : ∀ i, l i < c := fun i => by
    have := Finset.le_sup (f := fun i => l i) (Finset.mem_univ i)
    have := le_max_right (Finset.univ.sup fun i => k i) (Finset.univ.sup fun i => l i)
    omega
  have hfut := hX.condExp_block_comp_future_ae_eq hX_meas hk hl hkc hlc hf
  have htail_le : tailProcess X ≤ tailFamily X c := tailProcess_le_tailFamily X _
  have hfam_le : tailFamily X c ≤ (inferInstance : MeasurableSpace Ω) :=
    tailFamily_le_ambient c fun i _ => hX_meas i
  have htower : ∀ g : Ω → ℝ,
      μ[μ[g | tailFamily X c] | tailProcess X] =ᵐ[μ] μ[g | tailProcess X] :=
    fun g => condExp_condExp_of_le htail_le hfam_le
  exact (htower _).symm.trans ((condExp_congr_ae hfut).trans (htower _))

/-- **Conditional law of head coordinates given the future.** For a contractable process and two
head indices `j, k` below a cutoff `r`, the conditional expectations of `f ∘ X j` and `f ∘ X k`
given the future σ-algebra `tailFamily X r` agree almost everywhere.

The single-coordinate case of `Contractable.condExp_block_comp_future_ae_eq`. -/
theorem Contractable.condExp_comp_future_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r j k : ℕ}
    (hj : j < r) (hk : k < r) {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (X j ω) | tailFamily X r] =ᵐ[μ] μ[fun ω => f (X k ω) | tailFamily X r] := by
  simpa using hX.condExp_block_comp_future_ae_eq hX_meas (k := fun _ : Fin 1 => j)
    (l := fun _ : Fin 1 => k) (Subsingleton.strictMono _) (Subsingleton.strictMono _)
    (fun _ => hj) (fun _ => hk)
    (f := fun x : Fin 1 → α => f (x 0)) (hf.comp (measurable_pi_apply 0))

/-- **Extreme members agree on the tail.** For a contractable process and arbitrary coordinates
`j, k`, the conditional expectations of `f ∘ X j` and `f ∘ X k` given the process tail σ-algebra
`tailProcess X` agree almost everywhere.

The single-coordinate case of `Contractable.condExp_block_comp_tailProcess_ae_eq`: a one-element
selection is vacuously strictly monotone. -/
theorem Contractable.condExp_comp_tailProcess_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {j k : ℕ}
    {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (X j ω) | tailProcess X] =ᵐ[μ] μ[fun ω => f (X k ω) | tailProcess X] := by
  simpa using hX.condExp_block_comp_tailProcess_ae_eq hX_meas (k := fun _ : Fin 1 => j)
    (l := fun _ : Fin 1 => k) (Subsingleton.strictMono _) (Subsingleton.strictMono _)
    (f := fun x : Fin 1 → α => f (x 0)) (hf.comp (measurable_pi_apply 0))

end Probability

end TauCeti
