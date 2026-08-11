/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

/-- The reindexing that reads a strictly monotone block `k` first and then the future from `c`. -/
private def blockThenFuture {r : ℕ} (k : Fin r → ℕ) (c : ℕ) : ℕ → ℕ :=
  fun n => if h : n < r then k ⟨n, h⟩ else c + (n - r)

private theorem strictMono_blockThenFuture {r c : ℕ} {k : Fin r → ℕ} (hk : StrictMono k)
    (hkc : ∀ i, k i < c) : StrictMono (blockThenFuture k c) := by
  intro a b hab
  simp only [blockThenFuture]
  by_cases ha : a < r
  · by_cases hb : b < r
    · rw [dif_pos ha, dif_pos hb]
      exact hk (by exact_mod_cast hab)
    · rw [dif_pos ha, dif_neg hb]
      exact lt_of_lt_of_le (hkc ⟨a, ha⟩) (Nat.le_add_right c _)
  · have hb : ¬ b < r := by omega
    rw [dif_neg ha, dif_neg hb]
    omega

/-- **A strictly monotone block joins a common future exactly as the path law does.** For a
contractable process, a strictly monotone selection `k` lying below a cutoff `c`, the joint law of
the block `(X (k 0), …, X (k (r-1)))` with the future `(X c, X (c+1), …)` is the path law pushed
through the split `f ↦ (f ∘ Fin.val, fun n ↦ f (r + n))`.

Two such blocks therefore have the *same* joint law with the *same* future — which is what makes a
conditional statement given that future available. Note the equality is distributional: nothing
here says a tail event is pointwise invariant under reindexing. -/
private theorem map_block_future_eq_pathLaw_map {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_ae : ∀ n, AEMeasurable (X n) μ)
    {r c : ℕ} {k : Fin r → ℕ} (hk : StrictMono k) (hkc : ∀ i, k i < c) :
    μ.map (fun ω => (fun i : Fin r => X (k i) ω, fun n => X (c + n) ω))
      = (pathLaw μ X).map
          (fun f : ℕ → α => (fun i : Fin r => f (i : ℕ), fun n => f (r + n))) := by
  classical
  set φ := blockThenFuture k c with hφdef
  have hφ : StrictMono φ := strictMono_blockThenFuture hk hkc
  have hsplit : Measurable
      (fun f : ℕ → α => (fun i : Fin r => f (i : ℕ), fun n => f (r + n))) :=
    (measurable_pi_lambda (fun (f : ℕ → α) (i : Fin r) => f (i : ℕ))
        fun i => measurable_pi_apply (i : ℕ)).prodMk
      (measurable_pi_lambda (fun (f : ℕ → α) (n : ℕ) => f (r + n))
        fun n => measurable_pi_apply (r + n))
  have hreindex : μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X :=
    hX.map_reindex_pathLaw_eq hX_ae hφ
  have hcomp : (fun f : ℕ → α => (fun i : Fin r => f (i : ℕ), fun n => f (r + n)))
      ∘ (fun ω (i : ℕ) => X (φ i) ω)
      = fun ω => (fun i : Fin r => X (k i) ω, fun n => X (c + n) ω) := by
    funext ω
    refine Prod.ext ?_ ?_
    · funext i
      simp only [Function.comp_apply, hφdef, blockThenFuture, dif_pos i.isLt, Fin.eta]
    · funext n
      have hnr : ¬ (r + n < r) := by omega
      simp only [Function.comp_apply, hφdef, blockThenFuture, dif_neg hnr]
      congr 1
      omega
  rw [← hcomp, ← AEMeasurable.map_map_of_aemeasurable hsplit.aemeasurable
    (aemeasurable_pi_lambda _ fun i => hX_ae (φ i)), hreindex]

/-- **Future-conditioned selection invariance for finite blocks.** Two strictly monotone selections
of the same length, both lying below a cutoff `c`, have the same conditional law given the future
`tailFamily X c`.

Both blocks are appended to the *same* future, and a strictly monotone block below `c` followed by
the future from `c` is a strictly increasing reindexing of `ℕ`; contractability therefore makes the
two joint laws equal, which transfers to conditional expectations. -/
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
  classical
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
  have hmono : ∀ m : ℕ, StrictMono (fun _ : Fin 1 => m) := fun m a b hab => absurd
    (Subsingleton.elim a b) (ne_of_lt hab)
  simpa using hX.condExp_block_comp_future_ae_eq hX_meas (k := fun _ : Fin 1 => j)
    (l := fun _ : Fin 1 => k) (hmono j) (hmono k) (fun _ => hj) (fun _ => hk)
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
  have hmono : ∀ m : ℕ, StrictMono (fun _ : Fin 1 => m) := fun m a b hab => absurd
    (Subsingleton.elim a b) (ne_of_lt hab)
  simpa using hX.condExp_block_comp_tailProcess_ae_eq hX_meas (k := fun _ : Fin 1 => j)
    (l := fun _ : Fin 1 => k) (hmono j) (hmono k)
    (f := fun x : Fin 1 → α => f (x 0)) (hf.comp (measurable_pi_apply 0))

end Probability

end TauCeti
