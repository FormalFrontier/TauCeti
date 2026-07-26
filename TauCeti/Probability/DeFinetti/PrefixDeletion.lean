/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift
import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Probability.Independence.Conditional
import TauCeti.Probability.Independence.Conditional
import TauCeti.Probability.Process.Tail.Basic

/-!
# Prefix-deletion conditional-expectation identity (Kallenberg 1.3 input)

For a contractable process `X`, this file proves the "prefix-deletion" conditional-expectation
identity feeding the de Finetti martingale route: for `r ≤ m` and a measurable `B`,
```
μ[𝟙_{(X r)⁻¹ B} | σ(U) ⊔ σ(W)] =ᵐ[μ] μ[𝟙_{(X r)⁻¹ B} | σ(W)],
```
where `U ω = (X 0 ω, …, X (r-1) ω)` is the length-`r` prefix and `W = processShift X (m+1)` is the
far tail from time `m+1`.  Informally, `X r` is conditionally independent of the prefix given the
far tail, so conditioning the `X r`-indicator on `σ(U) ⊔ σ(W)` collapses to conditioning on `σ(W)`.

## Main results

The public interface consists of two theorems:

* `Contractable.condIndep_coord_prefix_tail` — the primary conditional-independence statement:
  for a contractable process and `r ≤ m`, `X r` is conditionally independent of the prefix `U`
  given the far tail `W = processShift X (m+1)`, packaged as a `ProbabilityTheory.CondIndep` object.
* `Contractable.condExp_indicator_prefix_sup_tail_eq` — the prefix-deletion drop-info identity read
  off from that conditional independence: for `r ≤ m` and a measurable `B`,
  `μ[𝟙_{(X r)⁻¹ B} | σ(U) ⊔ σ(W)] =ᵐ μ[𝟙_{(X r)⁻¹ B} | σ(W)]`.

The contractability-specific pair-law equality feeding the argument is internal proof machinery,
kept `private` to this module.  The generic contraction-independence (Kallenberg 1.3) L² engine and
the conditional-independence projection step are imported from
`TauCeti.Probability.Independence.Conditional`.

Adapted from `cameronfreer/exchangeability` (`DeFinetti/ViaMartingale/PairLawEquality.lean`,
`Probability/TripleLawDropInfo/*`, `Probability/CondIndep/*`).
-/

public section

noncomputable section

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSpace γ] {μ : Measure Ω}

/-! ### The two reindexing maps -/

/-- Injection `φ₀` for contractability: indices `0,…,r-1, m+1, m+2, …` (skips `r,…,m`). -/
private def phi0 (r m : ℕ) : ℕ → ℕ := fun n => if n < r then n else n + (m - r + 1)

/-- Injection `φ₁` for contractability: indices `0,…,r, m+1, m+2, …` (skips `r+1,…,m`). -/
private def phi1 (r m : ℕ) : ℕ → ℕ := fun n => if n ≤ r then n else n + (m - r)

private lemma phi0_strictMono (r m : ℕ) : StrictMono (phi0 r m) := by
  intro i j hij
  simp only [phi0]
  by_cases hi : i < r
  · by_cases hj : j < r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j < r := fun h => hi (Nat.lt_of_lt_of_le hij (Nat.le_of_lt h))
    simp only [hj, if_false]
    omega

private lemma phi1_strictMono (r m : ℕ) : StrictMono (phi1 r m) := by
  intro i j hij
  simp only [phi1]
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ r
    · simp [hi, hj, hij]
    · simp only [hi, if_true, hj, if_false]
      omega
  · simp only [hi, if_false]
    have hj : ¬j ≤ r := fun h => hi (Nat.le_trans (Nat.le_of_lt hij) h)
    simp only [hj, if_false]
    omega

/-! ### Prefix-tail split as a measurable equivalence -/

/-- Split a sequence into its length-`r` prefix `Fin r → α` and the tail `ℕ → α` from index `r`, as
a measurable equivalence.  The forward map sends `f` to `(fun i => f i.val, fun j => f (r + j))`;
its inverse glues a prefix/tail pair back into a sequence, taking coordinates below `r` from the
prefix and the rest (reindexed by `· - r`) from the tail. -/
private def prefixSplitEquiv (r : ℕ) : (ℕ → α) ≃ᵐ (Fin r → α) × (ℕ → α) :=
  (MeasurableEquiv.arrowCongr' (finSumNatEquiv r).symm (.refl α)).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ => α)

/-- The inverse of `prefixSplitEquiv` glues a prefix/tail pair into a sequence: coordinates below
`r` come from the prefix `p.1`, the rest (reindexed by `· - r`) from the tail `p.2`. -/
private lemma prefixSplitEquiv_symm_apply (r : ℕ) (p : (Fin r → α) × (ℕ → α)) (n : ℕ) :
    (prefixSplitEquiv r).symm p n = if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
  have key : (prefixSplitEquiv r).symm p
      = fun n => if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
    apply (prefixSplitEquiv r).injective
    rw [MeasurableEquiv.apply_symm_apply]
    -- BRITTLE: uses the defeq `prefixSplitEquiv r f = (fun i => f i.val, fun j => f (r + j))`;
    -- `MeasurableEquiv.arrowCongr'` exposes no coe/apply lemma, so this cannot be a `simp` rewrite.
    change p = (fun i : Fin r => (if h : (i : ℕ) < r then p.1 ⟨i, h⟩ else p.2 ((i : ℕ) - r)),
        fun j : ℕ => if h : r + j < r then p.1 ⟨r + j, h⟩ else p.2 (r + j - r))
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [dif_pos i.isLt, Fin.eta]
    · have h : ¬ (r + j < r) := Nat.not_lt.mpr (Nat.le_add_right r j)
      simp only [dif_neg h, Nat.add_sub_cancel_left]
  rw [key]

omit [MeasurableSpace Ω] in
/-- Gluing the length-`r` prefix `i ↦ X i` onto the shifted tail `processShift X (m+1)` yields the
`phi0`-reindexing of `X` (evaluated pointwise). -/
private lemma prefixSplitEquiv_symm_apply_processShift {X : ℕ → Ω → α} {r m : ℕ} (hr : r ≤ m)
    (ω : Ω) (n : ℕ) :
    (prefixSplitEquiv r).symm ((fun i : Fin r => X i ω), processShift X (m + 1) ω) n
      = X (phi0 r m n) ω := by
  simp only [prefixSplitEquiv_symm_apply, phi0]
  by_cases hn : n < r
  · simp only [hn, dite_true, ite_true]
  · simp only [hn, dite_false, ite_false, processShift_apply]
    congr 1
    omega

omit [MeasurableSpace Ω] in
/-- Gluing the length-`r` prefix `i ↦ X i` onto the consed tail
`processCons (X r) (processShift X (m+1))` yields the `phi1`-reindexing of `X` (evaluated
pointwise). -/
private lemma prefixSplitEquiv_symm_apply_processCons {X : ℕ → Ω → α} {r m : ℕ} (hr : r ≤ m)
    (ω : Ω) (n : ℕ) :
    (prefixSplitEquiv r).symm ((fun i : Fin r => X i ω),
        processCons (fun ω => X r ω) (processShift X (m + 1)) ω) n = X (phi1 r m n) ω := by
  simp only [prefixSplitEquiv_symm_apply, phi1]
  by_cases hn : n < r
  · have hle : n ≤ r := Nat.le_of_lt hn
    simp only [hn, dite_true, hle, ite_true]
  · simp only [hn, dite_false]
    by_cases hn' : n = r
    · subst hn'
      simp only [Nat.sub_self, le_refl, ite_true, processCons_zero]
    · have hgt : r < n := Nat.lt_of_le_of_ne (Nat.not_lt.mp hn) (Ne.symm hn')
      simp only [Nat.not_le.mpr hgt, ite_false]
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
      subst hk
      have h_idx : r + k + 1 - r = k + 1 := by omega
      rw [h_idx]
      simp only [processCons_succ, processShift_apply]
      congr 1
      omega

/-! ### Pair-law equality from contractability -/

/-- **Pair-law equality from contractability:** `(U, W) =ᵈ (U, W')`, where `U` is the length-`r`
prefix, `W = processShift X (m+1)` is the far tail, and `W' = processCons (X r) W`.  Both pairs
arise from strictly increasing reindexings (`phi0`, `phi1`) of the same contractable process, so
they have the same law. -/
private lemma pair_law_eq_of_contractable [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX : ∀ n, Measurable (X n))
    (r m : ℕ) (hr : r ≤ m) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    let W' := processCons (fun ω => X r ω) W
    Measure.map (fun ω => (U ω, W ω)) μ =
    Measure.map (fun ω => (U ω, W' ω)) μ := by
  intro U W W'
  have hX_ae : ∀ i, AEMeasurable (X i) μ := fun i => (hX i).aemeasurable
  -- Reindexing a contractable process by a strictly increasing map preserves the path law.
  have hreindex : ∀ φ : ℕ → ℕ, StrictMono φ →
      μ.map (fun ω (i : ℕ) => X (φ i) ω) = pathLaw μ X := by
    intro φ hφ
    calc μ.map (fun ω (i : ℕ) => X (φ i) ω)
        = (pathLaw μ X).map (fun x : ℕ → α => fun i => x (φ i)) :=
          (map_reindex_pathLaw μ hX_ae φ).symm
      _ = pathLaw μ X := (hContr.measurePreserving_reindex hX_ae hφ).map_eq
  -- Measurability of the building blocks.
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX (m + 1 + n)
  have hW'_meas : Measurable W' :=
    measurable_processCons (hX r) fun n => (measurable_pi_apply n).comp hW_meas
  -- The two glued sequences are the `phi0`/`phi1`-reindexings of `X`, hence share `pathLaw μ X`.
  let seq0 : Ω → ℕ → α := fun ω => (prefixSplitEquiv r).symm (U ω, W ω)
  let seq1 : Ω → ℕ → α := fun ω => (prefixSplitEquiv r).symm (U ω, W' ω)
  have hseq0_meas : Measurable seq0 :=
    (prefixSplitEquiv r).symm.measurable.comp (hU_meas.prodMk hW_meas)
  have hseq1_meas : Measurable seq1 :=
    (prefixSplitEquiv r).symm.measurable.comp (hU_meas.prodMk hW'_meas)
  have hseq0_eq : seq0 = fun ω (i : ℕ) => X (phi0 r m i) ω :=
    funext fun ω => funext fun n => prefixSplitEquiv_symm_apply_processShift hr ω n
  have hseq1_eq : seq1 = fun ω (i : ℕ) => X (phi1 r m i) ω :=
    funext fun ω => funext fun n => prefixSplitEquiv_symm_apply_processCons hr ω n
  have h_seq_eq : Measure.map seq0 μ = Measure.map seq1 μ := by
    rw [hseq0_eq, hseq1_eq, hreindex (phi0 r m) (phi0_strictMono r m),
      hreindex (phi1 r m) (phi1_strictMono r m)]
  -- Pull back via `prefixSplitEquiv`, whose forward map reassembles the split sequences.
  have h0 : Measure.map (fun ω => (U ω, W ω)) μ = Measure.map (⇑(prefixSplitEquiv r) ∘ seq0) μ :=
    congrArg (Measure.map · μ) <|
      funext fun ω => ((prefixSplitEquiv r).apply_symm_apply (U ω, W ω)).symm
  have h1 : Measure.map (fun ω => (U ω, W' ω)) μ = Measure.map (⇑(prefixSplitEquiv r) ∘ seq1) μ :=
    congrArg (Measure.map · μ) <|
      funext fun ω => ((prefixSplitEquiv r).apply_symm_apply (U ω, W' ω)).symm
  rw [h0, h1, ← Measure.map_map (prefixSplitEquiv r).measurable hseq0_meas,
    ← Measure.map_map (prefixSplitEquiv r).measurable hseq1_meas, h_seq_eq]

/-- **Drop-info for the prefix `U`.** For a contractable process and `r ≤ m`, conditioning the
indicator of the prefix `U` on `σ(W') = σ(X r) ⊔ σ(W)` equals conditioning on `σ(W)`; here
`W = processShift X (m+1)` and `W' = processCons (X r) W`. -/
private lemma condExp_indicator_eq_of_contractable [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) {A : Set (Fin r → α)} (hA : MeasurableSet A) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    let W' := processCons (fun ω => X r ω) W
    μ[(U ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W' inferInstance]
      =ᵐ[μ]
    μ[(U ⁻¹' A).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  intro U W W'
  have hU : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hW' : Measurable W' :=
    measurable_processCons (hX_meas r) fun n => (measurable_pi_apply n).comp hW
  exact condExp_indicator_eq_of_law_eq_of_comap_le U W W' hU hW hW'
    (pair_law_eq_of_contractable hContr hX_meas r m hrm)
    (comap_le_comap_processCons (fun ω => X r ω) W) hA

/-! ### Conditional independence and the prefix-deletion identity (main target) -/

/-- **Prefix/tail conditional independence.** For a contractable process and `r ≤ m`, the value
`X r` is conditionally independent of the length-`r` prefix `U` given the far tail
`W = processShift X (m+1)`, packaged as Mathlib's `ProbabilityTheory.CondIndep` object.  This is the
primary result; the prefix-deletion drop-info identity is read off from it below. -/
theorem Contractable.condIndep_coord_prefix_tail [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) :
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    CondIndep (MeasurableSpace.comap W inferInstance)
      (MeasurableSpace.comap (X r) inferInstance) (MeasurableSpace.comap U inferInstance)
      (measurable_processShift fun n => hX_meas (m + 1 + n)).comap_le μ := by
  intro U W
  let W' : Ω → ℕ → α := processCons (X r) W
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hmU : MeasurableSpace.comap U inferInstance ≤ ‹MeasurableSpace Ω› := hU_meas.comap_le
  have hmW : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› := hW_meas.comap_le
  have hmXr : MeasurableSpace.comap (X r) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hX_meas r).comap_le
  -- `σ(W') = σ(X r) ⊔ σ(W)`, since `W'` conses `X r` onto the far tail `W`.
  have h_sup : MeasurableSpace.comap W' inferInstance
      = MeasurableSpace.comap (X r) inferInstance ⊔ MeasurableSpace.comap W inferInstance :=
    comap_processCons_eq_sup (X r) W
  -- Drop-`X r` form: conditioning a prefix indicator on `σ(X r) ⊔ σ(W)` collapses to `σ(W)`,
  -- supplied by the private drop-info wrapper `condExp_indicator_eq_of_contractable`.
  have h_drop : ∀ H, MeasurableSet[MeasurableSpace.comap U inferInstance] H →
      μ[H.indicator (fun _ => (1 : ℝ))
          | MeasurableSpace.comap (X r) inferInstance ⊔ MeasurableSpace.comap W inferInstance]
        =ᵐ[μ]
      μ[H.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
    rintro H ⟨A, hA, rfl⟩
    have h := condExp_indicator_eq_of_contractable hContr hX_meas hrm hA
    rw [← h_sup]
    exact h
  -- `CondIndep σ(W) σ(X r) σ(U)`: `X r` and the prefix `U` are independent given the far tail.
  exact condIndep_of_indicator_condExp_eq hmXr hmW hmU h_drop

/-- **Prefix-deletion conditional-expectation identity.** For a contractable process and `r ≤ m`,
conditioning the indicator of `X r` on `σ(U) ⊔ σ(W)` equals conditioning on `σ(W)`, where `U` is the
length-`r` prefix and `W = processShift X (m+1)` is the far tail.  This is read off from the
prefix/tail conditional independence `Contractable.condIndep_coord_prefix_tail`. -/
theorem Contractable.condExp_indicator_prefix_sup_tail_eq [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hContr : Contractable μ X) (hX_meas : ∀ n, Measurable (X n))
    {r m : ℕ} (hrm : r ≤ m) {B : Set α} (hB : MeasurableSet B) :
    let Y := X r
    let U := fun ω : Ω => (fun i : Fin r => X i ω)
    let W := processShift X (m + 1)
    μ[(Y ⁻¹' B).indicator (fun _ => (1 : ℝ))
       | MeasurableSpace.comap U inferInstance ⊔ MeasurableSpace.comap W inferInstance]
      =ᵐ[μ]
    μ[(Y ⁻¹' B).indicator (fun _ => (1 : ℝ)) | MeasurableSpace.comap W inferInstance] := by
  intro Y U W
  have hU_meas : Measurable U := measurable_pi_lambda _ fun i => hX_meas i.val
  have hW_meas : Measurable W := measurable_processShift fun n => hX_meas (m + 1 + n)
  have hmU : MeasurableSpace.comap U inferInstance ≤ ‹MeasurableSpace Ω› := hU_meas.comap_le
  have hmW : MeasurableSpace.comap W inferInstance ≤ ‹MeasurableSpace Ω› := hW_meas.comap_le
  have hmXr : MeasurableSpace.comap (X r) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hX_meas r).comap_le
  -- Symmetrise `CondIndep σ(W) σ(X r) σ(U)` to `CondIndep σ(W) σ(U) σ(X r)` and project.
  exact condExp_indicator_sup_eq_of_condIndep hmU hmW hmXr
    (Contractable.condIndep_coord_prefix_tail hContr hX_meas hrm).symm ⟨B, hB, rfl⟩

end Probability

end TauCeti
