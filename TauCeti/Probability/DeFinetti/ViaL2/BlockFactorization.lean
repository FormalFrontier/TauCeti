/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.CondExp
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.DeFinetti.DirectingMeasure.Basic
import TauCeti.Probability.DeFinetti.ViaL2.WindowProduct
import TauCeti.Probability.DeFinetti.DirectingMeasure.Integral

/-!
# The finite-block factorization, via `L²`

For a contractable process on a standard Borel state space, the conditional law of any finite
strictly monotone block, given the process tail, factorizes into the directing measure's marginals:

```text
μ[blockIndicatorProd X k B | tailProcess X] =ᵐ[μ] ∏ i, (directingMeasure μ X ·).real (B i).
```

This is the single theorem the file provides. Integrating it over a tail event is what supplies
`hcore`, the hypothesis of `conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral`,
and hence `ConditionallyIIDWith μ X (directingProbabilityMeasure μ X)`; that integration step is
separate and does not live here.

## Why this route exists

`DeFinetti/BlockFactorization.lean` proves the same factorization through the reverse martingale
convergence theorem. This file reaches it from the `L²` averaging library instead, and imports
neither that module nor `TailFactorization`, `JointRectangle` or `Martingale.Convergence` — the
point of the `viaL2` route is that the factorization does not need a martingale.

Two inputs meet, and neither knows about the other:

*Selection invariance.* `Contractable.condExp_block_comp_tailProcess_ae_eq` says the conditional
law of a block given the tail is the same for every strictly monotone selection of that length.
The tuples appearing in a product of disjoint-window block averages are exactly such selections —
factor `i` reads its own window, and the windows are ordered, so `window_lt_window` makes each
tuple strictly monotone.

*Averaging.* `prod_blockAverage_window_eq_expect` writes a product of disjoint-window block
averages as a plain average over those tuples, so conditioning it on the tail returns the single
common value. Meanwhile the same product converges in `L¹` to `∏ i, (directingMeasure ω).real (B i)`
by the disjoint-window convergence theorem in `ViaL2/WindowProduct.lean`.
A constant sequence that converges must equal its limit, which is the factorization.

## Relation to the martingale route

`DeFinetti/BlockFactorization.lean` proves
`condExp_blockIndicatorProd_prefix_ae_eq_prod_directingMeasure`, the same factorization for the
*prefix* selection, through `TailFactorization` and reverse-martingale convergence. The overlap is
intentional: the two are the corresponding steps of the two roadmap routes. Their names record the
difference in what they *say* — `_prefix_` against `_strictMono_` — rather than how they are
proved; the roadmap's `_viaL2` route suffix is reserved for the public route endpoints.

This statement is strictly stronger than the prefix form: it holds for every strictly monotone
selection, not only `i ↦ i`, and does not assume `StandardBorelSpace Ω`. So the implication does
run one way — specializing `k` to `fun i : Fin r => (i : ℕ)` turns this into the prefix statement,
and any module importing this one can derive it (its `StandardBorelSpace Ω` hypothesis then being
unused). The converse is unavailable, the prefix form being weaker.

What separate proofs buy is therefore not logical independence but independent **import closures**.
A single Lean declaration carries a single proof and a single import closure, so making this
theorem the canonical source of the prefix statement would put the `L²` averaging library beneath
the martingale route. The genuinely shared ingredients — tail-conditioned selection invariance,
directing-measure integrability, the `ℝ≥0∞` conversion — are already factored into neutral modules
that both routes import.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** — the martingale-free
  standard-Borel de Finetti route, `deFinetti_viaL2`.
* Not adapted from the pinned `cameronfreer/exchangeability` sources: the argument here is built
  from this repository's `L²` averaging library and its tail-conditioned selection invariance,
  and deliberately diverges from that development's `ViaL2` material.
-/

public section

noncomputable section

open Filter MeasureTheory

open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The product-of-indicators observable on a block is measurable. -/
private theorem measurable_prod_indicator {r : ℕ} {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    Measurable fun x : Fin r → α => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (x i) :=
  Finset.measurable_prod _ fun i _ =>
    (measurable_const.indicator (hB i)).comp (measurable_pi_apply i)

namespace Contractable

/-- **Selection invariance for indicator blocks.** The `Fin r`-indexed indicator observable is a
measurable function of the block, so `condExp_block_comp_tailProcess_ae_eq` applies to it. -/
private theorem condExp_prod_indicator_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α}
    (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r : ℕ} {k l : Fin r → ℕ}
    (hk : StrictMono k) (hl : StrictMono l) {B : Fin r → Set α}
    (hB : ∀ i, MeasurableSet (B i)) :
    μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (k i) ω) | tailProcess X]
      =ᵐ[μ] μ[fun ω => ∏ i, (B i).indicator (fun _ => (1 : ℝ)) (X (l i) ω) | tailProcess X] :=
  hX.condExp_block_comp_tailProcess_ae_eq hX_meas hk hl (measurable_prod_indicator hB)

/-- **The finite-block factorization, conditionally on the tail.** For a contractable process on a
standard Borel state space and any strictly monotone block `k`, the conditional expectation of
`∏ i, 𝟙_{B i} ∘ X (k i)` given `tailProcess X` is the product of the directing measure's
marginals. -/
theorem condExp_blockIndicatorProd_strictMono_tailProcess_ae_eq_prod_directingMeasure
    [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX : Contractable μ X)
    (hX_meas : ∀ n, Measurable (X n)) {r : ℕ} {k : Fin r → ℕ} (hk : StrictMono k)
    {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i)) :
    μ[blockIndicatorProd X k B | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (directingMeasure μ X ω).real (B i) := by
  classical
  rw [funext fun ω => blockIndicatorProd_apply X k B ω]
  have hTail : tailProcess X ≤ (inferInstance : MeasurableSpace Ω) :=
    tailProcess_le_ambient 0 fun c _ => hX_meas c
  set Y : Fin r → ℕ → Ω → ℝ := fun i c ω => (B i).indicator (fun _ => (1 : ℝ)) (X c ω) with hY
  set Z : Ω → ℝ := fun ω => ∏ i, Y i (k i) ω with hZ
  set W : Ω → ℝ := fun ω => ∏ i, (directingMeasure μ X ω).real (B i) with hW
  -- `W` is tail-measurable, so it is its own conditional expectation.
  have hW_tail : Measurable[tailProcess X] W :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_tailProcess_directingMeasure_coe (hB i)).ennreal_toReal
  have hW_int : Integrable W μ := integrable_prod_directingMeasure_real hTail hB
  have hcondW : μ[W | tailProcess X] =ᵐ[μ] W := by
    rw [condExp_of_stronglyMeasurable hTail hW_tail.stronglyMeasurable hW_int]
  -- Each indicator block is `blockIndicatorProd` along its own selection, hence integrable.
  have hblock_int : ∀ s : Fin r → ℕ, Integrable (fun ω => ∏ i, Y i (s i) ω) μ := fun s =>
    (integrable_blockIndicatorProd (fun i => (hX_meas (s i)).aemeasurable) hB).congr
      (ae_of_all _ fun ω => blockIndicatorProd_apply X s B ω)
  -- The product of disjoint-window block averages, whose conditional expectation is `μ[Z | tail]`
  -- at every length and which converges in `L¹` to `W`.
  set P : ℕ → Ω → ℝ :=
    fun n ω => ∏ i : Fin r, blockAverage (Y i) (disjointWindow (i : ℕ) n) ω with hP
  -- The product of block averages over the disjoint windows is a plain average over tuples.
  have hPsum : ∀ n, P n = ((Fintype.card (Fin r → Fin (n + 1)) : ℝ))⁻¹ •
      ∑ js : Fin r → Fin (n + 1), fun ω => ∏ i, Y i (window (n + 1) (i : ℕ) (js i : ℕ)) ω := by
    intro n
    funext ω
    have hexp := prod_blockAverage_window_eq_expect (N := n + 1) Y ω
    rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul] at hexp
    simpa [hP] using hexp
  have hP_int : ∀ n, Integrable (P n) μ := by
    intro n
    rw [hPsum n]
    exact (integrable_finsetSum' _ fun js _ => hblock_int _).smul
      (((Fintype.card (Fin r → Fin (n + 1)) : ℝ))⁻¹)
  have hconst : ∀ n, μ[P n | tailProcess X] =ᵐ[μ] μ[Z | tailProcess X] := by
    intro n
    set c : ℝ := (Fintype.card (Fin r → Fin (n + 1)) : ℝ) with hc
    have hcard : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    set G : (Fin r → Fin (n + 1)) → Ω → ℝ :=
      fun js ω => ∏ i, Y i (window (n + 1) (i : ℕ) (js i : ℕ)) ω with hG
    -- Every tuple is a strictly monotone selection, so all the terms share one conditional law.
    have hterm : ∀ js, μ[G js | tailProcess X] =ᵐ[μ] μ[Z | tailProcess X] :=
      fun js => hX.condExp_prod_indicator_ae_eq hX_meas (window_selection_strictMono js) hk hB
    have hsum : μ[∑ js, G js | tailProcess X] =ᵐ[μ] fun ω => c * μ[Z | tailProcess X] ω := by
      refine (condExp_finsetSum (fun js _ => hblock_int _) (tailProcess X)).trans ?_
      filter_upwards [(eventually_all_finset (Finset.univ : Finset (Fin r → Fin (n + 1)))).2
        fun js _ => hterm js] with ω hω
      rw [Finset.sum_apply, Finset.sum_congr rfl fun js hjs => hω js hjs]
      simp [hc, Finset.card_univ]
    calc μ[P n | tailProcess X]
        =ᵐ[μ] μ[c⁻¹ • ∑ js, G js | tailProcess X] := by rw [hPsum n]
      _ =ᵐ[μ] c⁻¹ • μ[∑ js, G js | tailProcess X] := condExp_smul _ _ _
      _ =ᵐ[μ] μ[Z | tailProcess X] := by
          filter_upwards [hsum] with ω hω
          simp only [Pi.smul_apply, hω, smul_eq_mul, inv_mul_cancel_left₀ hcard]
  -- `L¹` convergence of the same product to `W`.
  have hlim : Tendsto (fun n => ∫ ω, |P n ω - W ω| ∂μ) atTop (𝓝 0) :=
    hX.tendsto_integral_abs_prod_blockAverage_indicator_disjointWindow_sub_prod_directingMeasure
      hX_meas B hB
  -- The conditional expectation of `Z` is within `∫ |P n - W|` of `W`, for every `n`.
  have hbound : ∀ n, ∫ ω, |μ[Z | tailProcess X] ω - W ω| ∂μ ≤ ∫ ω, |P n ω - W ω| ∂μ := by
    intro n
    have hZW : μ[P n - W | tailProcess X] =ᵐ[μ] fun ω => μ[Z | tailProcess X] ω - W ω := by
      filter_upwards [condExp_sub (hP_int n) hW_int (tailProcess X), hconst n, hcondW]
        with ω h1 h2 h3
      rw [h1]
      simp only [Pi.sub_apply, h2, h3]
    calc ∫ ω, |μ[Z | tailProcess X] ω - W ω| ∂μ
        = ∫ ω, |μ[P n - W | tailProcess X] ω| ∂μ :=
          integral_congr_ae (hZW.mono fun ω hω => by simp only [hω])
      _ ≤ ∫ ω, |(P n - W) ω| ∂μ := integral_abs_condExp_le _
      _ = ∫ ω, |P n ω - W ω| ∂μ := by simp only [Pi.sub_apply]
  -- A nonnegative quantity below a sequence tending to `0` is `0`.
  have hint : Integrable (fun ω => |μ[Z | tailProcess X] ω - W ω|) μ :=
    (integrable_condExp.sub hW_int).abs
  have hzero : ∫ ω, |μ[Z | tailProcess X] ω - W ω| ∂μ = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound))
      (integral_nonneg fun _ => abs_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) hint).mp hzero
  filter_upwards [this] with ω hω
  exact sub_eq_zero.mp (abs_eq_zero.mp hω)

end Contractable

end Probability

end TauCeti

end
