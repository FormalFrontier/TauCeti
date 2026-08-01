/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Exchangeability.L2.CesaroConvergence
public import TauCeti.Probability.Process.Tail.Basic
import TauCeti.MeasureTheory.Function.BoundedMemLp
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# The L² route's directing-measure bridge

Layer 3 of the Exchangeability roadmap reaches `weighted_sums_converge_L1`: every fixed-start
Cesàro window of a bounded observable of a contractable process converges in `L¹` to a common
limit. That limit is produced as an abstract `L¹` limit, so nothing about *where it lives* comes
for free. This file identifies it: it is a version of the conditional expectation of the observable
at the initial coordinate, given the process tail σ-algebra.

This file establishes the first half of that identification — that the limit may be taken
`tailProcess X`-measurable — in `Contractable.exists_tailProcess_measurable_cesaroLimit`.

The argument is elementary. In particular it does **not** use the reverse-martingale convergence
theorem `tendsto_ae_condExp_iInf` of Layer 4, which is what distinguishes this route from the
martingale one. The window starting at `r` is `tailFamily X r`-measurable, so the `L¹` limit `a`
satisfies `μ[a | tailFamily X r] =ᵐ[μ] a` for **every** `r`, by the `L¹`-closedness lemma
`condExp_ae_eq_self_of_tendsto_integral_abs_sub`. Taking `limsup` over `r` of those conditional
expectations (`tailLimsup`) produces an honestly `tailProcess X`-measurable function still a.e.
equal to `a`: the `limsup` over `atTop` ignores any initial segment, so it is
`tailFamily X N`-measurable for every `N`, and an intersection of σ-algebras is exactly what
`tailProcess X` is. Only countably many null sets are discarded, one per start index.

The complementary half — identifying that limit with `μ[f ∘ X 0 | tailProcess X]` by sliding every
coordinate of a window down to `X 0` along contractability — is **not** proved here, and neither
Layer 3 milestone (`realObservables_determine_directing_measure`,
`directing_measure_satisfies_requirements`) is reached yet. This file supplies the prerequisite
those milestones need.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

namespace Probability

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- An `L¹` limit of `m`-measurable functions is a.e. `m`-measurable, stated as the fixed-point
form `μ[a | m] =ᵐ[μ] a`.

This is the sub-σ-algebra closedness of `L¹` in the form the tail argument needs, and it is proved
directly from the `L¹` contraction `integral_abs_condExp_le` rather than through `Lp` subspaces. -/
theorem condExp_ae_eq_self_of_tendsto_integral_abs_sub {m m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {μ : Measure Ω} [SigmaFinite (μ.trim hm)] {a : Ω → ℝ} (ha : Integrable a μ)
    {g : ℕ → Ω → ℝ} (hg_meas : ∀ n, StronglyMeasurable[m] (g n))
    (hg_int : ∀ n, Integrable (g n) μ)
    (hg : Tendsto (fun n => ∫ ω, |g n ω - a ω| ∂μ) atTop (𝓝 0)) :
    μ[a | m] =ᵐ[μ] a := by
  -- `∫ |μ[a|m] - a| ≤ 2 ∫ |g n - a|` for every `n`, so the left side is `0`.
  have hbound : ∀ n, ∫ ω, |(μ[a | m]) ω - a ω| ∂μ ≤ 2 * ∫ ω, |g n ω - a ω| ∂μ := by
    intro n
    have hgn : μ[g n | m] = g n := condExp_of_stronglyMeasurable hm (hg_meas n) (hg_int n)
    have hsub : μ[a - g n | m] =ᵐ[μ] μ[a | m] - g n := by
      filter_upwards [condExp_sub ha (hg_int n) (m := m)] with ω hω
      simpa [hgn] using hω
    have h₁ : ∫ ω, |(μ[a | m]) ω - g n ω| ∂μ ≤ ∫ ω, |a ω - g n ω| ∂μ := by
      calc ∫ ω, |(μ[a | m]) ω - g n ω| ∂μ = ∫ ω, |(μ[a - g n | m]) ω| ∂μ :=
            integral_congr_ae (by filter_upwards [hsub] with ω hω; simp [hω])
        _ ≤ ∫ ω, |(a - g n) ω| ∂μ := integral_abs_condExp_le _
        _ = ∫ ω, |a ω - g n ω| ∂μ := by simp
    have hint₁ : Integrable (fun ω => |(μ[a | m]) ω - g n ω|) μ :=
      ((integrable_condExp.sub (hg_int n)).abs)
    have hint₂ : Integrable (fun ω => |g n ω - a ω|) μ := ((hg_int n).sub ha).abs
    calc ∫ ω, |(μ[a | m]) ω - a ω| ∂μ
        ≤ ∫ ω, (|(μ[a | m]) ω - g n ω| + |g n ω - a ω|) ∂μ :=
          integral_mono (integrable_condExp.sub ha).abs (hint₁.add hint₂)
            fun ω => by simpa using abs_sub_le ((μ[a | m]) ω) (g n ω) (a ω)
      _ = ∫ ω, |(μ[a | m]) ω - g n ω| ∂μ + ∫ ω, |g n ω - a ω| ∂μ :=
          integral_add hint₁ hint₂
      _ ≤ ∫ ω, |a ω - g n ω| ∂μ + ∫ ω, |g n ω - a ω| ∂μ := by gcongr
      _ = 2 * ∫ ω, |g n ω - a ω| ∂μ := by
          rw [two_mul]
          congr 1
          exact integral_congr_ae (Eventually.of_forall fun ω => abs_sub_comm _ _)
  have hle : ∫ ω, |(μ[a | m]) ω - a ω| ∂μ ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds (by simpa using hg.const_mul 2) ?_
    exact Eventually.of_forall hbound
  have hnonneg : 0 ≤ ∫ ω, |(μ[a | m]) ω - a ω| ∂μ :=
    integral_nonneg fun ω => abs_nonneg _
  have hzero : ∫ ω, |(μ[a | m]) ω - a ω| ∂μ = 0 := le_antisymm hle hnonneg
  have := (integral_eq_zero_iff_of_nonneg (fun ω => abs_nonneg _)
    (integrable_condExp.sub ha).abs).1 hzero
  filter_upwards [this] with ω hω
  have : |(μ[a | m]) ω - a ω| = 0 := hω
  linarith [abs_eq_zero.1 this, sub_eq_zero.1 (abs_eq_zero.1 this)]

variable {α : Type*} [MeasurableSpace α]

/-- A canonical `tailProcess X`-measurable representative: the `limsup` over the start index `r` of
the conditional expectations of `a` given the future σ-algebras `tailFamily X r`.

The `limsup` is taken over `atTop`, so it ignores every initial segment of start indices; that is
what makes it measurable with respect to *every* `tailFamily X N`, and hence with respect to their
intersection `tailProcess X`. -/
def tailLimsup (μ : Measure Ω) (X : ℕ → Ω → α) (a : Ω → ℝ) (ω : Ω) : ℝ :=
  limsup (fun r => (μ[a | tailFamily X r]) ω) atTop

/-- `tailLimsup` is genuinely `tailProcess X`-measurable, not merely a.e. so. -/
theorem measurable_tailProcess_tailLimsup (μ : Measure Ω) (X : ℕ → Ω → α) (a : Ω → ℝ) :
    Measurable[tailProcess X] (tailLimsup μ X a) := by
  rw [measurable_iff_comap_le, tailProcess_eq_iInf_tailFamily, le_iInf_iff]
  intro N
  rw [← measurable_iff_comap_le]
  have hshift : tailLimsup μ X a =
      fun ω => limsup (fun r => (μ[a | tailFamily X (r + N)]) ω) atTop := by
    funext ω
    exact (Filter.limsup_nat_add (fun r => (μ[a | tailFamily X r]) ω) N).symm
  rw [hshift]
  refine Measurable.limsup fun r => ?_
  exact (stronglyMeasurable_condExp (m := tailFamily X (r + N))).measurable.mono
    (tailFamily_antitone X (Nat.le_add_left N r)) le_rfl

/-- If `a` is a.e. equal to its conditional expectation given **every** future σ-algebra, then the
`tailProcess X`-measurable representative `tailLimsup` is a.e. equal to it. Only countably many
null sets are discarded, one per start index. -/
theorem tailLimsup_ae_eq_self {μ : Measure Ω} {X : ℕ → Ω → α} {a : Ω → ℝ}
    (h : ∀ r, μ[a | tailFamily X r] =ᵐ[μ] a) :
    tailLimsup μ X a =ᵐ[μ] a := by
  filter_upwards [ae_all_iff.2 h] with ω hω
  simp only [tailLimsup, hω]
  exact limsup_const _

/-- **The Cesàro limit lives on the tail.** For a bounded measurable observable `f` of a
contractable process, the common `L¹` limit of the fixed-start Cesàro windows supplied by
`weighted_sums_converge_L1` may be taken **`tailProcess X`-measurable**.

Each fixed-start window is `tailFamily X r`-measurable, so the limit is a.e. equal to its
conditional expectation given `tailFamily X r`, for every `r`; `tailLimsup` assembles those into a
single honestly tail-measurable representative. -/
theorem Contractable.exists_tailProcess_measurable_cesaroLimit {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ i, Measurable (X i))
    {f : α → ℝ} (hf : Measurable f) (hf_bdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ a : Ω → ℝ, Measurable[tailProcess X] a ∧ MemLp a 1 μ ∧
      ∀ r : ℕ,
        Tendsto
          (fun m => ∫ ω, |blockAverage (fun i ω => f (X i ω))
            (fun j : Fin (m + 1) => r + j) ω - a ω| ∂μ)
          atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hf_bdd
  obtain ⟨a₀, -, ha₀_L1, ha₀_lim⟩ :=
    weighted_sums_converge_L1 hX (fun i => (hX_meas i).aemeasurable) hf ⟨C, hC⟩
  -- Each coordinate observable is bounded and measurable, hence integrable.
  have hint : ∀ i : ℕ, Integrable (fun ω => f (X i ω)) μ := fun i =>
    MemLp.integrable le_rfl (memLp_comp_of_bound hf (hX_meas i).aemeasurable C
      (Filter.Eventually.of_forall fun ω => hC (X i ω)) 1)
  -- A window starting at `r` is a fixed multiple of a sum of coordinates from `r` onward.
  have hwin : ∀ (r m : ℕ), blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)
      = fun ω => ((m + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin (m + 1), f (X (r + j) ω) := by
    intro r m
    funext ω
    simp [blockAverage_apply]
  have hle : ∀ r : ℕ, tailFamily X r ≤ (inferInstance : MeasurableSpace Ω) := fun r =>
    tailFamily_le_ambient r fun k _ => hX_meas k
  -- The limit is a.e. its own conditional expectation given every future σ-algebra.
  have hfix : ∀ r : ℕ, μ[a₀ | tailFamily X r] =ᵐ[μ] a₀ := by
    intro r
    refine condExp_ae_eq_self_of_tendsto_integral_abs_sub (hle r)
      (MemLp.integrable le_rfl ha₀_L1) (g := fun m =>
        blockAverage (fun i ω => f (X i ω)) (fun j : Fin (m + 1) => r + j)) ?_ ?_ (ha₀_lim r)
    · intro m
      refine Measurable.stronglyMeasurable ?_
      rw [hwin r m]
      have hterm : ∀ j : Fin (m + 1),
          Measurable[tailFamily X r] fun ω => f (X (r + (j : ℕ)) ω) := fun j =>
        hf.comp (measurable_tailFamily_of_le (Nat.le_add_right r (j : ℕ)))
      exact Measurable.const_mul
        (Finset.measurable_sum Finset.univ fun j _ => hterm j) _
    · intro m
      rw [hwin r m]
      exact Integrable.const_mul
        (integrable_finsetSum (Finset.univ : Finset (Fin (m + 1)))
          fun (j : Fin (m + 1)) _ => hint (r + (j : ℕ))) _
  refine ⟨tailLimsup μ X a₀, measurable_tailProcess_tailLimsup μ X a₀, ?_, ?_⟩
  · exact ha₀_L1.ae_eq (tailLimsup_ae_eq_self hfix).symm
  · intro r
    refine (ha₀_lim r).congr fun m => integral_congr_ae ?_
    filter_upwards [tailLimsup_ae_eq_self (μ := μ) (X := X) hfix] with ω hω
    rw [hω]

end Probability

end TauCeti
