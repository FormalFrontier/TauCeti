/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.MeasureTheory.Function.ConditionalExpectation
public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Process.Tail.Basic

/-!
# Conditional law of a contractable coordinate given the tail

For a contractable process `X`, the conditional law of a coordinate `X j` given the future is the
same as that of any other coordinate `X k`. Two results, stated for an arbitrary integrable real
observable `f` of the state space:

* `Contractable.condExp_comp_future_eq` — for heads `j, k` below a cutoff `r`, the conditional
  expectations of `f ∘ X j` and `f ∘ X k` given the future σ-algebra `tailFamily X r` agree a.e.
* `Contractable.condExp_comp_tailProcess_eq` — for arbitrary coordinates `j, k`, the same
  equality conditioning on the process tail σ-algebra `tailProcess X`. The "extreme members agree on
  the tail" step.

The indicator specializations `Contractable.condExp_indicator_future_eq` and
`Contractable.condExp_indicator_tailProcess_eq` are what the de Finetti directing-measure
construction consumes; the general form is what the `L²` route's Cesàro bridge needs.

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

/-- **Conditional law of head coordinates given the future.** For a contractable process and two
head indices `j, k` below a cutoff `r`, the conditional expectations of `f ∘ X j` and `f ∘ X k`
given the future σ-algebra `tailFamily X r` agree almost everywhere. -/
theorem Contractable.condExp_comp_future_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r j k : ℕ}
    (hj : j < r) (hk : k < r) {f : α → ℝ} (hf : Measurable f)
    (hf_int : Integrable (fun ω => f (X 0 ω)) μ) :
    μ[fun ω => f (X j ω) | tailFamily X r] =ᵐ[μ] μ[fun ω => f (X k ω) | tailFamily X r] := by
  rw [tailFamily_eq_comap_shift X r]
  exact TauCeti.MeasureTheory.condExp_comp_eq_of_pair_law_eq (X j) (X k)
    (fun ω n => X (r + n) ω) (hX_meas j) (hX_meas k)
    (measurable_pi_lambda _ fun n => hX_meas (r + n))
    (hX.pairLaw_eq (j := j) (k := k) (g := fun n => r + n)
      (fun n => (hX_meas n).aemeasurable) (fun a b hab => by dsimp only; omega)
      (by omega) (by omega)) hf
    (hX.integrable_comp (fun n => (hX_meas n).aemeasurable) hf hf_int j)

/-- **Extreme members agree on the tail.** For a contractable process and arbitrary coordinates
`j, k`, the conditional expectations of `f ∘ X j` and `f ∘ X k` given the process tail σ-algebra
`tailProcess X` agree almost everywhere. -/
theorem Contractable.condExp_comp_tailProcess_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {j k : ℕ}
    {f : α → ℝ} (hf : Measurable f) (hf_int : Integrable (fun ω => f (X 0 ω)) μ) :
    μ[fun ω => f (X j ω) | tailProcess X] =ᵐ[μ] μ[fun ω => f (X k ω) | tailProcess X] := by
  -- Condition on the future from a cutoff strictly above both `j` and `k`.
  have htail_le : tailProcess X ≤ tailFamily X (max j k + 1) := tailProcess_le_tailFamily X _
  have hfam_le : tailFamily X (max j k + 1) ≤ (inferInstance : MeasurableSpace Ω) :=
    tailFamily_le_ambient (max j k + 1) fun i _ => hX_meas i
  have : IsFiniteMeasure (μ.trim hfam_le) := isFiniteMeasure_trim hfam_le
  have hfut := hX.condExp_comp_future_eq (r := max j k + 1) (j := j) (k := k) hX_meas
    (by omega) (by omega) hf hf_int
  -- The tower over `tailProcess X ≤ tailFamily X (max j k + 1)` replaces the reverse martingale.
  have htower : ∀ g : Ω → ℝ,
      μ[μ[g | tailFamily X (max j k + 1)] | tailProcess X] =ᵐ[μ] μ[g | tailProcess X] :=
    fun g => condExp_condExp_of_le htail_le hfam_le
  exact (htower _).symm.trans ((condExp_congr_ae hfut).trans (htower _))

/-- An indicator composed with a measurable map is integrable on a finite measure space. -/
private theorem integrable_indicator_comp {μ : Measure Ω} [IsFiniteMeasure μ] {W : Ω → α}
    (hW : Measurable W) {B : Set α} (hB : MeasurableSet B) :
    Integrable (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (W ω)) μ := by
  have hrw : (fun ω => Set.indicator B (fun _ => (1 : ℝ)) (W ω))
      = (W ⁻¹' B).indicator (fun _ => (1 : ℝ)) := rfl
  rw [hrw]
  exact Integrable.indicator (integrable_const (1 : ℝ)) (hW hB)

/-- Indicator form of `Contractable.condExp_comp_future_eq`, the shape the finite-block
factorizations use. -/
theorem Contractable.condExp_indicator_future_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r j k : ℕ}
    (hj : j < r) (hk : k < r) {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X j | tailFamily X r]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailFamily X r] :=
  hX.condExp_comp_future_eq hX_meas hj hk (measurable_const.indicator hB)
    (integrable_indicator_comp (hX_meas 0) hB)

/-- Indicator form of `Contractable.condExp_comp_tailProcess_eq`, the shape the directing-measure
construction uses. -/
theorem Contractable.condExp_indicator_tailProcess_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {j k : ℕ}
    {B : Set α} (hB : MeasurableSet B) :
    μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X j | tailProcess X]
      =ᵐ[μ] μ[Set.indicator B (fun _ => (1 : ℝ)) ∘ X k | tailProcess X] :=
  hX.condExp_comp_tailProcess_eq hX_meas (measurable_const.indicator hB)
    (integrable_indicator_comp (hX_meas 0) hB)

end Probability

end TauCeti
