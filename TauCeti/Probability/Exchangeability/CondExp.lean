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
same as that of any other coordinate `X k`. Two results, stated for an arbitrary measurable real
observable `f` of the state space:

* `Contractable.condExp_comp_future_ae_eq` — for heads `j, k` below a cutoff `r`, the conditional
  expectations of `f ∘ X j` and `f ∘ X k` given the future σ-algebra `tailFamily X r` agree a.e.
* `Contractable.condExp_comp_tailProcess_ae_eq` — for arbitrary coordinates `j, k`, the same
  equality conditioning on the process tail σ-algebra `tailProcess X`. The "extreme members agree on
  the tail" step.

Both are facts about contractable processes alone, so they live in the shared exchangeability
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

/-- **Conditional law of head coordinates given the future.** For a contractable process and two
head indices `j, k` below a cutoff `r`, the conditional expectations of `f ∘ X j` and `f ∘ X k`
given the future σ-algebra `tailFamily X r` agree almost everywhere. -/
theorem Contractable.condExp_comp_future_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {r j k : ℕ}
    (hj : j < r) (hk : k < r) {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (X j ω) | tailFamily X r] =ᵐ[μ] μ[fun ω => f (X k ω) | tailFamily X r] := by
  rw [tailFamily_eq_comap_shift X r]
  exact TauCeti.MeasureTheory.condExp_comp_ae_eq_of_pair_law_eq (X j) (X k)
    (fun ω n => X (r + n) ω) (hX_meas j) (hX_meas k)
    (measurable_pi_lambda _ fun n => hX_meas (r + n))
    (hX.pairLaw_eq (j := j) (k := k) (g := fun n => r + n)
      (fun n => (hX_meas n).aemeasurable) (fun a b hab => by dsimp only; omega)
      (by omega) (by omega)) hf

/-- **Extreme members agree on the tail.** For a contractable process and arbitrary coordinates
`j, k`, the conditional expectations of `f ∘ X j` and `f ∘ X k` given the process tail σ-algebra
`tailProcess X` agree almost everywhere. -/
theorem Contractable.condExp_comp_tailProcess_ae_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} (hX : Contractable μ X) (hX_meas : ∀ n, Measurable (X n)) {j k : ℕ}
    {f : α → ℝ} (hf : Measurable f) :
    μ[fun ω => f (X j ω) | tailProcess X] =ᵐ[μ] μ[fun ω => f (X k ω) | tailProcess X] := by
  -- Condition on the future from a cutoff strictly above both `j` and `k`.
  have htail_le : tailProcess X ≤ tailFamily X (max j k + 1) := tailProcess_le_tailFamily X _
  have hfam_le : tailFamily X (max j k + 1) ≤ (inferInstance : MeasurableSpace Ω) :=
    tailFamily_le_ambient (max j k + 1) fun i _ => hX_meas i
  have : IsFiniteMeasure (μ.trim hfam_le) := isFiniteMeasure_trim hfam_le
  have hfut := hX.condExp_comp_future_ae_eq (r := max j k + 1) (j := j) (k := k) hX_meas
    (by omega) (by omega) hf
  -- The tower over `tailProcess X ≤ tailFamily X (max j k + 1)` replaces the reverse martingale.
  have htower : ∀ g : Ω → ℝ,
      μ[μ[g | tailFamily X (max j k + 1)] | tailProcess X] =ᵐ[μ] μ[g | tailProcess X] :=
    fun g => condExp_condExp_of_le htail_le hfam_le
  exact (htower _).symm.trans ((condExp_congr_ae hfut).trans (htower _))

end Probability

end TauCeti
