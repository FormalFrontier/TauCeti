/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.DeFinetti.DirectingMeasure.Integral
public import TauCeti.Probability.Exchangeability.Cylinder
public import TauCeti.Probability.Process.Tail.Basic

/-!
# The mass of a directing-measure event met with a block cylinder

One lemma, the integration step shared by every de Finetti route:

```text
μ ((ν ⁻¹' S) ∩ blockCylinder X k B) = ∫⁻ ω in ν ⁻¹' S, ∏ i, directingMeasure μ X ω (B i) ∂μ
```

given the conditional factorization of the block along `k`. That factorization is a **hypothesis**,
not a conclusion: this file proves none of it, and so depends on no route that establishes it. Each
route supplies its own — the martingale route from `TailFactorization`, the `L²` route from
`ViaL2/BlockFactorization.lean` — and both then instantiate this lemma.

That is the whole point of stating it this way. The routes are required to stay independent at the
level of imports, so the shared material has to be the part that *neither* proves: here, the
bookkeeping that turns an a.e. identity of conditional expectations into an identity of measures.

The argument is three steps. A directing-measure event is tail-measurable, so testing the
factorization against it is `setIntegral_condExp`. The cylinder's mass is the integral of its
indicator, which is `integral_blockIndicatorProd` read against the restricted measure. And the
conversion to `ℝ≥0∞` happens once, at the end, via
`ofReal_integral_eq_lintegral_prod_directingMeasure`.

The result feeds `conditionallyIIDWith_of_measure_inter_blockCylinder_eq_setLIntegral`, whose
`hcore` hypothesis it is in exactly this shape.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **The mass of a directing-measure event met with a block cylinder**, given the conditional
factorization of that block along `k`.

The factorization is a hypothesis, so this lemma is neutral between the routes that establish it.
Note that neither `Contractable μ X` nor `[StandardBorelSpace Ω]` appears: both are needed only to
*produce* `hfac`, never to integrate it. -/
theorem measure_inter_blockCylinder_eq_setLIntegral_of_condExp [StandardBorelSpace α] [Nonempty α]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → α} (hX_meas : ∀ n, Measurable (X n))
    {r : ℕ} {k : Fin r → ℕ} {B : Fin r → Set α} (hB : ∀ i, MeasurableSet (B i))
    (hfac : μ[blockIndicatorProd X k B | tailProcess X]
      =ᵐ[μ] fun ω => ∏ i, (directingMeasure μ X ω).real (B i))
    {S : Set (ProbabilityMeasure α)} (hS : MeasurableSet S) :
    μ ((directingProbabilityMeasure μ X ⁻¹' S) ∩ blockCylinder X k B)
      = ∫⁻ ω in directingProbabilityMeasure μ X ⁻¹' S,
          ∏ i, directingMeasure μ X ω (B i) ∂μ := by
  have hTail : tailProcess X ≤ ‹MeasurableSpace Ω› :=
    tailProcess_le_ambient 0 fun j _ => hX_meas j
  have : IsFiniteMeasure (μ.trim hTail) := isFiniteMeasure_trim hTail
  set A : Set Ω := directingProbabilityMeasure μ X ⁻¹' S with hA_def
  have hA_tail : MeasurableSet[tailProcess X] A :=
    measurable_tailProcess_directingProbabilityMeasure hS
  have hA : MeasurableSet A := hTail _ hA_tail
  have hg_int : Integrable (fun ω => ∏ i, (directingMeasure μ X ω).real (B i)) μ :=
    integrable_prod_directingMeasure_real hTail hB
  have hind_int : Integrable (blockIndicatorProd X k B) μ :=
    integrable_blockIndicatorProd (fun i => (hX_meas _).aemeasurable) hB
  -- The factorization, tested against the tail event `A`.
  have hchain : ∫ ω in A, blockIndicatorProd X k B ω ∂μ
      = ∫ ω in A, ∏ i, (directingMeasure μ X ω).real (B i) ∂μ := by
    rw [← setIntegral_condExp hTail hind_int hA_tail]
    exact setIntegral_congr_ae hA (hfac.mono fun ω hω _ => hω)
  -- The left side is the real mass of the intersection, via the block-indicator integral read
  -- against the restricted measure.
  have hleft : ∫ ω in A, blockIndicatorProd X k B ω ∂μ
      = μ.real (A ∩ blockCylinder X k B) := by
    rw [integral_blockIndicatorProd (μ := μ.restrict A) (fun i => (hX_meas _).aemeasurable) hB,
      blockLaw_blockCylinder X (fun i => (hX_meas _).aemeasurable) hB,
      Measure.restrict_apply (measurableSet_blockCylinder (fun i => hX_meas _) hB),
      Set.inter_comm, measureReal_def]
  have hne : μ (A ∩ blockCylinder X k B) ≠ ⊤ := measure_ne_top μ _
  rw [← ENNReal.ofReal_toReal hne, ← measureReal_def, ← hleft, hchain,
    ofReal_integral_eq_lintegral_prod_directingMeasure hg_int.restrict]

end Probability

end TauCeti

end
