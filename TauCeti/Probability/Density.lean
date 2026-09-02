/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Densities from laws presented as `withDensity`

Two bridges from a law given as `μ.withDensity f` to Mathlib's `MeasureTheory.HasPDF` and `pdf`,
together with two bridges for a law presented as Lebesgue measure with a real-valued density:
`integrable_withDensity_ofReal_iff` reduces integrability under such a law to integrability of the
density-weighted function against Lebesgue measure, and `measureReal_withDensity_ofReal` computes
the real mass of a measurable set as the integral of the density over it.

Several of Mathlib's continuous scalar families can be *presented* as `withDensity` measures — some
by definition, others only away from a degenerate parameter — and so can laws Tau Ceti builds on top
of them, but none is connected to `HasPDF`. These theorems make that connection once, so no
individual family has to repeat the `hasPDF_of_map_eq_withDensity hX.aemeasurable … hX.map_eq`
plumbing, and the family files do not each re-prove the same density integral and mass identities.

The file is deliberately neutral: it mentions no particular distribution, so a module defining one
family can import it without acquiring the others.

## Main results

* `hasPDF_of_hasLaw_withDensity` — a law presented as `μ.withDensity f` gives `HasPDF`;
* `pdf_eq_of_hasLaw_withDensity` — and its density is `f`;
* `integrable_withDensity_ofReal_iff` — under a law `volume.withDensity (ENNReal.ofReal ∘ f)`, a
  function is integrable iff `f`-weighted against Lebesgue measure it is;
* `measureReal_withDensity_ofReal` — the real mass of a set on which the nonnegative density `f` is
  integrable is its integral over the set.

The density bridges are stated for an arbitrary codomain and codomain measure, since neither proof
uses anything about `ℝ` or `volume`, and both ask only for `AEMeasurable f μ`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω} {μ : Measure E}
  {X : Ω → E} {f : E → ℝ≥0∞}

/-- **The shared bridge.** A law presented as `μ.withDensity f`, with `f` a.e. measurable, gives
`HasPDF`. -/
theorem hasPDF_of_hasLaw_withDensity (hf : AEMeasurable f μ)
    (hX : HasLaw X (μ.withDensity f) P) : HasPDF X P μ :=
  hasPDF_of_map_eq_withDensity hX.aemeasurable f hf hX.map_eq

/-- The density supplied by `hasPDF_of_hasLaw_withDensity` is the one the law was presented with.

Needs `[SigmaFinite μ]` on the *codomain* measure — satisfied by `volume` — and nothing on the
source measure. -/
theorem pdf_eq_of_hasLaw_withDensity [SigmaFinite μ] (hf : AEMeasurable f μ)
    (hX : HasLaw X (μ.withDensity f) P) : pdf X P μ =ᵐ[μ] f := by
  have : HasPDF X P μ := hasPDF_of_hasLaw_withDensity hf hX
  exact (pdf.eq_of_map_eq_withDensity' f hf).mp hX.map_eq

section RealDensity

variable {g ρ : ℝ → ℝ} {s : Set ℝ}

/-- Under a law presented as Lebesgue measure with the real-valued density `ρ`, a function is
integrable iff its product with `ρ` is Lebesgue integrable. The density need only be nonnegative
a.e.; the `ℝ≥0∞`-valued density used in the presentation is its `ENNReal.ofReal` lift. -/
theorem integrable_withDensity_ofReal_iff (hρ : Measurable ρ) (hnn : 0 ≤ᵐ[volume] ρ) :
    Integrable g (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x * g x) := by
  have hlt : ∀ᵐ x : ℝ ∂volume, ENNReal.ofReal (ρ x) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal hlt]
  refine integrable_congr ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul, mul_comm]

/-- Integrating a nonnegative density that is integrable on `s` computes the real mass of `s`
under the law presented as Lebesgue measure with that density. -/
theorem measureReal_withDensity_ofReal (hnn : 0 ≤ᵐ[volume] ρ)
    (hs : MeasurableSet s) (hint : IntegrableOn ρ s) :
    (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).real s = ∫ x in s, ρ x := by
  have hnn' : 0 ≤ᵐ[volume.restrict s] ρ :=
    (ae_restrict_iff' hs).mpr (hnn.mono fun _ hx _ => hx)
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn']
  exact ENNReal.toReal_ofReal (setIntegral_nonneg_of_ae hnn)

end RealDensity

end Probability

end TauCeti
