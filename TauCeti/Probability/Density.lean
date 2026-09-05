/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.HasLaw

/-!
# Densities from laws presented as `withDensity`

Two bridges from a law given as `μ.withDensity f` to Mathlib's `MeasureTheory.HasPDF` and `pdf`,
together with two bridges for a law presented by a nonnegative real-valued density:
`integrable_withDensity_ofReal_iff` reduces integrability under such a law to integrability of the
density-weighted function against the reference measure, and `measureReal_withDensity_ofReal`
computes the real mass of a measurable set as the integral of the density over it.

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
* `integrable_withDensity_ofReal_iff` — under a law `μ.withDensity (ENNReal.ofReal ∘ f)`, a
  function is integrable iff `f`-weighted against the reference measure it is;
* `measureReal_withDensity_ofReal` — the real mass of a measurable set on which the density `f` is
  nonnegative and integrable is its integral over that set.

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

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {g : α → F} {ρ : α → ℝ} {s : Set α}

/-- Under a law presented by a real-valued density `ρ`, a function is integrable iff its scalar
product with `ρ` is integrable against the reference measure. The density need only be nonnegative
a.e.; the `ℝ≥0∞`-valued density used in the presentation is its `ENNReal.ofReal` lift. -/
theorem integrable_withDensity_ofReal_iff (hρ : AEMeasurable ρ μ) (hnn : 0 ≤ᵐ[μ] ρ) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔
      Integrable (fun x => ρ x • g x) μ := by
  have hlt : ∀ᵐ x ∂μ, ENNReal.ofReal (ρ x) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul₀' hρ.ennreal_ofReal hlt]
  refine integrable_congr ?_
  filter_upwards [hnn] with x hx
  rw [ENNReal.toReal_ofReal hx]

/-- Integrating a density that is nonnegative and integrable on `s` computes the real mass of `s`
under the law presented by that density. The nonnegativity hypothesis is only local to `s`. -/
theorem measureReal_withDensity_ofReal (hnn : 0 ≤ᵐ[μ.restrict s] ρ)
    (hs : MeasurableSet s) (hint : IntegrableOn ρ s μ) :
    (μ.withDensity (fun x => ENNReal.ofReal (ρ x))).real s = ∫ x in s, ρ x ∂μ := by
  rw [measureReal_def, withDensity_apply _ hs,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn)

end RealDensity

end Probability

end TauCeti
