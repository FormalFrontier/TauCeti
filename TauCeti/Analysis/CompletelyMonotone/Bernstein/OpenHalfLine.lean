/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
-- Non-public: Bernstein's existence theorem supplies the representing measures of the positive
-- shifts, and the improper-integral calculus evaluates the reciprocal example.
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem

/-!
# The Hausdorff--Bernstein--Widder theorem on the open half-line

A function completely monotone on the *open* half-line `(0, ∞)` is the Laplace transform of a
unique positive measure on `ℝ≥0`, and that measure need not be finite: the reciprocal
`t ↦ 1 / t` is completely monotone on `(0, ∞)` and is represented by Lebesgue measure. The
finite-measure statement, `TauCeti.hausdorff_bernstein_widder`, is the strictly stronger
conclusion drawn from the strictly stronger hypothesis of continuity up to the boundary point
`0`; this file records what survives when that boundary hypothesis is dropped.

The representation predicate is `TauCeti.RepresentsLaplaceOnIoi`, which replaces the finiteness
clause of `TauCeti.RepresentsLaplace` by integrability of the exponential kernel at every
positive parameter -- exactly what makes the transform a genuine Bochner integral rather than the
junk value of a non-integrable one.

The proof is an exponential-tilt bookkeeping argument on top of Bernstein's theorem. For each
`a > 0` the shift `t ↦ f (t + a)` is completely monotone on the closed half-line, so it has a
finite representing measure `σ a`; the tilted measures `e^{a p} · σ a` are then all equal, and
their common value is the representing measure of `f` itself. Uniqueness runs the tilt backwards:
tilting by `e^{-p}` turns any representing measure into a finite one, where the Laplace transform
is already known to determine the measure.

## Main declarations

* `TauCeti.RepresentsLaplaceOnIoi`: a possibly infinite measure represents a function by its
  Laplace transform on `(0, ∞)`.
* `TauCeti.RepresentsLaplace.representsLaplaceOnIoi`: the finite-measure predicate is stronger.
* `TauCeti.RepresentsLaplaceOnIoi.isCompletelyMonotoneOnIoi`: the easy direction.
* `TauCeti.RepresentsLaplaceOnIoi.unique`: at most one measure represents a given function.
* `TauCeti.exists_representsLaplaceOnIoi_of_isCompletelyMonotoneOnIoi`: the existence half.
* `TauCeti.hausdorff_bernstein_widder_onIoi`,
  `TauCeti.hausdorff_bernstein_widder_onIoi_existsUnique`: the headline equivalence.
* `TauCeti.representsLaplaceOnIoi_one_div`, `TauCeti.isCompletelyMonotoneOnIoi_one_div`, and
  `TauCeti.measure_univ_map_toNNReal_volume_restrict_Ioi`: the reciprocal `t ↦ 1 / t`, its
  representing measure, and the fact that this measure is infinite.

## References

D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV, Theorem 12a; see also
R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012),
Theorem 1.4 and its remark on the open half-line.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B: the warning attached to the
  Bernstein milestone asks for the open-half-line representation by a possibly infinite measure,
  with `1 / t = ∫₀^∞ e^{-tx} dx` as its example.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

variable {f : ℝ → ℝ} {μ ν : Measure ℝ≥0}

/-! ## Exponential tilts of measures on `ℝ≥0`

Tilting a measure by the density `p ↦ e^{a p}` shifts its Laplace transform by `a`. This is the
only device the proofs below need, so it stays private to this file.
-/

/-- The exponential density `p ↦ e^{a p}` on `ℝ≥0`, valued in `ℝ≥0`. -/
private noncomputable def expWeight (a : ℝ) (p : ℝ≥0) : ℝ≥0 :=
  (Real.exp (a * (p : ℝ))).toNNReal

/-- The exponential density, read back as a real number. -/
private lemma expWeight_coe (a : ℝ) (p : ℝ≥0) :
    ((expWeight a p : ℝ≥0) : ℝ) = Real.exp (a * (p : ℝ)) :=
  Real.coe_toNNReal _ (Real.exp_pos _).le

/-- The exponential density is measurable. -/
private lemma measurable_expWeight (a : ℝ) : Measurable (expWeight a) :=
  (continuous_real_toNNReal.comp (by fun_prop)).measurable

/-- Exponential densities multiply by adding their exponents. -/
private lemma expWeight_mul (a b : ℝ) (p : ℝ≥0) :
    expWeight a p * expWeight b p = expWeight (a + b) p := by
  refine NNReal.coe_injective ?_
  push_cast [expWeight_coe]
  rw [← Real.exp_add]
  ring_nf

/-- The measure `μ` tilted by the exponential density `p ↦ e^{a p}`. -/
private noncomputable def expTilt (a : ℝ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  μ.withDensity fun p => (expWeight a p : ℝ≥0∞)

/-- Tilting by the exponent `0` does nothing. -/
private lemma expTilt_zero (μ : Measure ℝ≥0) : expTilt 0 μ = μ := by
  have h : (fun p : ℝ≥0 => ((expWeight 0 p : ℝ≥0) : ℝ≥0∞)) = 1 := by
    funext p
    simp [expWeight]
  rw [expTilt, h, withDensity_one]

/-- Successive tilts add their exponents. -/
private lemma expTilt_expTilt (a b : ℝ) (μ : Measure ℝ≥0) :
    expTilt b (expTilt a μ) = expTilt (a + b) μ := by
  rw [expTilt, expTilt, expTilt,
    ← withDensity_mul _ (measurable_expWeight a).coe_nnreal_ennreal
      (measurable_expWeight b).coe_nnreal_ennreal]
  congr 1
  funext p
  rw [Pi.mul_apply, ← ENNReal.coe_mul, expWeight_mul]

/-- Integrating against a tilt is integrating against the tilted integrand. -/
private lemma integral_expTilt (a : ℝ) (μ : Measure ℝ≥0) (g : ℝ≥0 → ℝ) :
    ∫ p, g p ∂(expTilt a μ) = ∫ p, Real.exp (a * (p : ℝ)) * g p ∂μ := by
  rw [expTilt, integral_withDensity_eq_integral_smul (measurable_expWeight a)]
  simp only [NNReal.smul_def, expWeight_coe, smul_eq_mul]

/-- Integrability against a tilt is integrability of the tilted integrand. -/
private lemma integrable_expTilt_iff (a : ℝ) (μ : Measure ℝ≥0) (g : ℝ≥0 → ℝ) :
    Integrable g (expTilt a μ) ↔ Integrable (fun p : ℝ≥0 => Real.exp (a * (p : ℝ)) * g p) μ := by
  rw [expTilt, integrable_withDensity_iff_integrable_smul (measurable_expWeight a)]
  simp only [NNReal.smul_def, expWeight_coe, smul_eq_mul]

/-- The tilt absorbs into the exponential kernel by shifting its parameter. -/
private lemma exp_mul_exp_neg_mul (a t : ℝ) (p : ℝ≥0) :
    Real.exp (a * (p : ℝ)) * Real.exp (-(t * (p : ℝ))) = Real.exp (-((t - a) * (p : ℝ))) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- Tilting by `e^{a p}` translates the Laplace transform by `a`. -/
private lemma laplaceTransform_expTilt (a t : ℝ) (μ : Measure ℝ≥0) :
    laplaceTransform (expTilt a μ) t = laplaceTransform μ (t - a) := by
  rw [laplaceTransform_apply, laplaceTransform_apply, integral_expTilt]
  simp only [exp_mul_exp_neg_mul]

/-- The exponential kernel is integrable against a tilt exactly when the translated kernel is
integrable against the original measure. -/
private lemma integrable_exp_neg_mul_expTilt_iff (a t : ℝ) (μ : Measure ℝ≥0) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) (expTilt a μ) ↔
      Integrable (fun p : ℝ≥0 => Real.exp (-((t - a) * (p : ℝ)))) μ := by
  rw [integrable_expTilt_iff]
  simp only [exp_mul_exp_neg_mul]

/-- A tilt by a nonpositive exponent has density at most `1`, so it preserves finiteness. -/
private lemma isFiniteMeasure_expTilt_of_nonpos (μ : Measure ℝ≥0) [IsFiniteMeasure μ] {a : ℝ}
    (ha : a ≤ 0) : IsFiniteMeasure (expTilt a μ) := by
  have hint : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) (expTilt a μ) := by
    rw [integrable_expTilt_iff]
    simpa using integrable_exp_neg_mul μ (x := -a) (neg_nonneg.mpr ha)
  rcases integrable_const_iff.mp hint with h | h
  · exact absurd h one_ne_zero
  · exact h

/-! ## The open-half-line representation predicate -/

/-- A positive measure on `ℝ≥0` **represents `f` by its Laplace transform on `(0, ∞)`** if the
exponential kernel `p ↦ e^{-tp}` is integrable against it for every `t > 0` and the resulting
transform agrees with `f` there.

The measure is *not* required to be finite: that is the whole point of the open-half-line
statement, and the integrability clause is what takes over the role finiteness plays in
`TauCeti.RepresentsLaplace`. -/
def RepresentsLaplaceOnIoi (μ : Measure ℝ≥0) (f : ℝ → ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) ∧
    ∀ t : ℝ, 0 < t → f t = laplaceTransform μ t

/-- `RepresentsLaplaceOnIoi μ f` unfolds to integrability of the exponential kernel at every
positive parameter together with equality with the Laplace transform there. -/
lemma representsLaplaceOnIoi_iff :
    RepresentsLaplaceOnIoi μ f ↔
      (∀ t : ℝ, 0 < t → Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ) ∧
        ∀ t : ℝ, 0 < t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplaceOnIoi

/-- The exponential kernel is integrable against a representing measure at positive
parameters. -/
lemma integrable (h : RepresentsLaplaceOnIoi μ f) {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : ℝ≥0 => Real.exp (-(t * (p : ℝ)))) μ := h.1 t ht

/-- A representing measure has the advertised Laplace-transform values on `(0, ∞)`. -/
lemma eq_laplaceTransform (h : RepresentsLaplaceOnIoi μ f) {t : ℝ} (ht : 0 < t) :
    f t = laplaceTransform μ t := h.2 t ht

/-- A representation transports along agreement on the positive half-line: the predicate
constrains `f` only there. -/
protected lemma congr {g : ℝ → ℝ} (hf : RepresentsLaplaceOnIoi μ f) (h : EqOn g f (Ioi 0)) :
    RepresentsLaplaceOnIoi μ g :=
  ⟨hf.1, fun _ ht => (h (mem_Ioi.mpr ht)).trans (hf.eq_laplaceTransform ht)⟩

/-- **Easy direction**: a represented function is completely monotone on `(0, ∞)`. -/
lemma isCompletelyMonotoneOnIoi (h : RepresentsLaplaceOnIoi μ f) :
    IsCompletelyMonotoneOnIoi f :=
  (isCompletelyMonotoneOnIoi_laplaceTransform μ h.1).congr fun _ ht => h.eq_laplaceTransform ht

end RepresentsLaplaceOnIoi

/-- A finite representing measure represents on the open half-line as well: the finiteness
clause supplies the integrability clause, and `(0, ∞) ⊆ [0, ∞)`. -/
lemma RepresentsLaplace.representsLaplaceOnIoi (h : RepresentsLaplace μ f) :
    RepresentsLaplaceOnIoi μ f := by
  have := h.isFiniteMeasure
  exact ⟨fun _ ht => integrable_exp_neg_mul μ ht.le, fun _ ht => h.eq_laplaceTransform ht.le⟩

/-! ## Uniqueness -/

/-- Tilting a representing measure by `e^{-p}` produces a finite measure. -/
private lemma isFiniteMeasure_expTilt_neg_one (h : RepresentsLaplaceOnIoi μ f) :
    IsFiniteMeasure (expTilt (-1) μ) := by
  have hint : Integrable (fun _ : ℝ≥0 => (1 : ℝ)) (expTilt (-1) μ) := by
    rw [integrable_expTilt_iff]
    simpa using h.integrable one_pos
  rcases integrable_const_iff.mp hint with h' | h'
  · exact absurd h' one_ne_zero
  · exact h'

/-- **A function has at most one open-half-line representing measure.** Tilting by `e^{-p}`
reduces the statement to the finite-measure uniqueness theorem
`TauCeti.Measure.ext_of_forall_laplaceTransform_natCast_eq`. -/
protected lemma RepresentsLaplaceOnIoi.unique
    (hμ : RepresentsLaplaceOnIoi μ f) (hν : RepresentsLaplaceOnIoi ν f) : μ = ν := by
  have _ := isFiniteMeasure_expTilt_neg_one hμ
  have _ := isFiniteMeasure_expTilt_neg_one hν
  have hkey : expTilt (-1) μ = expTilt (-1) ν := by
    refine Measure.ext_of_forall_laplaceTransform_natCast_eq fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) - -1 := by
      simp only [sub_neg_eq_add]
      positivity
    rw [laplaceTransform_expTilt, laplaceTransform_expTilt,
      ← hμ.eq_laplaceTransform hpos, ← hν.eq_laplaceTransform hpos]
  calc
    μ = expTilt 1 (expTilt (-1) μ) := by rw [expTilt_expTilt]; norm_num [expTilt_zero]
    _ = expTilt 1 (expTilt (-1) ν) := by rw [hkey]
    _ = ν := by rw [expTilt_expTilt]; norm_num [expTilt_zero]

/-! ## Existence -/

/-- Two shifts `t ↦ f (t + a)` and `t ↦ f (t + b)` of the same function, with `a ≤ b`, have
representing measures whose tilts by `e^{a p}` and `e^{b p}` agree. -/
private lemma expTilt_eq_of_representsLaplace_shift {a b : ℝ} (hab : a ≤ b)
    (hμ : RepresentsLaplace μ fun t => f (t + a))
    (hν : RepresentsLaplace ν fun t => f (t + b)) :
    expTilt a μ = expTilt b ν := by
  have _ := hμ.isFiniteMeasure
  have _ := isFiniteMeasure_expTilt_of_nonpos μ (a := a - b) (by linarith)
  have hrep : RepresentsLaplace (expTilt (a - b) μ) fun t => f (t + b) := by
    refine representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩
    have h := hμ.eq_laplaceTransform (t := t - (a - b)) (by linarith)
    rw [laplaceTransform_expTilt]
    refine (h.symm.trans ?_).symm
    congr 1
    ring
  rw [← hrep.unique hν, expTilt_expTilt]
  congr 1
  ring

/-- **Existence half of the open-half-line Hausdorff--Bernstein--Widder theorem.** A function
completely monotone on `(0, ∞)` is the Laplace transform of a positive -- possibly infinite --
measure on `ℝ≥0`.

The positive shifts `t ↦ f (t + a)` are completely monotone on the closed half-line, so
Bernstein's theorem gives them finite representing measures `σ a`; tilting `σ a` by `e^{a p}`
undoes the shift, and the resulting measure does not depend on `a`. -/
theorem exists_representsLaplaceOnIoi_of_isCompletelyMonotoneOnIoi
    (hf : IsCompletelyMonotoneOnIoi f) : ∃ μ : Measure ℝ≥0, RepresentsLaplaceOnIoi μ f := by
  have hex : ∀ a : ℝ, ∃ σ : Measure ℝ≥0, 0 < a → RepresentsLaplace σ fun t => f (t + a) := by
    intro a
    rcases le_or_gt a 0 with ha | ha
    · exact ⟨0, fun h => absurd h (not_lt.mpr ha)⟩
    · obtain ⟨σ, hσ⟩ :=
        exists_representsLaplace_of_isCompletelyMonotone
          (hf.isCompletelyMonotone_comp_add_const ha)
      exact ⟨σ, fun _ => hσ⟩
  choose σ hσ using hex
  have key : ∀ a : ℝ, 0 < a → expTilt a (σ a) = expTilt 1 (σ 1) := by
    intro a ha
    rcases le_total a 1 with h | h
    · exact expTilt_eq_of_representsLaplace_shift h (hσ a ha) (hσ 1 one_pos)
    · exact (expTilt_eq_of_representsLaplace_shift h (hσ 1 one_pos) (hσ a ha)).symm
  refine ⟨expTilt 1 (σ 1), fun t ht => ?_, fun t ht => ?_⟩
  · have hhalf : (0 : ℝ) < t / 2 := by linarith
    have _ := (hσ (t / 2) hhalf).isFiniteMeasure
    rw [← key (t / 2) hhalf, integrable_exp_neg_mul_expTilt_iff]
    exact integrable_exp_neg_mul _ (by linarith)
  · have hhalf : (0 : ℝ) < t / 2 := by linarith
    have h := (hσ (t / 2) hhalf).eq_laplaceTransform (t := t - t / 2) (by linarith)
    rw [← key (t / 2) hhalf, laplaceTransform_expTilt]
    refine (h.symm.trans ?_).symm
    congr 1
    ring

/-! ## The headline equivalence -/

/-- **The Hausdorff--Bernstein--Widder theorem on the open half-line.** A function is completely
monotone on `(0, ∞)` if and only if it is the Laplace transform of a positive measure on `ℝ≥0`,
integrable against the exponential kernel at every positive parameter.

Compare `TauCeti.hausdorff_bernstein_widder`, which adds continuity at `0` to the hypotheses and
gets a *finite* measure in return. -/
theorem hausdorff_bernstein_widder_onIoi (f : ℝ → ℝ) :
    IsCompletelyMonotoneOnIoi f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplaceOnIoi μ f :=
  ⟨exists_representsLaplaceOnIoi_of_isCompletelyMonotoneOnIoi,
    fun ⟨_, hμ⟩ => hμ.isCompletelyMonotoneOnIoi⟩

/-- Unique-existence form of the open-half-line Hausdorff--Bernstein--Widder theorem. -/
theorem hausdorff_bernstein_widder_onIoi_existsUnique (f : ℝ → ℝ) :
    IsCompletelyMonotoneOnIoi f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplaceOnIoi μ f := by
  rw [hausdorff_bernstein_widder_onIoi]
  exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun _ hν => hν.unique hμ⟩, fun ⟨μ, hμ, _⟩ => ⟨μ, hμ⟩⟩

/-! ## The reciprocal, and an infinite representing measure

`t ↦ 1 / t` is the standard witness that the open-half-line theorem cannot return a finite
measure: its representing measure is Lebesgue measure on `(0, ∞)`, pushed to `ℝ≥0`.
-/

/-- Lebesgue measure on `(0, ∞)`, pushed forward to `ℝ≥0`, is infinite. -/
theorem measure_univ_map_toNNReal_volume_restrict_Ioi :
    ((volume.restrict (Ioi (0 : ℝ))).map Real.toNNReal) univ = ∞ := by
  rw [Measure.map_apply continuous_real_toNNReal.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioi]

/-- **The reciprocal is the Laplace transform of Lebesgue measure**: `1 / t = ∫₀^∞ e^{-tx} dx`
for `t > 0`. By `TauCeti.measure_univ_map_toNNReal_volume_restrict_Ioi` the representing measure
is infinite, so this is genuinely outside the reach of the finite-measure theorem. -/
theorem representsLaplaceOnIoi_one_div :
    RepresentsLaplaceOnIoi ((volume.restrict (Ioi (0 : ℝ))).map Real.toNNReal)
      fun t : ℝ => 1 / t := by
  have hmeas : AEMeasurable Real.toNNReal (volume.restrict (Ioi (0 : ℝ))) :=
    continuous_real_toNNReal.measurable.aemeasurable
  have hcomp : ∀ t : ℝ, EqOn (fun x : ℝ => Real.exp (-(t * ((Real.toNNReal x : ℝ≥0) : ℝ))))
      (fun x : ℝ => Real.exp (-(t * x))) (Ioi 0) := by
    intro t x hx
    simp only [Real.coe_toNNReal x (le_of_lt hx)]
  have hint : ∀ t : ℝ, 0 < t →
      IntegrableOn (fun x : ℝ => Real.exp (-(t * ((Real.toNNReal x : ℝ≥0) : ℝ)))) (Ioi 0) := by
    intro t ht
    refine IntegrableOn.congr_fun ?_ (fun x hx => (hcomp t hx).symm) measurableSet_Ioi
    simpa [neg_mul] using exp_neg_integrableOn_Ioi (0 : ℝ) ht
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · rw [integrable_map_measure ((continuous_exp_neg_mul t).aestronglyMeasurable) hmeas]
    exact hint t ht
  · rw [laplaceTransform_apply,
      integral_map hmeas ((continuous_exp_neg_mul t).aestronglyMeasurable),
      setIntegral_congr_fun measurableSet_Ioi (hcomp t),
      integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) 0 ht]
    rw [mul_zero, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]
    exact one_div t

/-- The reciprocal is completely monotone on `(0, ∞)`, read off from its Laplace
representation. -/
theorem isCompletelyMonotoneOnIoi_one_div : IsCompletelyMonotoneOnIoi fun t : ℝ => 1 / t :=
  representsLaplaceOnIoi_one_div.isCompletelyMonotoneOnIoi

end TauCeti
