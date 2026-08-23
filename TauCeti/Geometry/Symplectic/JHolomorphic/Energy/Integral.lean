/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Integrated energy for maps from the standard complex line

This file integrates the pointwise energy density from
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic`.  Given a measurable source `X`, a
measure `μ`, and a field

`du : X → (ℝ × ℝ) →ₗ[ℝ] V`,

its energy is

`∫⁻ x, ENNReal.ofReal (energyDensity (du x) / 2) ∂μ`.

The factor `1 / 2` is the standard convention for the energy of a map.  The named pointwise
density `stdComplexLineEnergyDensity` is *twice* the symplectic area density on a complex-linear
differential, so it is the normalized half-density integrated here that equals the area density
`ω (du ∂s) (du ∂t)` exactly.  The differential is kept explicit: for a differentiable map `u`,
consumers use
`fun x ↦ (fderiv ℝ u x).toLinearMap`.  This avoids assigning a misleading energy to a
nondifferentiable map, since Mathlib defines `fderiv` to be zero where differentiability fails.

Under a taming hypothesis, zero energy is equivalent to the differential vanishing almost
everywhere (assuming the energy integrand is a.e. measurable).  Under compatibility, the
integrated Wirtinger inequality bounds the integral of the symplectic area density by energy;
equality needs only that the differential is complex linear almost everywhere.  These are the
first total-energy statements needed before the compactness theory for `J`-holomorphic curves.
Everything is stated for an abstract field of differentials over an abstract measure, so a domain
such as a strip or a disk is handled by restricting the measure to it.

Both integrands are wrapped in `ENNReal.ofReal`, so what is integrated is in each case a positive
part.  A taming pair makes the energy density nonnegative, so nothing is truncated on the energy
side; the symplectic area density `ω (du ∂s) (du ∂t)` of an *arbitrary* differential can be
negative even for a compatible pair, and is truncated when it is.  It is nonnegative once the
differential is complex linear and the pair tames, since then it is half the energy density.

## Main declarations

* `TauCeti.SymplecticForm.stdComplexLineEnergy`: the integrated energy of a field of
  differentials.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_eq_zero_iff`: zero energy detects a differential
  that vanishes almost everywhere.
* `TauCeti.SymplecticForm.lintegral_symplecticForm_le_stdComplexLineEnergy`: the integrated
  Wirtinger inequality.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_eq_lintegral_symplecticForm`: equality of energy
  and symplectic area for an almost everywhere complex-linear differential.
* `TauCeti.SymplecticForm.fderiv_stdComplexLineEnergy_eq_lintegral_symplecticForm`: the
  energy--area identity for an almost everywhere constant-structure `J`-holomorphic map.

The convention and the energy--area identity follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Section 2.1.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

namespace SymplecticForm

variable {X V : Type*} [MeasurableSpace X]
variable [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {μ ν : Measure X} {du dv : X → (ℝ × ℝ) →ₗ[ℝ] V}

/-- The normalized energy of a field of real-linear maps out of the standard complex line: the
lower Lebesgue integral of the positive part of half the pointwise associated-form density
`TauCeti.SymplecticForm.stdComplexLineEnergyDensity`.

Nothing here relates `ω` and `J`.  For a compatible pair the density is the energy density of the
associated metric `g = ω(·, J ·)`, so this is the usual `(1 / 2) ∫ |du|²` measured in `g` and the
positive part loses nothing; for a general pair the density can be negative, and `ENNReal.ofReal`
truncates it.  Values lie in `ℝ≥0∞`, so infinite energy is represented honestly rather than being
collapsed to zero by a nonintegrable Bochner integral. -/
noncomputable def stdComplexLineEnergy
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ω.stdComplexLineEnergyDensity J (du x) / 2) ∂μ

/-- The energy of a differential field is the lower integral of its normalized pointwise energy
density. -/
lemma stdComplexLineEnergy_def
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) :
    ω.stdComplexLineEnergy J du μ =
      ∫⁻ x, ENNReal.ofReal (ω.stdComplexLineEnergyDensity J (du x) / 2) ∂μ :=
  (rfl)

-- As in `TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic`, the equation above is the whole
-- elimination API of the energy: the definition is neither `@[expose]`d nor reducible.  It is
-- written out by hand rather than generated by `irreducible_def`, whose equation lemma states the
-- elaborated body, which mentions a proof constant the module system keeps private.
attribute [irreducible] stdComplexLineEnergy

/-- Energy depends only on the differential field almost everywhere. -/
lemma stdComplexLineEnergy_congr_ae
    (h : du =ᵐ[μ] dv) :
    ω.stdComplexLineEnergy J du μ = ω.stdComplexLineEnergy J dv μ := by
  rw [stdComplexLineEnergy_def, stdComplexLineEnergy_def]
  exact lintegral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- Enlarging the source measure cannot decrease energy. -/
lemma stdComplexLineEnergy_mono_measure (hμν : μ ≤ ν) :
    ω.stdComplexLineEnergy J du μ ≤ ω.stdComplexLineEnergy J du ν := by
  rw [stdComplexLineEnergy_def, stdComplexLineEnergy_def]
  exact lintegral_mono' hμν le_rfl

/-- The zero differential has zero energy. -/
@[simp]
lemma stdComplexLineEnergy_zero :
    ω.stdComplexLineEnergy J (fun _ : X => 0) μ = 0 := by
  simp [stdComplexLineEnergy_def]

/-- Every differential has zero energy with respect to the zero measure. -/
@[simp]
lemma stdComplexLineEnergy_zero_measure :
    ω.stdComplexLineEnergy J du 0 = 0 := by
  simp [stdComplexLineEnergy_def]

/-- The energy of a constant differential is its normalized pointwise density times the total
mass of the source. -/
lemma stdComplexLineEnergy_const (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergy J (fun _ : X => F) μ =
      ENNReal.ofReal (ω.stdComplexLineEnergyDensity J F / 2) * μ Set.univ := by
  rw [stdComplexLineEnergy_def, lintegral_const]

private lemma energyIntegrand_eq_zero_iff (hω : ω.Tames J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ENNReal.ofReal (ω.stdComplexLineEnergyDensity J F / 2) = 0 ↔ F = 0 := by
  rw [ENNReal.ofReal_eq_zero]
  have hnonneg := ω.stdComplexLineEnergyDensity_nonneg hω F
  constructor
  · intro h
    exact (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mp (by linarith)
  · rintro rfl
    simp

/-- Under tameness, energy vanishes exactly when the differential vanishes almost everywhere.

The a.e.-measurability assumption is necessary for the implication from zero energy to a.e.
vanishing: the lower Lebesgue integral of a nonmeasurable function can be zero without that
function vanishing almost everywhere.  It is stated for the real-valued pointwise density, so no
consumer has to reassemble the normalization that `TauCeti.SymplecticForm.stdComplexLineEnergy`
applies to it. -/
lemma stdComplexLineEnergy_eq_zero_iff (hω : ω.Tames J)
    (hmeas : AEMeasurable (fun x ↦ ω.stdComplexLineEnergyDensity J (du x)) μ) :
    ω.stdComplexLineEnergy J du μ = 0 ↔ du =ᵐ[μ] 0 := by
  rw [stdComplexLineEnergy_def,
    lintegral_eq_zero_iff' (AEMeasurable.ennreal_ofReal (hmeas.div_const 2))]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact (energyIntegrand_eq_zero_iff (ω := ω) hω (du x)).mp <| by
      simpa only [Pi.zero_apply] using hx
  · intro h
    filter_upwards [h] with x hx
    simpa only [Pi.zero_apply] using
      (energyIntegrand_eq_zero_iff (ω := ω) hω (du x)).mpr hx

/-- If the differential vanishes almost everywhere, then its energy is zero.  This direction does
not require measurability. -/
lemma stdComplexLineEnergy_eq_zero_of_ae_eq_zero
    (hdu : du =ᵐ[μ] 0) :
    ω.stdComplexLineEnergy J du μ = 0 :=
  (stdComplexLineEnergy_congr_ae hdu).trans stdComplexLineEnergy_zero

/-- **Integrated Wirtinger inequality.**  For a compatible pair, the integral of the positive
symplectic area density is at most the energy. -/
lemma lintegral_symplecticForm_le_stdComplexLineEnergy (hcompat : ω.Compatible J) :
    (∫⁻ x, ENNReal.ofReal
      (ω (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ) ≤
        ω.stdComplexLineEnergy J du μ := by
  rw [stdComplexLineEnergy_def]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hpoint :=
    ω.two_mul_symplecticForm_le_stdComplexLineEnergyDensity hcompat (du x)
  linarith

/-- **Equality in the integrated Wirtinger inequality.**  A differential that is complex linear
almost everywhere has energy equal to the integral of its symplectic area density.  In particular,
this applies to the differential of a constant-structure `J`-holomorphic map.

No hypothesis on the pair `(ω, J)` is needed: complex linearity alone makes the pointwise energy
density twice the symplectic area density, so the two `ENNReal.ofReal` integrands agree pointwise.
Under a taming pair the common value is moreover nonnegative, and the identity is the
energy--area identity rather than one between positive parts. -/
lemma stdComplexLineEnergy_eq_lintegral_symplecticForm
    (hdu : ∀ᵐ x ∂μ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (du x)) :
    ω.stdComplexLineEnergy J du μ =
      ∫⁻ x, ENNReal.ofReal
        (ω (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ := by
  rw [stdComplexLineEnergy_def]
  apply lintegral_congr_ae
  filter_upwards [hdu] with x hx
  rw [hx.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm (ω := ω)]
  congr 1
  ring

section Map

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {ω : SymplecticForm W}
variable {f : ℝ × ℝ → W} {μ : Measure (ℝ × ℝ)}

/-- The energy of a map that is constant-structure `J`-holomorphic almost everywhere is the lower
Lebesgue integral of its symplectic area density.  Holomorphy is needed only almost everywhere, so
a map holomorphic on a strip or a disk is covered by restricting `μ` to that domain.

As in `TauCeti.SymplecticForm.stdComplexLineEnergy_eq_lintegral_symplecticForm`, no hypothesis
relating `ω` and `J` is needed for the identity; a taming pair is what additionally makes the
common integrand nonnegative, so that neither side is truncated by `ENNReal.ofReal`. -/
lemma fderiv_stdComplexLineEnergy_eq_lintegral_symplecticForm
    (hf : ∀ᵐ x ∂μ, IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.stdComplexLineEnergy J (fun x ↦ (fderiv ℝ f x).toLinearMap) μ =
      ∫⁻ x, ENNReal.ofReal
        (ω (fderiv ℝ f x stdComplexLineReal)
          (fderiv ℝ f x stdComplexLineImag)) ∂μ :=
  ω.stdComplexLineEnergy_eq_lintegral_symplecticForm <|
    hf.mono fun _ hx => hx.fderiv_isComplexLinear

end Map

end SymplecticForm

end TauCeti
