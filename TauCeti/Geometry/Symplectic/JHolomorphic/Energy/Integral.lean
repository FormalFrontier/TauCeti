/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Integrated energy for maps from the standard complex line

This file integrates the pointwise energy density from
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Basic`.  Given a measurable source `X`, a
measure `μ`, and a field

`du : X → (ℝ × ℝ) →ₗ[ℝ] V`,

its energy is

`∫⁻ x, ENNReal.ofReal (energyDensity (du x) / 2) ∂μ`.

The factor `1 / 2` is the standard convention for the energy of a map.  Thus a complex-linear
differential has energy density exactly equal to its symplectic area density.  The differential is
kept explicit: for a differentiable map `u`, consumers use
`fun x ↦ (fderiv ℝ u x).toLinearMap`.  This avoids assigning a misleading energy to a
nondifferentiable map, since Mathlib defines `fderiv` to be zero where differentiability fails.

Under a taming hypothesis, zero energy is equivalent to the differential vanishing almost
everywhere (assuming the energy integrand is a.e. measurable).  Under compatibility, the
integrated Wirtinger inequality bounds symplectic area by energy, and equality holds when the
differential is complex-linear almost everywhere.  These are the total-energy statements needed
before the compactness theory for `J`-holomorphic strips and disks.

## Main declarations

* `TauCeti.SymplecticForm.stdComplexLineEnergy`: the integrated energy of a field of
  differentials.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_eq_zero_iff`: zero energy detects a differential
  that vanishes almost everywhere.
* `TauCeti.SymplecticForm.lintegral_symplecticForm_le_stdComplexLineEnergy`: the integrated
  Wirtinger inequality.
* `TauCeti.SymplecticForm.stdComplexLineEnergy_eq_lintegral_symplecticForm`: equality of energy
  and symplectic area for a complex-linear differential.
* `TauCeti.IsConstStructureJHolomorphic.stdComplexLineEnergy_eq_lintegral_symplecticForm`: the
  energy--area identity for a globally constant-structure `J`-holomorphic map.

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

/-- The normalized energy of a field of real-linear maps out of the standard complex line.

For the differential `du` of a map, this is
`(1 / 2) ∫ |du|²`.  It takes values in `ℝ≥0∞`, so infinite energy is represented honestly rather
than being collapsed to zero by a nonintegrable Bochner integral. -/
noncomputable irreducible_def stdComplexLineEnergy
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ω.stdComplexLineEnergyDensity J (du x) / (1 + 1)) ∂μ

/-- The energy of a differential field is the lower integral of its normalized pointwise energy
density. -/
lemma stdComplexLineEnergy_apply
    (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (du : X → ((ℝ × ℝ) →ₗ[ℝ] V)) (μ : Measure X) :
    ω.stdComplexLineEnergy J du μ =
      ∫⁻ x, ENNReal.ofReal (ω.stdComplexLineEnergyDensity J (du x) / 2) ∂μ :=
  by simpa only [one_add_one_eq_two] using stdComplexLineEnergy_def ω J du μ

/-- Energy depends only on the differential field almost everywhere. -/
lemma stdComplexLineEnergy_congr
    (h : du =ᵐ[μ] dv) :
    ω.stdComplexLineEnergy J du μ = ω.stdComplexLineEnergy J dv μ := by
  rw [stdComplexLineEnergy_apply, stdComplexLineEnergy_apply]
  exact lintegral_congr_ae <| h.mono fun x hx => by
    simp [hx]

/-- Enlarging the source measure cannot decrease energy. -/
lemma stdComplexLineEnergy_mono_measure (hμν : μ ≤ ν) :
    ω.stdComplexLineEnergy J du μ ≤ ω.stdComplexLineEnergy J du ν := by
  rw [stdComplexLineEnergy_apply, stdComplexLineEnergy_apply]
  exact lintegral_mono' hμν le_rfl

/-- The zero differential has zero energy. -/
@[simp]
lemma stdComplexLineEnergy_zero :
    ω.stdComplexLineEnergy J (fun _ : X => 0) μ = 0 := by
  simp [stdComplexLineEnergy_apply, stdComplexLineEnergyDensity_apply]

/-- Every differential has zero energy with respect to the zero measure. -/
@[simp]
lemma stdComplexLineEnergy_zero_measure :
    ω.stdComplexLineEnergy J du 0 = 0 := by
  simp [stdComplexLineEnergy_apply]

/-- The energy of a constant differential is its normalized pointwise density times the total
mass of the source. -/
lemma stdComplexLineEnergy_const (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergy J (fun _ : X => F) μ =
      ENNReal.ofReal (ω.stdComplexLineEnergyDensity J F / 2) * μ Set.univ := by
  rw [stdComplexLineEnergy_apply, lintegral_const]

private lemma energyIntegrand_eq_zero_iff (hω : ω.Tames J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ENNReal.ofReal (ω.stdComplexLineEnergyDensity J F / 2) = 0 ↔ F = 0 := by
  rw [ENNReal.ofReal_eq_zero]
  have hnonneg := ω.stdComplexLineEnergyDensity_nonneg hω F
  constructor
  · intro h
    exact (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mp (by linarith)
  · rintro rfl
    simp [stdComplexLineEnergyDensity_apply]

/-- Under tameness, energy vanishes exactly when the differential vanishes almost everywhere.

The a.e.-measurability assumption is necessary for the implication from zero energy to a.e.
vanishing: the lower Lebesgue integral of a nonmeasurable function can be zero without that
function vanishing almost everywhere. -/
lemma stdComplexLineEnergy_eq_zero_iff (hω : ω.Tames J)
    (hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (ω.stdComplexLineEnergyDensity J (du x) / 2)) μ) :
    ω.stdComplexLineEnergy J du μ = 0 ↔ du =ᵐ[μ] 0 := by
  rw [stdComplexLineEnergy_apply, lintegral_eq_zero_iff' hmeas]
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
    ω.stdComplexLineEnergy J du μ = 0 := by
  rw [stdComplexLineEnergy_apply]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hdu] with x hx
  simp [hx, stdComplexLineEnergyDensity_apply]

/-- **Integrated Wirtinger inequality.**  For a compatible pair, the integral of the positive
symplectic area density is at most the energy. -/
lemma lintegral_symplecticForm_le_stdComplexLineEnergy (hcompat : ω.Compatible J) :
    (∫⁻ x, ENNReal.ofReal
      (ω (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ) ≤
        ω.stdComplexLineEnergy J du μ := by
  rw [stdComplexLineEnergy_apply]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have hpoint :=
    ω.two_mul_symplecticForm_le_stdComplexLineEnergyDensity hcompat (du x)
  linarith

/-- A complex-linear differential has energy equal to the integral of its symplectic area
density.  In particular, this applies to the differential of a constant-structure
`J`-holomorphic map. -/
lemma stdComplexLineEnergy_eq_lintegral_symplecticForm
    (hdu : ∀ᵐ x ∂μ, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (du x)) :
    ω.stdComplexLineEnergy J du μ =
      ∫⁻ x, ENNReal.ofReal
        (ω (du x stdComplexLineReal) (du x stdComplexLineImag)) ∂μ := by
  rw [stdComplexLineEnergy_apply]
  apply lintegral_congr_ae
  filter_upwards [hdu] with x hx
  rw [hx.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm]
  congr 1
  ring

end SymplecticForm

namespace IsConstStructureJHolomorphic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {ω : SymplecticForm W}
variable {f : ℝ × ℝ → W}

/-- The energy of a globally constant-structure `J`-holomorphic map is the lower Lebesgue
integral of its symplectic area density. -/
lemma stdComplexLineEnergy_eq_lintegral_symplecticForm
    (hf : IsConstStructureJHolomorphic (AlmostComplexStructure.product ℝ) J f)
    (μ : Measure (ℝ × ℝ)) :
    ω.stdComplexLineEnergy J (fun x ↦ (fderiv ℝ f x).toLinearMap) μ =
      ∫⁻ x, ENNReal.ofReal
        (ω (fderiv ℝ f x stdComplexLineReal)
          (fderiv ℝ f x stdComplexLineImag)) ∂μ := by
  apply ω.stdComplexLineEnergy_eq_lintegral_symplecticForm
  filter_upwards with x
  exact (hf.isConstStructureJHolomorphicAt x).fderiv_isComplexLinear

end IsConstStructureJHolomorphic

end TauCeti
