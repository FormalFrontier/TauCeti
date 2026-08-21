/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Symplectic.CompatibleMetric
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import TauCeti.Geometry.Symplectic.Prod.Basic

/-!
# Pointwise energy density for maps from the standard complex line

This file adds the first pointwise energy-density bookkeeping for the analytic Heegaard Floer
roadmap. For a compatible pair `(ω, J)`, the associated metric is
`g(v, w) = ω(v, J w)`. If a real-linear map `F : ℝ × ℝ → V` is complex-linear, then the
standard energy density
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)` is twice the symplectic area density
`ω(F ∂s, F ∂t)`.

Under a taming symplectic form the density is moreover nondegenerate: it is nonnegative for every
real-linear map, vanishes exactly for the zero map, and is positive otherwise. The
Frechet-derivative versions specialize this to pointwise and within-set constant-structure
`J`-holomorphic maps.

For an *arbitrary* real-linear map the density obeys the **Wirtinger inequality**
`2 ω(F ∂s, F ∂t) ≤ g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, the pointwise form of `E(u) ≥ ∫ u^*ω`: the
difference is the Cauchy--Riemann defect square `g(F ∂s + J (F ∂t), F ∂s + J (F ∂t))`, which
vanishes exactly when `F` is complex linear, so the inequality is an equality precisely for
constant-structure `J`-holomorphic maps. This is the linear-algebra content behind
"constant-structure `J`-holomorphic curves minimize
energy in their homology class".

The statements here are pointwise linear algebra and Frechet-derivative calculus. They are
integrated over a measure space in
`TauCeti.Geometry.Symplectic.JHolomorphic.Energy.Integral`.

## Main declarations

* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity`: the metric energy density of a
  real-linear map from the standard complex line.
* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  for a complex-linear map, energy density is twice symplectic area density.
* `IsConstStructureJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  the corresponding Frechet-derivative statement for a pointwise constant-structure `J`-holomorphic
  map.
* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_pos` and
  `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_zero_iff`: nondegeneracy of the density
  under tameness, with
  `TauCeti.IsConstStructureJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_zero_iff` and
  `IsConstStructureJHolomorphicWithinAt.fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff`
  the Frechet-derivative versions.
* `TauCeti.SymplecticForm.prod_stdComplexLineEnergyDensity`: product-target energy density is
  the sum of the factor energy densities.
* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_sub_two_mul_symplecticForm`: the Wirtinger
  identity `energyDensity F - 2 ω(F ∂s, F ∂t) = g(F ∂s + J (F ∂t), F ∂s + J (F ∂t))`.
* `TauCeti.SymplecticForm.two_mul_symplecticForm_le_stdComplexLineEnergyDensity`: the Wirtinger
  inequality `2 ω(F ∂s, F ∂t) ≤ energyDensity F` for a compatible pair, with the
  Frechet-derivative corollaries
  `TauCeti.SymplecticForm.two_mul_symplecticForm_fderiv_le_stdComplexLineEnergyDensity` and
  `TauCeti.SymplecticForm.two_mul_symplecticForm_fderivWithin_le_stdComplexLineEnergyDensity`.
* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm_iff`: equality
  holds exactly for complex-linear (constant-structure `J`-holomorphic) maps.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: for a compatible pair, `g(·, ·) = ω(·, J ·)` and `du(∂t) = J du(∂s)`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V}
variable {ω : SymplecticForm V}

/-- The pointwise metric energy density of a real-linear map from the standard complex line.

For a compatible pair `(ω, J)`, this is
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, where `g(v,w) = ω(v, J w)`. -/
def stdComplexLineEnergyDensity (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) : ℝ :=
  ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag)

/-- The standard complex-line energy density is the sum of the associated bilinear form evaluated
on the images of the standard real and imaginary basis vectors. -/
lemma stdComplexLineEnergyDensity_def (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergyDensity J F =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
        ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) :=
  (rfl)

-- The equation above is the whole elimination API of the energy density: the definition is
-- neither `@[expose]`d nor reducible, so no module ever unfolds the body again. It is written out
-- by hand rather than being generated by `irreducible_def`, whose equation lemma states the
-- *elaborated* body: that mentions the auxiliary `SMulCommClass ℝ ℝ ℝ` instance proof extracted
-- from the helper definition, which the module system keeps private, so rewriting with it from
-- another module fails to kernel-check.
attribute [irreducible] stdComplexLineEnergyDensity

/-- The zero real-linear map has zero standard complex-line energy density.  No hypothesis
relating `ω` and `J` is needed, unlike in
`TauCeti.SymplecticForm.stdComplexLineEnergyDensity_eq_zero_iff`. -/
@[simp]
lemma stdComplexLineEnergyDensity_zero (ω : SymplecticForm V) (J : AlmostComplexStructure V) :
    ω.stdComplexLineEnergyDensity J 0 = 0 := by
  simp [stdComplexLineEnergyDensity_def]

/-- The standard pointwise energy density of any real-linear map is nonnegative under tameness. -/
lemma stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    0 ≤ ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  refine add_nonneg ?_ ?_
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineReal = 0
    · simp [h]
    · exact (hω (F stdComplexLineReal) h).le
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineImag = 0
    · simp [h]
    · exact (hω (F stdComplexLineImag) h).le

/-- Under tameness, the standard pointwise energy density of a nonzero real-linear map from the
standard complex line is positive. -/
lemma stdComplexLineEnergyDensity_pos (hω : ω.Tames J) {F : (ℝ × ℝ) →ₗ[ℝ] V}
    (hFne : F ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  by_cases hreal : F stdComplexLineReal = 0
  · have himag : F stdComplexLineImag ≠ 0 := by
      intro himag
      apply hFne
      apply LinearMap.ext
      intro z
      rw [LinearMap.apply_stdComplexLine F z, hreal, himag]
      simp
    exact add_pos_of_nonneg_of_pos
      (by simp [hreal])
      (by simpa [associatedBilinForm_apply] using hω (F stdComplexLineImag) himag)
  · exact add_pos_of_pos_of_nonneg
      (by simpa [associatedBilinForm_apply] using hω (F stdComplexLineReal) hreal)
      (by
        rw [associatedBilinForm_apply]
        by_cases himag : F stdComplexLineImag = 0
        · simp [himag]
        · exact (hω (F stdComplexLineImag) himag).le)

/-- Under tameness, standard pointwise energy density vanishes exactly for the zero real-linear
map from the standard complex line. -/
@[simp]
lemma stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J)
    {F : (ℝ × ℝ) →ₗ[ℝ] V} :
    ω.stdComplexLineEnergyDensity J F = 0 ↔ F = 0 := by
  constructor
  · intro henergy
    rw [stdComplexLineEnergyDensity_def] at henergy
    have hreal_nonneg :
        0 ≤ ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
      rw [associatedBilinForm_apply]
      by_cases hreal : F stdComplexLineReal = 0
      · simp [hreal]
      · exact (hω (F stdComplexLineReal) hreal).le
    have himag_nonneg :
        0 ≤ ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) := by
      rw [associatedBilinForm_apply]
      by_cases himag : F stdComplexLineImag = 0
      · simp [himag]
      · exact (hω (F stdComplexLineImag) himag).le
    have hreal_zero :
        ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) = 0 := by
      linarith
    have himag_zero :
        ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) = 0 := by
      linarith
    have hreal : F stdComplexLineReal = 0 :=
      (associatedBilinForm_self_eq_zero ((ω.tames_iff_associated_pos J).mp hω)).mp hreal_zero
    have himag : F stdComplexLineImag = 0 :=
      (associatedBilinForm_self_eq_zero ((ω.tames_iff_associated_pos J).mp hω)).mp himag_zero
    apply LinearMap.ext
    intro z
    rw [LinearMap.apply_stdComplexLine F z, hreal, himag]
    simp
  · intro hzero
    simp [hzero]

/-- Under tameness, the standard pointwise energy density is positive exactly for nonzero
real-linear maps from the standard complex line. -/
lemma stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) {F : (ℝ × ℝ) →ₗ[ℝ] V} :
    0 < ω.stdComplexLineEnergyDensity J F ↔ F ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((ω.stdComplexLineEnergyDensity_eq_zero_iff (J := J) hω).mpr hzero)
  · exact ω.stdComplexLineEnergyDensity_pos hω

/-- Under tameness, standard pointwise energy density of a continuous linear map vanishes exactly
when the continuous linear map is zero. -/
lemma stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff
    [TopologicalSpace V] (hω : ω.Tames J) (F : (ℝ × ℝ) →L[ℝ] V) :
    ω.stdComplexLineEnergyDensity J F.toLinearMap = 0 ↔ F = 0 := by
  constructor
  · intro henergy
    have hlin : F.toLinearMap = 0 :=
      (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mp henergy
    exact ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z
  · intro hzero
    rw [hzero]
    exact (ω.stdComplexLineEnergyDensity_eq_zero_iff hω).mpr rfl

/-- Under tameness, the standard pointwise energy density of a continuous linear map is positive
exactly when the continuous linear map is nonzero. -/
lemma stdComplexLineEnergyDensity_toLinearMap_pos_iff
    [TopologicalSpace V] (hω : ω.Tames J) (F : (ℝ × ℝ) →L[ℝ] V) :
    0 < ω.stdComplexLineEnergyDensity J F.toLinearMap ↔ F ≠ 0 := by
  constructor
  · intro hpos hzero
    exact hpos.ne' ((ω.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff hω F).mpr hzero)
  · intro hne
    exact (ω.stdComplexLineEnergyDensity_pos_iff hω).mpr fun hlin =>
      hne (ContinuousLinearMap.ext fun z => LinearMap.congr_fun hlin z)

section Prod

variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}
variable {J₁ : AlmostComplexStructure V} {J₂ : AlmostComplexStructure W}

/-- The standard-line energy density of a real-linear map into a direct-sum target is the sum of
the two factor energy densities of its coordinate projections. -/
@[simp]
lemma prod_stdComplexLineEnergyDensity (F : (ℝ × ℝ) →ₗ[ℝ] V × W) :
    (ω₁.prod ω₂).stdComplexLineEnergyDensity (J₁.prod J₂) F =
      ω₁.stdComplexLineEnergyDensity J₁ ((LinearMap.fst ℝ V W).comp F) +
        ω₂.stdComplexLineEnergyDensity J₂ ((LinearMap.snd ℝ V W).comp F) := by
  simp only [stdComplexLineEnergyDensity_def, prod_associatedBilinForm_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
  ring_nf

end Prod

end SymplecticForm

namespace IsComplexLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- For a complex-linear map out of the standard complex line, the associated-bilinear-form
diagonal of the imaginary-coordinate image equals that of the real-coordinate image. -/
lemma associatedBilinForm_apply_stdComplexLineImag_self_eq
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_apply_self_eq stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the real-coordinate
associated-bilinear-form diagonal is the symplectic area density of the ordered coordinate
pair. -/
lemma associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_self_eq_symplecticForm stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the standard pointwise energy
density is twice the symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.stdComplexLineEnergyDensity J F =
      2 * ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SymplecticForm.stdComplexLineEnergyDensity_def,
    hF.associatedBilinForm_apply_stdComplexLineImag_self_eq,
    hF.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm]
  ring

end IsComplexLinearMap

namespace IsConstStructureJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

/-- For a pointwise constant-structure `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative. -/
lemma associatedBilinForm_fderiv_stdComplexLineImag_self_eq
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineImag)
        (fderiv ℝ f x stdComplexLineImag) =
      ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a pointwise constant-structure `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`. -/
lemma associatedBilinForm_fderiv_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) =
      ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a pointwise constant-structure `J`-holomorphic map from the standard complex line, the
derivative's
standard energy density is twice its symplectic area density. -/
lemma fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap =
      2 * ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderiv_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderiv ℝ f x).toLinearMap

/-- Under tameness, the derivative standard energy density of a map from the standard complex line
vanishes exactly when its Frechet derivative is zero. -/
lemma fderiv_stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap = 0 ↔ fderiv ℝ f x = 0 :=
  ω.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff hω (fderiv ℝ f x)

/-- Under tameness, the derivative standard energy density of a map from the standard complex
line is positive exactly when its Frechet derivative is nonzero. -/
lemma fderiv_stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap ↔ fderiv ℝ f x ≠ 0 :=
  ω.stdComplexLineEnergyDensity_toLinearMap_pos_iff hω (fderiv ℝ f x)

/-- Under tameness, a map with nonzero Frechet derivative has positive standard derivative energy
density. -/
lemma fderiv_stdComplexLineEnergyDensity_pos (hω : ω.Tames J)
    (hfderiv : fderiv ℝ f x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  (fderiv_stdComplexLineEnergyDensity_pos_iff (ω := ω) (J := J) (f := f) (x := x) hω).mpr
    hfderiv

end IsConstStructureJHolomorphicAt

namespace IsConstStructureJHolomorphicWithinAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- For a within-set constant-structure `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineImag_self_eq
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineImag)
        (fderivWithin ℝ f s x stdComplexLineImag) =
      ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) :=
  (hf.fderivWithin_isComplexLinear hs).associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a within-set constant-structure `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) =
      ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  by
    have hlin := hf.fderivWithin_isComplexLinear hs
    exact hlin.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a within-set constant-structure `J`-holomorphic map from the standard complex line, the
derivative's
standard energy density is twice its symplectic area density, provided derivatives within the
set are unique. -/
lemma fderivWithin_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap =
      2 * ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  (hf.fderivWithin_isComplexLinear hs).stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The within-set derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderivWithin_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderivWithin ℝ f s x).toLinearMap

/-- Under tameness, the within-set derivative standard energy density of a map from the standard
complex line vanishes exactly when its Frechet derivative within the set is zero. -/
lemma fderivWithin_stdComplexLineEnergyDensity_eq_zero_iff (hω : ω.Tames J) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap = 0 ↔
      fderivWithin ℝ f s x = 0 :=
  ω.stdComplexLineEnergyDensity_toLinearMap_eq_zero_iff hω (fderivWithin ℝ f s x)

/-- Under tameness, the within-set derivative standard energy density is positive exactly when
the Frechet derivative within the set is nonzero. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos_iff (hω : ω.Tames J) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap ↔
      fderivWithin ℝ f s x ≠ 0 :=
  ω.stdComplexLineEnergyDensity_toLinearMap_pos_iff hω (fderivWithin ℝ f s x)

/-- Under tameness, a map with nonzero Frechet derivative within a set has positive standard
derivative energy density. -/
lemma fderivWithin_stdComplexLineEnergyDensity_pos (hω : ω.Tames J)
    (hfderiv : fderivWithin ℝ f s x ≠ 0) :
    0 < ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  (fderivWithin_stdComplexLineEnergyDensity_pos_iff
    (ω := ω) (J := J) (f := f) (s := s) (x := x) hω).mpr hfderiv

end IsConstStructureJHolomorphicWithinAt

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}

/-- The Wirtinger identity out of the standard complex line: the standard energy density minus
twice the symplectic area density is the Cauchy--Riemann defect square
`g(F ∂s + J (F ∂t), F ∂s + J (F ∂t))`. Needs only `J`-invariance of `ω`. -/
lemma stdComplexLineEnergyDensity_sub_two_mul_symplecticForm (hinv : ω.Invariant J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergyDensity J F -
        2 * ω (F stdComplexLineReal) (F stdComplexLineImag) =
      ω.associatedBilinForm J (F stdComplexLineReal + J (F stdComplexLineImag))
        (F stdComplexLineReal + J (F stdComplexLineImag)) := by
  rw [stdComplexLineEnergyDensity_def]
  linarith [hinv.associatedBilinForm_add_apply_self (F stdComplexLineReal) (F stdComplexLineImag)]

/-- **Wirtinger inequality.** For a compatible pair `(ω, J)` and any real-linear map out of the
standard complex line, twice the symplectic area density of the ordered coordinate pair is at
most the standard energy density: the local form of `E(u) ≥ ∫ u^*ω`. -/
lemma two_mul_symplecticForm_le_stdComplexLineEnergyDensity (hcompat : ω.Compatible J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    2 * ω (F stdComplexLineReal) (F stdComplexLineImag) ≤
      ω.stdComplexLineEnergyDensity J F := by
  have hid := stdComplexLineEnergyDensity_sub_two_mul_symplecticForm hcompat.invariant F
  have hnn : 0 ≤ ω.associatedBilinForm J (F stdComplexLineReal + J (F stdComplexLineImag))
      (F stdComplexLineReal + J (F stdComplexLineImag)) :=
    hcompat.associatedBilinForm_self_nonneg _
  linarith

/-- The Wirtinger inequality is an equality exactly when the map is complex linear, that is,
constant-structure `J`-holomorphic out of the standard complex line: the energy density then equals
twice the
symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_symplecticForm_iff (hcompat : ω.Compatible J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergyDensity J F =
        2 * ω (F stdComplexLineReal) (F stdComplexLineImag) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F := by
  refine ⟨fun heq => ?_, fun hF => hF.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm⟩
  have hid := stdComplexLineEnergyDensity_sub_two_mul_symplecticForm hcompat.invariant F
  have hz : ω.associatedBilinForm J (F stdComplexLineReal + J (F stdComplexLineImag))
      (F stdComplexLineReal + J (F stdComplexLineImag)) = 0 := by
    rw [← hid, heq]; ring
  have hw : F stdComplexLineReal + J (F stdComplexLineImag) = 0 :=
    (hcompat.associatedBilinForm_self_eq_zero).mp hz
  have key : J (F stdComplexLineReal) = F stdComplexLineImag := by
    simpa using congrArg (fun x => J x) (add_eq_zero_iff_eq_neg.mp hw)
  rw [isComplexLinearMap_stdComplexLine_iff]
  exact key.symm

section Fderiv

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J : AlmostComplexStructure W} {ω : SymplecticForm W}
variable {f : ℝ × ℝ → W}

/-- The Wirtinger inequality for the Frechet derivative of any map from the standard complex
line: twice the symplectic area density of the derivative's coordinate pair is at most its
standard energy density. -/
lemma two_mul_symplecticForm_fderiv_le_stdComplexLineEnergyDensity (hcompat : ω.Compatible J)
    (x : ℝ × ℝ) :
    2 * ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) ≤
      ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  two_mul_symplecticForm_le_stdComplexLineEnergyDensity hcompat (fderiv ℝ f x).toLinearMap

/-- The Wirtinger inequality for the within-set Frechet derivative of any map from the standard
complex line. -/
lemma two_mul_symplecticForm_fderivWithin_le_stdComplexLineEnergyDensity
    (hcompat : ω.Compatible J) (s : Set (ℝ × ℝ)) (x : ℝ × ℝ) :
    2 * ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) ≤
      ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  two_mul_symplecticForm_le_stdComplexLineEnergyDensity hcompat (fderivWithin ℝ f s x).toLinearMap

end Fderiv

end SymplecticForm

end TauCeti
