/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# The standard compatible triple on the complex line

The analytic Heegaard Floer roadmap uses the complex line both as the local model for
holomorphic-curve domains and as the one-dimensional target model for elementary checks. The
existing file `TauCeti.Geometry.Symplectic.StandardCompatible` builds the standard compatible
triple on a doubled real inner-product space `V × V`; this file transports the case `V = ℝ`
across Mathlib's real-linear equivalence `Complex.equivRealProdCLM.symm`.

The resulting almost complex structure on `ℂ` is multiplication by `Complex.I`, and the
transported symplectic form is the standard area form
`ω(z, w) = z.re * w.im - z.im * w.re`. Compatibility is inherited from the transported standard
model, giving a concrete non-vacuous model for the pointwise `J`-holomorphic and energy API.

## Main declarations

* `TauCeti.stdComplexSymplecticForm`: the standard symplectic area form on `ℂ`.
* `TauCeti.isComplexLinearMap_equivRealProdCLM_symm` and
  `TauCeti.isSymplectomorphism_equivRealProdCLM_symm`: the coordinate equivalence preserves
  the standard complex and symplectic structures.
* `TauCeti.stdComplexSymplecticForm_compatible`: compatibility of the standard area form with
  the standard complex structure.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard complex line is `ℝ²` with `J(x, y) = (-y, x)` and
`ω((x₁, y₁), (x₂, y₂)) = x₁ y₂ - y₁ x₂`.
-/

public section

namespace TauCeti

open Complex

/-- The standard symplectic area form on `ℂ`, transported from the standard form on `ℝ × ℝ`. -/
noncomputable def stdComplexSymplecticForm : SymplecticForm ℂ :=
  (stdSymplecticForm (V := ℝ)).transport Complex.equivRealProdCLM.symm.toLinearEquiv

private lemma product_transport_equivRealProdCLM_symm_eq_ofComplexModule :
    (AlmostComplexStructure.product ℝ).transport
        Complex.equivRealProdCLM.symm.toLinearEquiv =
      AlmostComplexStructure.ofComplexModule ℂ := by
  refine AlmostComplexStructure.ext fun z => ?_
  apply Complex.ext <;>
    simp [AlmostComplexStructure.ofComplexModule_apply, Complex.equivRealProdCLM_symm_apply,
      Complex.mul_re, Complex.mul_im]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is complex-linear for the standard
complex structures. -/
lemma isComplexLinearMap_equivRealProdCLM_symm :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.ofComplexModule ℂ)
      Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact AlmostComplexStructure.isComplexLinearMap_transport (AlmostComplexStructure.product ℝ)
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is complex-linear for the standard
complex structures. -/
lemma isComplexLinearMap_equivRealProdCLM :
    IsComplexLinearMap (AlmostComplexStructure.ofComplexModule ℂ)
      (AlmostComplexStructure.product ℝ)
      Complex.equivRealProdCLM.toLinearEquiv.toLinearMap := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact AlmostComplexStructure.isComplexLinearMap_symm_transport (AlmostComplexStructure.product ℝ)
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic form on `ℂ` is the usual coordinate area form. -/
@[simp]
lemma stdComplexSymplecticForm_apply (z w : ℂ) :
    stdComplexSymplecticForm z w = z.re * w.im - z.im * w.re := by
  simp [stdComplexSymplecticForm]
  ring

/-- The associated compatible metric on `ℂ` is the standard real dot product. -/
lemma stdComplexSymplecticForm_associatedBilinForm (z w : ℂ) :
    stdComplexSymplecticForm.associatedBilinForm (AlmostComplexStructure.ofComplexModule ℂ) z w =
      z.re * w.re + z.im * w.im := by
  simp [SymplecticForm.associatedBilinForm_apply, AlmostComplexStructure.ofComplexModule_apply]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is a symplectomorphism for the
standard symplectic forms. -/
lemma isSymplectomorphism_equivRealProdCLM_symm :
    SymplecticForm.IsSymplectomorphism (stdSymplecticForm (V := ℝ)) stdComplexSymplecticForm
      Complex.equivRealProdCLM.symm.toLinearEquiv := by
  exact (SymplecticForm.isSymplectomorphism_iff_transport_eq
    (ω₁ := stdSymplecticForm (V := ℝ)) (ω₂ := stdComplexSymplecticForm)
    (e := Complex.equivRealProdCLM.symm.toLinearEquiv)).mpr rfl

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is a symplectomorphism for the
standard symplectic forms. -/
lemma isSymplectomorphism_equivRealProdCLM :
    SymplecticForm.IsSymplectomorphism stdComplexSymplecticForm (stdSymplecticForm (V := ℝ))
      Complex.equivRealProdCLM.toLinearEquiv :=
  isSymplectomorphism_equivRealProdCLM_symm.symm

/-- The standard symplectic form on `ℂ` is invariant under multiplication by `I`. -/
lemma stdComplexSymplecticForm_invariant :
    stdComplexSymplecticForm.Invariant (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_invariant_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic form on `ℂ` tames multiplication by `I`. -/
lemma stdComplexSymplecticForm_tames :
    stdComplexSymplecticForm.Tames (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_tames_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic area form on `ℂ` is compatible with the standard complex structure. -/
lemma stdComplexSymplecticForm_compatible :
    stdComplexSymplecticForm.Compatible (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_compatible_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

end TauCeti
