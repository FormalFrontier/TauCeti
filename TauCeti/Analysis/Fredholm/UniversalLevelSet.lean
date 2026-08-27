/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import TauCeti.Analysis.Fredholm.Parametric

/-!
# Universal level sets of Fredholm families

Let `f : E × Λ → F` be a parametrized equation. At a zero `(x, l)`, write its derivative as
`D₁.coprod D₂`, where `D₁` differentiates in the `E` direction and `D₂` in the parameter
direction. The implicit function theorem locally parametrizes the universal zero set near `(x, l)`
once the total derivative is surjective and its kernel is topologically complemented.

The main result of this file obtains that complemented-kernel hypothesis from the condition used
in Fredholm transversality: `D₁` is Fredholm and `D₁.coprod D₂` is surjective. The proof splits the
finite-dimensional cokernel of `D₁` using parameter directions, and then solves the remaining
range component using a Fredholm decomposition. Thus it does not assume that the universal zero
set already has a manifold chart.

This is the splitting step in the parametric transversality package of McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A.3. The resulting complement
feeds Mathlib's complemented-kernel implicit function theorem, while
`TauCeti.parameterProj` describes the derivative of the projection from the universal zero set to
the parameter space.

## Main results

* `ContinuousLinearMap.IsFredholm.hasRightInverse_coprod`: a surjective total linearization whose
  fixed-parameter part is Fredholm admits a continuous linear right inverse.
* `ContinuousLinearMap.IsFredholm.closedComplemented_ker_coprod`: consequently, the kernel of the
  total linearization is topologically complemented.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace ContinuousLinearMap.IsFredholm

open Module

variable {𝕜 E Λ F : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup Λ] [NormedSpace 𝕜 Λ]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F}

/-- The projection onto the finite-dimensional cokernel direction in a Fredholm package,
restricted to the effect of changing the parameter. -/
private noncomputable def parameterObstruction
    (pkg : ContinuousLinearMap.FredholmPackage D₁) :
    Λ →L[𝕜] pkg.decCodom.X₀ :=
  (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm).comp D₂

/-- Surjectivity of the total linearization says that parameter directions cover the obstruction
space of a Fredholm package. -/
private theorem parameterObstruction_surjective
    (pkg : ContinuousLinearMap.FredholmPackage D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    Function.Surjective (parameterObstruction (D₂ := D₂) pkg) := by
  intro c
  obtain ⟨⟨x, l⟩, hxl⟩ := hD (c : F)
  refine ⟨l, ?_⟩
  have hp := congrArg
    (pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm) hxl
  simpa [parameterObstruction, pkg.eq_equiv] using hp

variable [CompleteSpace 𝕜]

/-- **A surjective total linearization splits continuously when its fixed-parameter part is
Fredholm.**

If `D₁ : E →L[𝕜] F` is Fredholm and `D₁.coprod D₂ : E × Λ →L[𝕜] F` is surjective, then the latter
has a continuous linear right inverse. Parameter directions first solve the finite-dimensional
cokernel component of `D₁`; a Fredholm quasi-inverse then solves the remaining range component. -/
theorem hasRightInverse_coprod (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    (D₁.coprod D₂).HasRightInverse := by
  let pkg := hD₁.nonempty_fredholmPackage.some
  let P : F →L[𝕜] pkg.decCodom.X₀ :=
    pkg.decCodom.X₀.projectionOntoL pkg.decCodom.X₁ pkg.decCodom.isTopCompl.symm
  let q : Λ →L[𝕜] pkg.decCodom.X₀ := parameterObstruction (D₂ := D₂) pkg
  have hq : Function.Surjective q := parameterObstruction_surjective pkg hD
  let _ : FiniteDimensional 𝕜 pkg.decCodom.X₀ := pkg.decCodom.finite_X₀
  let qinv : pkg.decCodom.X₀ →L[𝕜] Λ :=
    (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hq).rightInverse
  have hqinv : Function.RightInverse qinv q :=
    ContinuousLinearMap.HasRightInverse.rightInverse_rightInverse
      (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hq)
  let L : F →L[𝕜] Λ := qinv.comp P
  let R : F →L[𝕜] E :=
    pkg.quasiInverse.comp ((ContinuousLinearMap.id 𝕜 F) - D₂.comp L)
  refine ⟨R.prod L, fun y => ?_⟩
  have hq_eq : q = P.comp D₂ := by
    rfl
  have hPL : P (D₂ (L y)) = q (qinv (P y)) := by
    simp [L, hq_eq]
  have hP_sub : P (y - D₂ (L y)) = 0 := by
    rw [map_sub, hPL]
    exact sub_eq_zero.mpr (hqinv (P y)).symm
  have hsub_mem : y - D₂ (L y) ∈ pkg.decCodom.X₁ := by
    rw [← Submodule.ker_projectionOntoL pkg.decCodom.isTopCompl.symm]
    exact hP_sub
  have hproj : pkg.decCodom.proj (y - D₂ (L y)) = ⟨y - D₂ (L y), hsub_mem⟩ := by
    simpa only [FredholmDecomposition.proj] using
      Submodule.projectionOntoL_apply_left pkg.decCodom.isTopCompl
        (⟨y - D₂ (L y), hsub_mem⟩ : pkg.decCodom.X₁)
  have hright : D₁ (pkg.quasiInverse (y - D₂ (L y))) = y - D₂ (L y) := by
    simp [ContinuousLinearMap.FredholmPackage.quasiInverse, pkg.eq_equiv, hproj,
      FredholmDecomposition.proj]
  have hR : R y = pkg.quasiInverse (y - D₂ (L y)) := by
    simp [R]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply]
  rw [hR, hright, sub_add_cancel]

/-- The kernel of a surjective total linearization is topologically complemented when its
fixed-parameter part is Fredholm. This is the complemented-kernel hypothesis required by the
Banach-space implicit function theorem for the universal zero set. -/
theorem closedComplemented_ker_coprod (hD₁ : ContinuousLinearMap.IsFredholm D₁)
    (hD : Function.Surjective (D₁.coprod D₂)) :
    (D₁.coprod D₂).ker.ClosedComplemented :=
  let hright := hD₁.hasRightInverse_coprod hD
  ContinuousLinearMap.closedComplemented_ker_of_rightInverse _ hright.rightInverse
    hright.rightInverse_rightInverse

end ContinuousLinearMap.IsFredholm
