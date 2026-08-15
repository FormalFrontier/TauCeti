/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Regularity of tangent-bundle-valued maps and directional derivatives

This file records reusable regularity facts for maps into a tangent bundle and for applying the
manifold differential of a function to tangent vectors whose base point varies.

## Main results

* `contMDiff_tangentBundle_mk_zero`: smoothness of the zero tangent vector over a varying point.
* `contMDiff_tangentBundle_mk_constBase`: smoothness of a varying model vector over a fixed point.
* `mvfderiv_apply_eq_mfderiv_apply`: identifies `mvfderiv` with `mfderiv` when the target is a
  normed vector space.
* `mfderiv_continuousLinearMap_apply_const_apply`: differentiation commutes with evaluating a
  continuous-linear-map-valued function at a fixed vector.
* `ContMDiff.contMDiff_mvfderiv_apply`: applying the differential of a `C^n` function on the
  tangent bundle is `C^m` when `m + 1 ≤ n`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n m : ℕ∞ω}

section TangentBundleInputs

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- The zero tangent vector over a smoothly varying manifold point varies smoothly. -/
theorem contMDiff_tangentBundle_mk_zero {f : N → M} (hf : ContMDiff J I n f) :
    ContMDiff J I.tangent n
      (fun p => TotalSpace.mk' E (f p) 0 : N → TangentBundle I M) :=
  (contMDiff_zeroSection 𝕜 (TangentSpace I : M → Type _)).comp hf

/-- A model-space vector placed in the tangent fiber over a fixed point varies smoothly. -/
theorem contMDiff_tangentBundle_mk_constBase {v : N → E}
    (hv : ContMDiff J 𝓘(𝕜, E) n v) (x : M) :
    ContMDiff J I.tangent n
      (fun p => TotalSpace.mk' E x (v p) : N → TangentBundle I M) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace]
  constructor
  · exact contMDiffAt_const
  · have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source _
    have hfun :
        (fun q : N =>
          (trivializationAt E (TangentSpace I) x (TotalSpace.mk' E x (v q))).2) = v := by
      funext q
      rw [TangentBundle.trivializationAt_apply]
      -- Both fibers are over `x`, so their coordinate change is the identity on the model space.
      change tangentCoordChange I x x x (v q) = v q
      rw [tangentCoordChange_self hx]
    rw [hfun]
    exact hv p

end TangentBundleInputs

omit [IsManifold I 1 M] in
/-- For a normed vector-space target, the tangent-space identification in `mvfderiv` is the
canonical one, so evaluating it agrees with evaluating `mfderiv`. -/
@[simp] theorem mvfderiv_apply_eq_mfderiv_apply (f : M → F) (x : M) (v : TangentSpace I x) :
    mvfderiv I f x v = mfderiv I 𝓘(𝕜, F) f x v := by
  rw [mvfderiv, ContinuousLinearMap.comp_apply]
  -- `fromTangentSpace` is Mathlib's explicit interface for this canonical identification.
  rfl

omit [IsManifold I 1 M] in
/-- The derivative of a continuous-linear-map-valued function, evaluated at a fixed vector, is
the derivative of the pointwise evaluation. Tangent spaces of normed vector spaces are
definitionally the vector spaces themselves; the `show ... from` terms expose those identifications
to `mfderiv`. -/
theorem mfderiv_continuousLinearMap_apply_const_apply
    {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (f : M → V →L[𝕜] W) (x : M) (v : TangentSpace I x) (y : V)
    (hf : MDiffAt f x) :
    (show V →L[𝕜] W from mfderiv I 𝓘(𝕜, V →L[𝕜] W) f x v) y =
      (show W from mfderiv I 𝓘(𝕜, W) (fun z ↦ f z y) x v) := by
  let evalY : (V →L[𝕜] W) →L[𝕜] W := (ContinuousLinearMap.apply 𝕜 W) y
  have h := mfderiv_comp_apply x evalY.mdifferentiableAt hf v
  rw [evalY.hasMFDerivAt.mfderiv] at h
  have hfun : evalY ∘ f = fun z ↦ f z y := by
    funext z
    exact ContinuousLinearMap.apply_apply y (f z)
  rw [hfun] at h
  calc
    (show V →L[𝕜] W from mfderiv I 𝓘(𝕜, V →L[𝕜] W) f x v) y =
        evalY (show V →L[𝕜] W from mfderiv I 𝓘(𝕜, V →L[𝕜] W) f x v) :=
      (ContinuousLinearMap.apply_apply y _).symm
    _ = (show W from mfderiv I 𝓘(𝕜, W) (fun z ↦ f z y) x v) := h.symm

/-- The map that applies the differential of a `C^n` function to tangent vectors is `C^m` on the
tangent bundle when `m + 1 ≤ n`. -/
theorem ContMDiff.contMDiff_mvfderiv_apply {f : M → F}
    (hf : ContMDiff I 𝓘(𝕜, F) n f)
    (hmn : m + 1 ≤ n) :
    ContMDiff I.tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle I M => mvfderiv I f p.1 p.2) := by
  let df : TangentBundle I M → TangentBundle 𝓘(𝕜, F) F := tangentMap% f
  have hdf : ContMDiff I.tangent 𝓘(𝕜, F).tangent m df :=
    hf.contMDiff_tangentMap hmn
  have hsnd : ContMDiff 𝓘(𝕜, F).tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle 𝓘(𝕜, F) F => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  have h := hsnd.comp hdf
  have htangent (p : TangentBundle I M) :
      NormedSpace.fromTangentSpace (f p.1) ((tangentMap% f p).2) =
        mvfderiv I f p.1 p.2 := by
    rw [mvfderiv, ContinuousLinearMap.comp_apply, tangentMap_snd]
    rfl
  -- On a model vector space, `NormedSpace.fromTangentSpace` is the identity on the underlying
  -- type, so the second projection computed by `h` agrees definitionally with `mvfderiv`.
  exact h.congr fun p => (htangent p).symm
