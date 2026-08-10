/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Regularity of directional derivatives along vector fields

This file records the regularity of applying the manifold differential of a function to a smooth
tangent-bundle section.

## Main result

* `ContMDiff.contMDiff_mvfderiv_apply`: applying the differential of a `C^n` function to a `C^m`
  tangent-bundle section is `C^m` when `m + 1 ≤ n`.

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

/-- Applying the differential of a `C^n` function to a `C^m` tangent-bundle section is `C^m`
when `m + 1 ≤ n`. -/
theorem ContMDiff.contMDiff_mvfderiv_apply {f : M → F}
    {V : ∀ x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(𝕜, F) n f)
    (hV : ContMDiff I I.tangent m (fun x => (V x : TangentBundle I M)))
    (hmn : m + 1 ≤ n) :
    ContMDiff I 𝓘(𝕜, F) m (fun x => mvfderiv I f x (V x)) := by
  let df : TangentBundle I M → TangentBundle 𝓘(𝕜, F) F := tangentMap% f
  have hdf : ContMDiff I.tangent 𝓘(𝕜, F).tangent m df :=
    hf.contMDiff_tangentMap hmn
  have hsnd : ContMDiff 𝓘(𝕜, F).tangent 𝓘(𝕜, F) m
      (fun p : TangentBundle 𝓘(𝕜, F) F => p.2) :=
    contMDiff_snd_tangentBundle_modelSpace F 𝓘(𝕜, F)
  -- `TangentSpace 𝓘(𝕜, F) (f x)` is definitionally `F`; there is no lemma-based rewrite.
  change ContMDiff I 𝓘(𝕜, F) m
    (fun x => mfderiv I 𝓘(𝕜, F) f x (V x))
  have h := hsnd.comp (hdf.comp hV)
  exact h.congr fun x => rfl
