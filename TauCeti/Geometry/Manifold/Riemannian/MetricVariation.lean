/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.MetricVariation
public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.EVariationComparison

/-!
# Metric variation of paths in open Riemannian submanifolds

For an open submanifold of an inner-product space, the restricted Riemannian metric is the
ambient metric.  Consequently the total metric variation of a `C¹` path is exactly its
`Manifold.pathELength`: both are the integral of the norm of the ambient derivative.  This file
connects the vector-valued metric-variation identity with the canonical Riemannian path-length API.

The equality gives lower semicontinuity of Riemannian path length for pointwise convergent `C¹`
paths in any open submanifold of an inner-product space.

## Main results

* `TauCeti.Manifold.eVariationOn_eq_pathELength_open`: total metric variation equals Riemannian path
  length for a `C¹` path in any open submanifold of an inner-product space.
* `TauCeti.Manifold.pathELength_le_liminf_open`: path length is lower semicontinuous under
  pointwise convergence of `C¹` paths in that submanifold.
* `TauCeti.Manifold.pathELength_le_liminf_open_of_tendstoUniformlyOn`: the same lower
  semicontinuity result under uniform convergence on the interval.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.

-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Bundle ContDiff ENNReal Manifold Topology TauCeti

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]
  {U : Opens F} {γ : ℝ → U} {a b : ℝ}

/-- **Metric variation equals Riemannian path length on an open submanifold.** If `U` is an open
subset of an inner-product space and `γ` is `C¹` on `[a, b]`, then the total variation of `γ` for
the restricted metric is its Riemannian path length. -/
theorem eVariationOn_eq_pathELength_open
    (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) = Manifold.pathELength 𝓘(ℝ, F) γ a b := by
  calc
    eVariationOn γ (Icc a b) =
        eVariationOn ((Subtype.val : U → F) ∘ γ) (Icc a b) :=
      TauCeti.eVariationOn_subtypeVal_comp
    _ = ∫⁻ t in Icc a b, ‖derivWithin ((Subtype.val : U → F) ∘ γ) (Icc a b) t‖ₑ :=
      eVariationOn_eq_lintegral_enorm_derivWithin
        (contMDiffOn_iff_contDiffOn.mp
          ((ContMDiffOn.subtypeVal_comp_iff U γ (Icc a b)).mpr hγ))
    _ = Manifold.pathELength 𝓘(ℝ, F) ((Subtype.val : U → F) ∘ γ) a b := by
      rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
      simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      -- The scalar tangent space is definitionally the model field, but its bundled instances hide
      -- this from rewriting until the two one-dimensional continuous linear maps are exposed.
      change ‖derivWithin (Subtype.val ∘ γ) (Icc a b) t‖ₑ =
        ‖(fderivWithin ℝ (Subtype.val ∘ γ) (Icc a b) t : ℝ → F) 1‖ₑ
      rw [fderivWithin_derivWithin]
    _ = Manifold.pathELength 𝓘(ℝ, F) γ a b :=
      (Manifold.pathELength_subtypeVal_comp hγ).symm

/-- **Lower semicontinuity on an open submanifold.** Let `γᵢ` be eventually `C¹` on a fixed compact
interval and converge pointwise there to a `C¹` path `γ`. For the restricted Riemannian metric on
an open subset, the length of `γ` is at most the `liminf` of the lengths of `γᵢ`. -/
theorem pathELength_le_liminf_open
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → U}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : CMDiff[Icc a b] 1 γ)
    (hconv : ∀ t ∈ Icc a b, Tendsto (fun i ↦ γi i t) l (𝓝 (γ t))) :
    Manifold.pathELength 𝓘(ℝ, F) γ a b ≤
      liminf (fun i ↦ Manifold.pathELength 𝓘(ℝ, F) (γi i) a b) l := by
  rw [← eVariationOn_eq_pathELength_open hγ]
  have hconv' : ∀ t ∈ Icc a b,
      Tendsto (fun i ↦ (γi i t : F)) l (𝓝 (γ t : F)) := fun t ht ↦
    continuous_subtype_val.continuousAt.tendsto.comp (hconv t ht)
  calc
    eVariationOn γ (Icc a b) =
        eVariationOn ((Subtype.val : U → F) ∘ γ) (Icc a b) :=
      TauCeti.eVariationOn_subtypeVal_comp (f := γ)
    _ ≤ liminf (fun i ↦
        Manifold.pathELength 𝓘(ℝ, F) ((Subtype.val : U → F) ∘ γi i) a b) l :=
      eVariationOn_le_liminf_pathELength
        (I := 𝓘(ℝ, F)) (M := F)
        (hγi.mono fun i hi ↦
          (ContMDiffOn.subtypeVal_comp_iff U (γi i) (Icc a b)).mpr hi)
        hconv'
    _ = liminf (fun i ↦ Manifold.pathELength 𝓘(ℝ, F) (γi i) a b) l :=
      liminf_congr (hγi.mono fun i hi ↦
        (Manifold.pathELength_subtypeVal_comp (γ := γi i) hi).symm)

/-- **Lower semicontinuity under uniform convergence on an open submanifold.** Let `γᵢ` be
eventually `C¹` on a fixed compact interval, converge uniformly there to a `C¹` path `γ`, and
use the restricted Riemannian metric on an open subset. Then the length of `γ` is at most the
`liminf` of the lengths of `γᵢ`. -/
theorem pathELength_le_liminf_open_of_tendstoUniformlyOn
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → U}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : CMDiff[Icc a b] 1 γ)
    (hconv : TendstoUniformlyOn γi γ l (Icc a b)) :
    Manifold.pathELength 𝓘(ℝ, F) γ a b ≤
      liminf (fun i ↦ Manifold.pathELength 𝓘(ℝ, F) (γi i) a b) l :=
  pathELength_le_liminf_open hγi hγ fun _ ht ↦ hconv.tendsto_at ht

end TauCeti.Manifold

end
