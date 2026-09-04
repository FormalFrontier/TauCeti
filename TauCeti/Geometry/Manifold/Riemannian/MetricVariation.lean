/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.MetricVariation
public import TauCeti.Geometry.Manifold.Riemannian.Restriction
public import TauCeti.Geometry.Manifold.Riemannian.EVariationComparison

/-!
# Metric variation of paths in open Riemannian submanifolds

For an open submanifold of an inner-product space, the restricted Riemannian metric is the
ambient metric.  Consequently the total metric variation of a `C¹` path is exactly its
`Manifold.pathELength`: both are the integral of the norm of the ambient derivative.  This file
connects the vector-valued metric-variation identity with the canonical Riemannian path-length API.

The equality gives lower semicontinuity of Riemannian path length for uniformly convergent `C¹`
paths in any open submanifold of an inner-product space.  The corresponding theorem for an
arbitrary Riemannian manifold still requires the local chart comparison and finite subdivision
argument.

## Main results

* `TauCeti.Manifold.eVariationOn_eq_pathELength`: total metric variation equals Riemannian path
  length for a `C¹` path in any open submanifold of an inner-product space.
* `TauCeti.Manifold.pathELength_le_liminf`: path length is lower semicontinuous under
  uniform convergence of `C¹` paths in that submanifold.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 7, Section 2.
* The Hopf--Rinow roadmap, Layer 0, “Regular reparametrization and limits”.
-/

public section

open Filter MeasureTheory Set TopologicalSpace
open scoped Bundle ContDiff ENNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  {U : Opens F} {γ : ℝ → U} {a b : ℝ}

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem eVariationOn_subtypeVal_comp {γ : ℝ → U} {s : Set ℝ} :
    eVariationOn γ s = eVariationOn ((Subtype.val : U → F) ∘ γ) s := by
  rfl

omit [FiniteDimensional ℝ F] in
private theorem contDiffOn_subtypeVal_comp {γ : ℝ → U}
    (hγ : CMDiff[Icc a b] 1 γ) :
    ContDiffOn ℝ 1 ((Subtype.val : U → F) ∘ γ) (Icc a b) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact contMDiff_subtype_val.comp_contMDiffOn hγ

/-- **Metric variation equals Riemannian path length on an open submanifold.** If `U` is an open
subset of an inner-product space and `γ` is `C¹` on `[a, b]`, then the total variation of `γ` for
the restricted metric is its Riemannian path length. -/
theorem eVariationOn_eq_pathELength
    (hγ : CMDiff[Icc a b] 1 γ) :
    eVariationOn γ (Icc a b) = Manifold.pathELength 𝓘(ℝ, F) γ a b := by
  rw [eVariationOn_subtypeVal_comp, eVariationOn_eq_lintegral_enorm_derivWithin
    (contDiffOn_subtypeVal_comp hγ)]
  rw [Manifold.pathELength_subtypeVal_comp hγ,
    Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  -- The scalar tangent space is definitionally the model field, but its bundled instances hide
  -- this from rewriting until the two one-dimensional continuous linear maps are exposed.
  change ‖derivWithin (Subtype.val ∘ γ) (Icc a b) t‖ₑ =
    ‖(fderivWithin ℝ (Subtype.val ∘ γ) (Icc a b) t : ℝ → F) 1‖ₑ
  rw [fderivWithin_derivWithin]

/-- **Lower semicontinuity on an open submanifold.** Let `γᵢ` be eventually `C¹` on a fixed compact
interval and converge uniformly there to a `C¹` path `γ`. For the restricted Riemannian metric on
an open subset, the length of `γ` is at most the `liminf` of the lengths of `γᵢ`. -/
theorem pathELength_le_liminf
    {ι : Type*} {l : Filter ι} {γi : ι → ℝ → U}
    (hγi : ∀ᶠ i in l, CMDiff[Icc a b] 1 (γi i))
    (hγ : CMDiff[Icc a b] 1 γ)
    (hconv : TendstoUniformlyOn γi γ l (Icc a b)) :
    Manifold.pathELength 𝓘(ℝ, F) γ a b ≤
      liminf (fun i ↦ Manifold.pathELength 𝓘(ℝ, F) (γi i) a b) l := by
  rw [← eVariationOn_eq_pathELength hγ]
  calc
    eVariationOn γ (Icc a b) ≤
        liminf (fun i ↦ eVariationOn (γi i) (Icc a b)) l :=
      eVariationOn_le_liminf_of_eventually_le
        (hγi.mono fun _ _ ↦ le_rfl)
        (fun t ht ↦ hconv.tendsto_at ht)
    _ = liminf (fun i ↦ Manifold.pathELength 𝓘(ℝ, F) (γi i) a b) l :=
      liminf_congr (hγi.mono fun i hi ↦ eVariationOn_eq_pathELength hi)

end TauCeti.Manifold

end
