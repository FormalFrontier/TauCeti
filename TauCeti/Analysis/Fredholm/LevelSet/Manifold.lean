/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Fredholm.LevelSet.Smooth

/-!
# A regular level set of a Fredholm map is a manifold

Let `f : E → F` be a map between Banach spaces which, at every point of the level set
`{x | f x = c}`, is strictly differentiable and `C^m`, with surjective Fredholm derivative of
index `n`. `TauCeti.levelSetChartedSpace` already makes that level set a charted space modelled on
`Fin n → 𝕜`, the charts being the implicit-function charts of `TauCeti.levelSetChartAt`. This file
proves that those charts are smoothly compatible, so the level set is a `C^m` manifold of
dimension the index.

The transition from the chart at `z` to the chart at `w` is
`k ↦ Ψ (x k - w)`, where `x k` is the point of the level set with coordinate `k` in the chart at
`z`, and `Ψ` is the continuous linear map that reads a vector of `E` in the model space through the
projection onto `ker (D w)`. So everything reduces to smoothness of the inverse chart as a map
into `E`, which is `TauCeti.contDiffAt_coe_levelSetChart_symm_of_mem`: the inverse chart is smooth
at every point of its target, because `TauCeti.levelSetChartAt` was cut down to the neighbourhood
`TauCeti.levelSetImplicitCoordSource` on which the coordinate map of the implicit function theorem
keeps an invertible derivative.

This is the smooth half of the statement that the zero set of a Fredholm section is, at a regular
point, a manifold of dimension the index. As with the charted-space structure it refines, no
global hypothesis such as second countability is assumed, so `IsManifold` here is the smooth-atlas
statement and not the assertion that the level set is a topological manifold in the classical
sense.

## Main results

* `TauCeti.contDiffOn_coe_levelSetChartAt_symm`: the inverse of a preferred chart, included into
  the ambient Banach space, is `C^m` on the whole chart target.
* `TauCeti.contDiffOn_levelSetChartAt_trans`: the transition between two preferred charts is
  `C^m`.
* `TauCeti.isManifold_levelSet`: a regular level set of a `C^m` Fredholm map, of constant index
  `n`, is a `C^m` manifold modelled on `Fin n → 𝕜`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Appendix A.3.
-/

public section

namespace TauCeti

open Set
open scoped ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : E → F} {c : F} {D : E → E →L[𝕜] F} {n : ℕ} {m : ℕ∞ω}

/-- **The inverse of a preferred chart is smooth on the whole chart target.** Read into the
ambient Banach space, the inverse of `TauCeti.levelSetChartAt` is as smooth as the equation is
along the level set. -/
theorem contDiffOn_coe_levelSetChartAt_symm
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (hsmooth : ∀ x ∈ {x | f x = c}, ContDiffAt 𝕜 m f x) (z : ↥{x | f x = c}) :
    ContDiffOn 𝕜 m
      (fun k ↦ (((levelSetChartAt hf hFred hsurj hindex z).symm k : ↥{x | f x = c}) : E))
      (levelSetChartAt hf hFred hsurj hindex z).target := by
  set K := (D z.1).kerModelEquiv (hFred z.1 z.2).finite_ker
    (finrank_ker_eq_of_mem_levelSet hsurj hindex z.2)
  set chart := levelSetChart (hf z.1 z.2) (LinearMap.range_eq_top.2 (hsurj z.1 z.2))
    (hFred z.1 z.2).closedComplemented_ker z.2
  have hpt : ∀ j : Fin n → 𝕜,
      (((levelSetChartAt hf hFred hsurj hindex z).symm j : ↥{x | f x = c}) : E) =
        ((chart.symm (K.symm j) : ↥{x | f x = c}) : E) := fun j ↦ by
    rw [levelSetChartAt_symm_apply]
  refine ContDiffOn.congr ?_ fun j _ ↦ hpt j
  intro k hk
  rw [levelSetChartAt_target] at hk
  set u := (chart.symm (K.symm k) : ↥{x | f x = c})
  have hinner : ContDiffAt 𝕜 m
      (fun j ↦ ((chart.symm j : ↥{x | f x = c}) : E)) (K.symm k) := by
    refine contDiffAt_coe_levelSetChart_symm_of_mem _ _ _ _ hk.1 ?_ (A := D u.1)
      ((hf u.1 u.2).hasFDerivAt) (hsmooth u.1 u.2)
    have hmem := hk.2
    rw [Set.mem_preimage, mem_levelSetImplicitCoordSource_iff, hpt k] at hmem
    exact hmem
  exact (hinner.comp k
    ((K.symm : (Fin n → 𝕜) →L[𝕜] ↥(D z.1).ker).contDiff.contDiffAt)).contDiffWithinAt

/-- **Two preferred charts of a regular level set are smoothly compatible.** The transition map is
the inverse of one chart, followed by the linear reading of a vector of `E` in the model space
that the other chart is. -/
theorem contDiffOn_levelSetChartAt_trans
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (hsmooth : ∀ x ∈ {x | f x = c}, ContDiffAt 𝕜 m f x) (z w : ↥{x | f x = c}) :
    ContDiffOn 𝕜 m
      ((levelSetChartAt hf hFred hsurj hindex z).symm.trans
        (levelSetChartAt hf hFred hsurj hindex w))
      ((levelSetChartAt hf hFred hsurj hindex z).symm.trans
        (levelSetChartAt hf hFred hsurj hindex w)).source := by
  set e := levelSetChartAt hf hFred hsurj hindex z
  set e' := levelSetChartAt hf hFred hsurj hindex w with he'
  -- the linear map reading a vector of `E` in the model space of the chart at `w`
  set Ψ : E →L[𝕜] (Fin n → 𝕜) :=
    ((D w.1).kerModelEquiv (hFred w.1 w.2).finite_ker
      (finrank_ker_eq_of_mem_levelSet hsurj hindex w.2) :
        ↥(D w.1).ker →L[𝕜] (Fin n → 𝕜)).comp
      (Classical.choose (hFred w.1 w.2).closedComplemented_ker) with hΨ
  have hsub : (e.symm.trans e').source ⊆ e.target := fun k hk ↦ hk.1
  have hbase : ContDiffOn 𝕜 m (fun k ↦ ((e.symm k : ↥{x | f x = c}) : E))
      (e.symm.trans e').source :=
    (contDiffOn_coe_levelSetChartAt_symm hf hFred hsurj hindex hsmooth z).mono hsub
  have hconst : ContDiffOn 𝕜 m (fun _ : Fin n → 𝕜 ↦ ((w : ↥{x | f x = c}) : E))
      (e.symm.trans e').source := contDiffOn_const
  have h2 : ContDiffOn 𝕜 m
      (fun k ↦ Ψ (((e.symm k : ↥{x | f x = c}) : E) - ((w : ↥{x | f x = c}) : E)))
      (e.symm.trans e').source := by
    simpa only [Function.comp_def] using Ψ.contDiff.comp_contDiffOn (hbase.sub hconst)
  refine h2.congr fun k _ ↦ ?_
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, he', levelSetChartAt_apply,
    levelSetChart_apply, hΨ, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe]

/-- **A regular level set of a Fredholm map is a `C^m` manifold of dimension its index.** If `f` is
strictly differentiable and `C^m` at every point of the level set `{x | f x = c}`, with surjective
Fredholm derivative of index `n` there, then the charted-space structure of
`TauCeti.levelSetChartedSpace` is a `C^m` atlas.

Together with `TauCeti.levelSetChartedSpace` this is the "the zero set of a Fredholm section is,
at a regular point, a manifold of dimension the index" statement; as there, no global hypothesis
is assumed, so this is a statement about the atlas and not about second countability. -/
theorem isManifold_levelSet
    (hf : ∀ x ∈ {x | f x = c}, HasStrictFDerivAt f (D x) x)
    (hFred : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.IsFredholm (D x))
    (hsurj : ∀ x ∈ {x | f x = c}, Function.Surjective (D x))
    (hindex : ∀ x ∈ {x | f x = c}, ContinuousLinearMap.index (D x) = n)
    (hsmooth : ∀ x ∈ {x | f x = c}, ContDiffAt 𝕜 m f x) :
    letI := levelSetChartedSpace hf hFred hsurj hindex
    IsManifold (modelWithCornersSelf 𝕜 (Fin n → 𝕜)) m ↥{x | f x = c} := by
  let _i := levelSetChartedSpace hf hFred hsurj hindex
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' ↦ ?_
  rw [levelSetChartedSpace_atlas] at he he'
  obtain ⟨z, rfl⟩ := he
  obtain ⟨w, rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id, Function.comp_id, Function.id_comp] using
    contDiffOn_levelSetChartAt_trans hf hFred hsurj hindex hsmooth z w

end TauCeti

end
