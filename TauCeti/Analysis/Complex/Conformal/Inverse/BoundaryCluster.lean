/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.MonotoneExtension
public import TauCeti.Analysis.Complex.Conformal.Biholomorph
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected

/-!
# Boundary injectivity via inverse cluster sets

If `IsPreconnectedApproachAt` (from `TauCeti/Topology/ClusterSet.lean`) holds at
every boundary point of an open image, the cluster-set continuum theorem makes
each boundary fibre of the extension preconnected. The topological core
(`clusterSetOn_invFunOn_eq_boundary_fiber`,
`isPreconnected_boundary_fiber_of_isPreconnected_image_approach`) assumes only
`IsOpen (f '' U)` and continuity of the inverse; the conformal specialization
(`injOn_closedBall_of_isPreconnected_image_approach`) derives these from
injective differentiability.

Adapted from D. Cureton, `sphere-six-complex`,
`SphereSixComplex/Periods/Uniformization/InverseBoundaryCluster.lean` at `895c0a0`
(Apache-2.0); cusp-chart material omitted.

## Main results

* `TauCeti.clusterSetOn_invFunOn_eq_boundary_fiber` — boundary fibre =
  cluster set of the inverse.
* `TauCeti.isPreconnected_boundary_fiber_of_isPreconnected_image_approach`
  — connected approach regions ⇒ preconnected boundary fibres.
* `TauCeti.injOn_closedBall_of_isPreconnected_image_approach` —
  end-to-end reduction to `IsPreconnectedApproachAt`.

## References

* D. Cureton, `sphere-six-complex`,
  `SphereSixComplex/Periods/Uniformization/InverseBoundaryCluster.lean`
  at `895c0a0`, github.com/deancureton/sphere-six-complex.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der
  konformen Abbildung*, Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

open Set Metric Topology Function Filter

namespace TauCeti

/-! ### Cluster-set identification and fibre theorems -/

variable {U : Set ℂ} {f F : ℂ → ℂ} {a : ℂ}

/-- The fibre of a continuous extension over an image-boundary point
is the cluster set of the inverse map at that point. -/
theorem clusterSetOn_invFunOn_eq_boundary_fiber
    (hUo : IsOpen U) (hfo : IsOpen (f '' U))
    (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U))
    (hFf : EqOn F f U)
    (ha : a ∈ frontier (f '' U)) :
    clusterSetOn (invFunOn f U) (f '' U) a =
      {z | z ∈ frontier U ∧ F z = a} := by
  let g : ℂ → ℂ := invFunOn f U
  have hbij : BijOn f U (f '' U) := hfi.bijOn_image
  have hgU : MapsTo g (f '' U) U :=
    hbij.surjOn.mapsTo_invFunOn
  have hleft : LeftInvOn g f U := hbij.invOn_invFunOn.1
  have hright : RightInvOn g f (f '' U) :=
    hbij.invOn_invFunOn.2
  ext z
  constructor
  · intro hz
    have hz' :
        MapClusterPt z (nhdsWithin a (f '' U)) g :=
      mem_clusterSetOn_iff.mp hz
    have hzcl : z ∈ closure U :=
      closure_mono
        (invFunOn_image_image_subset f U)
        (clusterSetOn_subset_closure_image hz)
    let l : Filter ℂ := nhdsWithin a (f '' U)
    have hmap_closure :
        map g l ≤ principal (closure U) := by
      rw [le_principal_iff, mem_map]
      exact mem_of_superset self_mem_nhdsWithin
        fun y hy ↦ subset_closure (hgU hy)
    have hF_tendsto :
        Tendsto F (nhds z ⊓ map g l) (nhds (F z)) := by
      apply (hFc z hzcl).mono_left
      rw [nhdsWithin]
      exact inf_le_inf le_rfl hmap_closure
    have hzF : MapClusterPt (F z) l (F ∘ g) := by
      exact hz'.tendsto_comp' hF_tendsto
    have hFg : F ∘ g =ᶠ[l] id := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [Function.comp_apply, id_eq]
      rw [hFf (hgU hy), hright hy]
    have hzid : MapClusterPt (F z) l id :=
      hzF.congrFun hFg
    have hlim : Tendsto id l (nhds a) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have : NeBot l :=
      mem_closure_iff_nhdsWithin_neBot.mp
        (frontier_subset_closure ha)
    have hFa : F z = a := by
      have : NeBot (nhds (F z) ⊓ l) := hzid.clusterPt
      exact tendsto_nhds_unique
        (tendsto_id.mono_left inf_le_left)
        (hlim.mono_left inf_le_right)
    have hzU : z ∉ U := by
      intro hzU
      have ha_image : a ∈ f '' U :=
        ⟨z, hzU, by rw [← hFa, hFf hzU]⟩
      exact (hfo.frontier_eq.subset ha).2 ha_image
    refine ⟨?_, hFa⟩
    rw [hUo.frontier_eq]
    exact ⟨hzcl, hzU⟩
  · rintro ⟨hzfr, hFza⟩
    let p : Filter ℂ := nhdsWithin z U
    have : NeBot p :=
      mem_closure_iff_nhdsWithin_neBot.mp
        (frontier_subset_closure hzfr)
    have hgf : g ∘ f =ᶠ[p] id := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hleft hx
    have hzcomp : MapClusterPt z p (g ∘ f) :=
      ((ClusterPt.of_le_nhds
        nhdsWithin_le_nhds).mapClusterPt_id).congrFun
        hgf.symm
    have hftend_nhds : Tendsto f p (nhds a) := by
      have hFtend : Tendsto F p (nhds (F z)) :=
        (hFc z (frontier_subset_closure hzfr)).mono_left
          (nhdsWithin_mono z subset_closure)
      have hfeq : f =ᶠ[p] F := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (hFf hx).symm
      simpa only [hFza] using
        (tendsto_congr' hfeq).mpr hFtend
    have hftend :
        Tendsto f p (nhdsWithin a (f '' U)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        f hftend_nhds
        (mem_of_superset self_mem_nhdsWithin
          fun x hx ↦ ⟨x, hx, rfl⟩)
    exact mem_clusterSetOn_iff.mpr
      (MapClusterPt.of_comp hftend hzcomp)

/-- If the image domain is locally preconnected from within at a
boundary point, the fibre of a continuous extension over that point
is preconnected. -/
theorem
    isPreconnected_boundary_fiber_of_isPreconnected_image_approach
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfo : IsOpen (f '' U))
    (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U))
    (hFf : EqOn F f U)
    (hgc : ContinuousOn (invFunOn f U) (f '' U))
    (ha : a ∈ frontier (f '' U))
    (hloc : IsPreconnectedApproachAt (f '' U) a) :
    IsPreconnected {z : frontier U | F z = a} := by
  let g : ℂ → ℂ := invFunOn f U
  have hgU : MapsTo g (f '' U) U :=
    hfi.bijOn_image.surjOn.mapsTo_invFunOn
  have hcluster :
      IsPreconnected
        (clusterSetOn g (f '' U) a) :=
    isPreconnected_clusterSetOn
      hUb.isCompact_closure
      (fun z hz ↦ subset_closure (hgU hz)) hgc (isPreconnectedApproachAt_def.mp hloc)
  rw [← IsInducing.subtypeVal.isPreconnected_image]
  have himage :
      Subtype.val '' {z : frontier U | F z = a} =
        {z | z ∈ frontier U ∧ F z = a} := by
    ext z
    simp [and_comm]
  rw [himage,
    ← clusterSetOn_invFunOn_eq_boundary_fiber
      hUo hfo hfi hFc hFf ha]
  exact hcluster

/-- A local connected-approach basis at every image-boundary point
makes every fibre of the boundary restriction preconnected. -/
theorem isPreconnected_frontier_fiber_of_image_approach
    (hUo : IsOpen U) (hUb : Bornology.IsBounded U)
    (hfo : IsOpen (f '' U)) (hfi : InjOn f U)
    (hFc : ContinuousOn F (closure U))
    (hFf : EqOn F f U)
    (hgc : ContinuousOn (invFunOn f U) (f '' U))
    (hboundary : F '' frontier U ⊆ frontier (f '' U))
    (hloc : ∀ a ∈ frontier (f '' U),
      IsPreconnectedApproachAt (f '' U) a) :
    ∀ a, IsPreconnected {z : frontier U | F z = a} := by
  intro a
  by_cases ha : a ∈ frontier (f '' U)
  · exact
      isPreconnected_boundary_fiber_of_isPreconnected_image_approach
        hUo hUb hfo hfi hFc hFf hgc ha (hloc a ha)
  · have hempty :
        {z : frontier U | F z = a} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      intro hz
      exact ha (hboundary ⟨z, z.2, hz⟩)
    rw [hempty]
    exact isPreconnected_empty

variable {c : ℂ} {r : ℝ}

/-- The preceding inverse-cluster reduction, specialized to a disc
and fed to Tau Ceti's monotone-extension theorem. -/
theorem injOn_closedBall_of_isPreconnected_image_approach
    (hr : 0 < r)
    (hfd : DifferentiableOn ℂ f (ball c r))
    (hfi : InjOn f (ball c r))
    (hFc : ContinuousOn F (closedBall c r))
    (hFf : EqOn F f (ball c r))
    (hloc : ∀ a ∈ frontier (f '' ball c r),
      IsPreconnectedApproachAt (f '' ball c r) a) :
    InjOn F (closedBall c r) := by
  have hcl : closure (ball c r) = closedBall c r :=
    closure_ball c hr.ne'
  have hfo : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hfd hfi
  let e := DifferentiableOn.toOpenPartialHomeomorph hfd isOpen_ball hfi
  have hgc : ContinuousOn (invFunOn f (ball c r)) (f '' ball c r) := by
    simpa only [e,
      DifferentiableOn.toOpenPartialHomeomorph_target,
      DifferentiableOn.toOpenPartialHomeomorph_coe_symm]
      using e.continuousOn_symm
  have hpre :
      ∀ a,
        IsPreconnected {z : sphere c r | F z = a} := by
    intro a
    have hboundary : F '' frontier (ball c r) ⊆ frontier (f '' ball c r) :=
      image_frontier_subset_frontier_image isOpen_ball hfd hfi (hcl.symm ▸ hFc) hFf
    have h :=
      isPreconnected_frontier_fiber_of_image_approach
        isOpen_ball isBounded_ball hfo hfi
        (hcl.symm ▸ hFc) hFf hgc hboundary hloc a
    rw [frontier_ball c hr.ne'] at h
    exact h
  have hfdF : DifferentiableOn ℂ F (ball c r) :=
    hfd.congr fun z hz ↦ hFf hz
  have hfiF : InjOn F (ball c r) := hfi.congr hFf.symm
  exact injOn_closedBall_of_isPreconnected_boundary_fiber
    hr hFc hfdF hfiF hpre

end TauCeti
