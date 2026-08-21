/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Riemannian metrics on open submanifolds

This file restricts a `C^n` Riemannian metric to an open submanifold. Mathlib models the tangent
space of a manifold on the model vector space itself, so the restricted metric is pointwise the
ambient metric; the content is that this family is `C^n` for the inherited manifold and tangent
bundle structures.

## Main definitions

* `Bundle.RiemannianMetric.restrictOpenTangentSpace`: restriction of a fibrewise Riemannian metric.
* `Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace`: restriction of a `C^n` Riemannian
  metric.
* `TauCeti.Manifold.contMDiffRiemannianMetricOpen`: the ambient instance metric restricted to an
  open submanifold.
* `TauCeti.Manifold.instRiemannianBundleOpen`,
  `TauCeti.Manifold.instIsContinuousRiemannianBundleOpen`, and
  `TauCeti.Manifold.instIsContMDiffRiemannianBundleOpen`: the corresponding scoped instances.

The three instances are in the `TauCeti` scope; use `open scoped TauCeti` to install them. In
particular, under the usual separation hypotheses this makes `EMetricSpace.ofRiemannianMetric`
available on the open submanifold.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Restriction to open submanifolds".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 1, §2.
-/

public section

open Bundle Filter Manifold TopologicalSpace
open scoped Bundle ContDiff Manifold Topology

noncomputable section

namespace Bundle.RiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private noncomputable def restrictedTangentInner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) {U : Opens M} (x : U) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
  e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x.1)

private theorem restrictedTangentInner_apply
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) {U : Opens M}
    (x : U) (v w : TangentSpace I x) :
    restrictedTangentInner g x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  rfl

/-- Restrict a Riemannian metric on a tangent bundle to an open submanifold. -/
noncomputable def restrictOpenTangentSpace
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    RiemannianMetric (fun x : U ↦ TangentSpace I x) where
  inner := restrictedTangentInner g
  symm x v w := by
    rw [restrictedTangentInner_apply, restrictedTangentInner_apply]
    exact g.symm x.1 _ _
  pos x v hv := by
    rw [restrictedTangentInner_apply]
    exact g.pos x.1 _
      ((TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).toLinearEquiv.map_ne_zero_iff.mpr hv)
  continuousAt x := by
    have h : ContinuousAt (fun v : TangentSpace I x ↦
        g.inner x.1 (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
          (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)) 0 :=
      (g.continuousAt x.1).comp_of_eq
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).continuousAt (map_zero _)
    simpa only [restrictedTangentInner_apply] using h
  isVonNBounded x := by
    have heq : {v | restrictedTangentInner g x v v < 1} =
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap ''
          {v | g.inner x.1 v v < 1} := by
      simp only [restrictedTangentInner_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.image_symm_eq_preimage, Set.preimage_ofPred_eq]
    rw [heq]
    exact (g.isVonNBounded x.1).image
      (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap

/-- Restricting a Riemannian metric evaluates the ambient metric through the canonical tangent-space
identification. -/
@[simp]
theorem restrictOpenTangentSpace_inner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  rfl

/-- The restricted metric is the pullback of the ambient metric along the differential of the
open-submanifold inclusion. -/
theorem restrictOpenTangentSpace_inner_mfderiv_subtype_val
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w) := by
  rw [TauCeti.Manifold.mfderiv_subtype_val]
  exact g.restrictOpenTangentSpace_inner U x v w

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [IsManifold I 1 M]

/-- Restrict a `C^n` Riemannian metric on a manifold to an open submanifold. -/
noncomputable def restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) :=
  { g.toRiemannianMetric.restrictOpenTangentSpace U with
  contMDiff x := by
    -- Pull ambient `C^n` regularity back along the inclusion and compare the inherited and ambient
    -- tangent-bundle coordinates on a common neighbourhood of `x`.
    rw [contMDiffAt_section]
    have h := g.contMDiff.contMDiffAt.comp x
      (contMDiff_subtype_val (I := I) (U := U)).contMDiffAt
    rw [contMDiffAt_totalSpace] at h
    apply h.2.congr_of_eventuallyEq
    filter_upwards [
      (trivializationAt E (TangentSpace I : U → Type _) x).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : U → Type _) x),
      continuousAt_subtype_val.eventually
        ((trivializationAt E (TangentSpace I : M → Type _) x.1).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x.1)),
      TauCeti.Manifold.eventually_tangentSpaceOpenEquiv_symmL_trivializationAt_eq
        (I := I) x] with y hyU hyM hsymm
    have hyU' : y ∈ (chartAt H x).source := by simpa using hyU
    have hyM' : (y : M) ∈ (chartAt H (x : M)).source := hyM
    have hyUhom : y ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z : U ↦ TangentSpace I z →L[ℝ] ℝ) x).baseSet := by
      simpa using hyU'
    have hyMhom : (y : M) ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) (x : M)).baseSet := by
      simpa using hyM'
    ext v w
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
      Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply,
      Trivialization.linearMapAt_apply,
      hyU, hyUhom, hyMhom, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ite_true]
    rw [Bundle.RiemannianMetric.restrictOpenTangentSpace_inner]
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet,
      Set.mem_univ, ite_true, Trivial.trivialization_apply,
      Bundle.ContMDiffRiemannianMetric.toRiemannianMetric,
      Bundle.ContMDiffRiemannianMetric.toContinuousRiemannianMetric,
      Bundle.ContinuousRiemannianMetric.toRiemannianMetric]
    have hsymm' (z : E) :
        TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y
            ((trivializationAt E (TangentSpace I : U → Type _) x).symm y z) =
          (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL ℝ (y : M) z := by
      simpa only [Trivialization.symmL_apply _ hyU] using hsymm z
    have hp :
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y
            ((trivializationAt E (TangentSpace I : U → Type _) x).symm y v),
          TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) y
            ((trivializationAt E (TangentSpace I : U → Type _) x).symm y w)) =
        ((trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL ℝ (y : M) v,
          (trivializationAt E (TangentSpace I : M → Type _) (x : M)).symmL ℝ (y : M) w) :=
      Prod.ext (hsymm' v) (hsymm' w)
    simpa only using
      congrArg (fun p : TangentSpace I (y : M) × TangentSpace I (y : M) ↦
        g.inner (y : M) p.1 p.2) hp
  }

omit [IsManifold I n M] in
/-- Restricting a `C^n` Riemannian metric evaluates the ambient metric through the canonical
tangent-space identification. -/
@[simp]
theorem restrictOpenTangentSpace_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpenTangentSpace U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  exact Bundle.RiemannianMetric.restrictOpenTangentSpace_inner g.toRiemannianMetric U x v w

omit [IsManifold I n M] in
/-- Forgetting `C^n` regularity after restricting a metric gives its fibrewise restriction. -/
@[simp]
theorem restrictOpenTangentSpace_toRiemannianMetric
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    (g.restrictOpenTangentSpace U).toRiemannianMetric =
      g.toRiemannianMetric.restrictOpenTangentSpace U := by
  rfl

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [IsManifold I 1 M]

/-- The `C^n` Riemannian metric on an open submanifold obtained by restricting the ambient
metric. -/
noncomputable def contMDiffRiemannianMetricOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) :=
  (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := n) (F := E) (V := fun x : M ↦ TangentSpace I x)).restrictOpenTangentSpace U

omit [IsManifold I n M] in
/-- The restricted Riemannian metric is the ambient metric under the canonical identification of
tangent spaces. -/
@[simp]
theorem contMDiffRiemannianMetricOpen_inner
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) (x : U) (v w : TangentSpace I x) :
    (contMDiffRiemannianMetricOpen (I := I) (n := n) U).inner x v w =
      RiemannianBundle.g.inner (x : M)
        (tangentSpaceOpenEquiv (I := I) x v)
        (tangentSpaceOpenEquiv (I := I) x w) := by
  simpa only [contMDiffRiemannianMetricOpen,
    Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner] using
    Bundle.ContMDiffRiemannianMetric.restrictOpenTangentSpace_inner
    (Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
      (IB := I) (n := n) (F := E) (V := fun x : M ↦ TangentSpace I x)) U x v w

end TauCeti.Manifold

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [IsManifold I 1 M]

omit [IsManifold I n M] [IsManifold I 1 M] in
/-- An open submanifold inherits the ambient Riemannian bundle (fibrewise inner product). -/
@[instance_reducible]
noncomputable def Manifold.instRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) :
  RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
  ⟨RiemannianBundle.g.restrictOpenTangentSpace U⟩

scoped[TauCeti] attribute [instance] Manifold.instRiemannianBundleOpen

omit [IsManifold I n M] in
/-- The restricted Riemannian bundle is continuous whenever the ambient bundle is continuous. -/
theorem Manifold.instIsContinuousRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsContinuousRiemannianBundle E (fun x : U ↦ TangentSpace I x) := by
  let _ : IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  let g := Manifold.contMDiffRiemannianMetricOpen (I := I) (n := 0) U
  exact ⟨g.inner, g.contMDiff.continuous, by
    intro x v w
    exact (Bundle.RiemannianMetric.restrictOpenTangentSpace_inner
      RiemannianBundle.g U x v w).trans
        (Manifold.contMDiffRiemannianMetricOpen_inner (I := I) (n := 0) U x v w).symm⟩

scoped[TauCeti] attribute [instance] Manifold.instIsContinuousRiemannianBundleOpen

omit [IsManifold I n M] in
/-- The restricted Riemannian bundle is as `C^n` as the ambient one. -/
theorem Manifold.instIsContMDiffRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsContMDiffRiemannianBundle I n E (fun x : U ↦ TangentSpace I x) := by
  let g := Manifold.contMDiffRiemannianMetricOpen (I := I) (n := n) U
  exact ⟨g.inner, g.contMDiff, by
    intro x v w
    exact (Bundle.RiemannianMetric.restrictOpenTangentSpace_inner
      RiemannianBundle.g U x v w).trans
        (Manifold.contMDiffRiemannianMetricOpen_inner (I := I) (n := n) U x v w).symm⟩

scoped[TauCeti] attribute [instance] Manifold.instIsContMDiffRiemannianBundleOpen

namespace Manifold

omit [IsManifold I n M] [IsManifold I 1 M] in
/-- The metric installed on an open submanifold is the fibrewise restriction of the ambient
metric. -/
@[simp]
theorem riemannianBundleOpen_g
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    letI := instRiemannianBundleOpen (I := I) U
    RiemannianBundle.g (E := fun x : U ↦ TangentSpace I x) =
      (RiemannianBundle.g (E := fun x : M ↦ TangentSpace I x)).restrictOpenTangentSpace U := by
  rfl

omit [IsManifold I n M] [IsManifold I 1 M] in
/-- The inner product installed on an open submanifold is the ambient inner product under the
canonical tangent-space identification. -/
@[simp]
theorem inner_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    inner ℝ v w = RiemannianBundle.g.inner (x : M)
      (tangentSpaceOpenEquiv (I := I) x v) (tangentSpaceOpenEquiv (I := I) x w) := by
  exact Bundle.RiemannianMetric.restrictOpenTangentSpace_inner RiemannianBundle.g U x v w

omit [IsManifold I n M] [IsManifold I 1 M] in
/-- The norm installed on an open submanifold is the ambient Riemannian norm under the canonical
tangent-space identification. -/
@[simp]
theorem norm_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    ‖v‖ = ‖tangentSpaceOpenEquiv (I := I) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_open]
  congr 1

omit [IsManifold I n M] [IsManifold I 1 M] in
/-- The extended norm installed on an open submanifold is the ambient Riemannian extended norm
under the canonical tangent-space identification. -/
@[simp]
theorem enorm_tangentSpace_open
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)] (U : Opens M)
    (x : U) (v : TangentSpace I x) :
    letI := instRiemannianBundleOpen (I := I) U
    ‖v‖ₑ = ‖tangentSpaceOpenEquiv (I := I) x v‖ₑ := by
  simp only [enorm, nnnorm, norm_tangentSpace_open]

end TauCeti.Manifold
