/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Riemannian metrics on open submanifolds

This file restricts a smooth Riemannian metric to an open submanifold. Mathlib models the tangent
space of a manifold on the model vector space itself, so the restricted metric is pointwise the
ambient metric; the content is that this family is smooth for the inherited manifold and tangent
bundle structures.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.restrictOpen`: restriction of a smooth Riemannian metric to an
  open submanifold.

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

/-- Restrict a Riemannian metric on a tangent bundle to an open submanifold. -/
noncomputable def restrictOpen
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    RiemannianMetric (fun x : U ↦ TangentSpace I x) where
  inner x :=
    let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
    e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x.1)
  symm x v w := by
    simpa only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply,
      TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using g.symm x.1 v w
  pos x v hv := by
    simpa only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply,
      TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using g.pos x.1 v hv
  continuousAt x := by
    let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
    have h := (g.continuousAt x.1).comp_of_eq e.continuousAt (map_zero e)
    apply h.congr_of_eventuallyEq
    filter_upwards with v
    rfl
  isVonNBounded x := by
    let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
    let restrictedInner :=
      e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x.1)
    change Bornology.IsVonNBounded ℝ {v | restrictedInner v v < 1}
    have heq : {v | restrictedInner v v < 1} =
        e.symm.toContinuousLinearMap '' {v | g.inner x.1 v v < 1} := by
      ext v
      change restrictedInner v v < 1 ↔ v ∈ e.symm '' {v | g.inner x.1 v v < 1}
      rw [show v ∈ e.symm '' {v | g.inner x.1 v v < 1} ↔
          e v ∈ {v | g.inner x.1 v v < 1} from
        Set.mem_image_equiv (f := e.symm.toEquiv)]
      simp only [restrictedInner, ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply, Set.mem_ofPred_eq]
    rw [heq]
    exact (g.isVonNBounded x.1).image e.symm.toContinuousLinearMap

/-- Restricting a Riemannian metric evaluates the ambient metric through the canonical tangent-space
identification. -/
@[simp]
theorem restrictOpen_inner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpen U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  rfl

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [IsManifold I 1 M]

/-- Restrict a smooth Riemannian metric on a manifold to an open submanifold. -/
noncomputable def restrictOpen
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) where
  inner x :=
    let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
    e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x.1)
  symm x v w := by
    simpa only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply,
      TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using g.symm x.1 v w
  pos x v hv := by
    simpa only [ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
      ContinuousLinearEquiv.refl_apply,
      TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using g.pos x.1 v hv
  isVonNBounded x := by
    let e := TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x
    let restrictedInner :=
      e.symm.arrowCongr (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)) (g.inner x.1)
    change Bornology.IsVonNBounded ℝ {v | restrictedInner v v < 1}
    have heq : {v | restrictedInner v v < 1} =
        e.symm.toContinuousLinearMap '' {v | g.inner x.1 v v < 1} := by
      ext v
      change restrictedInner v v < 1 ↔ v ∈ e.symm '' {v | g.inner x.1 v v < 1}
      rw [show v ∈ e.symm '' {v | g.inner x.1 v v < 1} ↔
          e v ∈ {v | g.inner x.1 v v < 1} from
        Set.mem_image_equiv (f := e.symm.toEquiv)]
      simp only [restrictedInner, ContinuousLinearEquiv.arrowCongr_apply,
        ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_apply, Set.mem_ofPred_eq]
    rw [heq]
    exact (g.isVonNBounded x.1).image e.symm.toContinuousLinearMap
  contMDiff x := by
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
      TauCeti.Manifold.tangentSpaceOpenEquiv_trivializationAt_symmL_eventuallyEq
        (I := I) x] with y hyU hyM hsymm
    have hyU' : y ∈ (chartAt H x).source := by simpa using hyU
    have hyM' : (y : M) ∈ (chartAt H (x : M)).source := by exact hyM
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
      ContinuousLinearEquiv.arrowCongr_apply,
      ite_true]
    simp [TauCeti.Manifold.tangentSpaceOpenEquiv_apply]
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
    simpa [TauCeti.Manifold.tangentSpaceOpenEquiv_apply] using
      congrArg (fun p : TangentSpace I (y : M) × TangentSpace I (y : M) ↦
        g.inner (y : M) p.1 p.2) hp

omit [IsManifold I n M] in
/-- Restricting a smooth Riemannian metric evaluates the ambient metric through the canonical
tangent-space identification. -/
@[simp]
theorem restrictOpen_inner
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (U : Opens M)
    (x : U) (v w : TangentSpace I x) :
    (g.restrictOpen U).inner x v w =
      g.inner (x : M) (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (TauCeti.Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  rfl

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [IsManifold I 1 M]

private noncomputable def ambientContMDiffRiemannianMetric
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] :
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) where
  inner := RiemannianBundle.g.inner
  symm := RiemannianBundle.g.symm
  pos := RiemannianBundle.g.pos
  isVonNBounded := RiemannianBundle.g.isVonNBounded
  contMDiff := by
    obtain ⟨g, hg, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff
        (IB := I) (n := n) (F := E) (E := fun x : M ↦ TangentSpace I x)
    convert hg using 1
    funext x
    congr 1
    ext v w
    exact hinner x v w

/-- The smooth Riemannian metric on an open submanifold obtained by restricting the ambient
metric. -/
noncomputable def riemannianMetricOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    ContMDiffRiemannianMetric I n E (fun x : U ↦ TangentSpace I x) :=
  (ambientContMDiffRiemannianMetric (I := I) (n := n)).restrictOpen U

/-- An open submanifold inherits the ambient smooth Riemannian bundle. -/
noncomputable scoped instance instRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) :
    RiemannianBundle (fun x : U ↦ TangentSpace I x) :=
  ⟨RiemannianBundle.g.restrictOpen U⟩

/-- The restricted Riemannian bundle is as smooth as the ambient one. -/
noncomputable scoped instance instIsContMDiffRiemannianBundleOpen
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] (U : Opens M) :
    IsContMDiffRiemannianBundle I n E (fun x : U ↦ TangentSpace I x) := by
  let g := riemannianMetricOpen (I := I) (n := n) U
  exact ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩

omit [IsManifold I n M] in
/-- The restricted Riemannian metric is the ambient metric under the canonical identification of
tangent spaces. -/
@[simp]
theorem riemannianMetricOpen_inner
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
    (U : Opens M) (x : U) (v w : TangentSpace I x) :
    (riemannianMetricOpen (I := I) (n := n) U).inner x v w =
      RiemannianBundle.g.inner (x : M)
        (Manifold.tangentSpaceOpenEquiv (I := I) x v)
        (Manifold.tangentSpaceOpenEquiv (I := I) x w) := by
  exact Bundle.ContMDiffRiemannianMetric.restrictOpen_inner
    (ambientContMDiffRiemannianMetric (I := I) (n := n)) U x v w

end TauCeti
