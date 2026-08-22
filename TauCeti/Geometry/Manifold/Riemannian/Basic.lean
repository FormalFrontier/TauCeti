/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Basic Riemannian bundle constructions

This file provides conversions between Mathlib's Riemannian bundle classes and bundled
Riemannian metrics.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle`: package the metric of a
  `C^n` Riemannian bundle.
* `Bundle.ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner`: the packaged metric is
  the bundle's inner product.
* `Bundle.IsContinuousRiemannianBundle.toIsContMDiffZero`: view a continuous Riemannian bundle as
  a `C^0` Riemannian bundle.
-/

public section

open Bundle Manifold
open scoped Bundle ContDiff Manifold

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, TopologicalSpace (V b)] [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  [∀ b, IsTopologicalAddGroup (V b)] [∀ b, ContinuousConstSMul ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Package the metric of a `C^n` Riemannian bundle as a `C^n` Riemannian metric. -/
noncomputable def ofIsContMDiffRiemannianBundle
    [RiemannianBundle V] [IsContMDiffRiemannianBundle IB n F V] :
    ContMDiffRiemannianMetric IB n F V where
  inner := RiemannianBundle.g.inner
  symm := RiemannianBundle.g.symm
  pos := RiemannianBundle.g.pos
  isVonNBounded := RiemannianBundle.g.isVonNBounded
  contMDiff := by
    obtain ⟨g, hg, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := IB) (n := n) (F := F) (E := V)
    convert hg using 1
    funext x
    congr 1
    ext v w
    exact hinner x v w

/-- The Riemannian metric packaged from a `C^n` Riemannian bundle is its inner product. -/
@[simp]
theorem ofIsContMDiffRiemannianBundle_inner
    [RiemannianBundle V] [IsContMDiffRiemannianBundle IB n F V]
    (x : B) (v w : V x) :
    (ofIsContMDiffRiemannianBundle (IB := IB) (n := n) (F := F) (V := V)).inner x v w =
      RiemannianBundle.g.inner x v w := by
  rfl

end Bundle.ContMDiffRiemannianMetric

namespace Bundle.IsContinuousRiemannianBundle

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- A continuous Riemannian bundle is a `C^0` Riemannian bundle. This is deliberately a theorem,
not an instance, because Mathlib avoids the corresponding inference path. -/
theorem toIsContMDiffZero [IsContinuousRiemannianBundle F V] :
    IsContMDiffRiemannianBundle IB 0 F V := by
  obtain ⟨g, hg, hinner⟩ := IsContinuousRiemannianBundle.exists_continuous (F := F) (E := V)
  exact ⟨g, contMDiff_zero_iff.mpr hg, hinner⟩

end Bundle.IsContinuousRiemannianBundle
