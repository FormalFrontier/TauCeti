/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Geometry.Manifold.DerivationBundle
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Tangent vectors as point derivations

A tangent vector acts on smooth scalar-valued functions by directional differentiation. This gives
a canonical linear map from the ordinary tangent space to the algebraic point derivations.

## Main results

* `tangentToPointDerivation`: the point derivation associated to a tangent vector.
* `tangentToPointDerivation_injective`: distinct tangent vectors induce distinct point derivations
  on finite-dimensional Hausdorff real manifolds.
* `PointDerivation.congr_of_eventuallyEq`: on a finite-dimensional Hausdorff real manifold, a point
  derivation depends only on the germ of a smooth function at its basepoint.
* `tangentToPointDerivation_mfderiv`: this association commutes with differentials.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

open scoped ContDiff Derivation Manifold Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A tangent vector acts on smooth functions by directional differentiation. -/
-- Exposure is required for the exported characteristic equation below to unfold this definition
-- under the module system.
@[expose]
def tangentToPointDerivation (x : M) : TangentSpace I x →ₗ[𝕜] PointDerivation I x where
  toFun v :=
    Derivation.mk'
      { toFun := fun f => mvfderiv I f x v
        map_add' := fun f g => by
          -- Unfold the pointed smooth-map addition wrapper: `ContMDiffMap.coe_add` does not match
          -- this type synonym directly.
          change mvfderiv I (⇑f + ⇑g) x v = _
          exact congr($(mvfderiv_add
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
        map_smul' := fun c f => by
          have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
          -- Unfold the pointed smooth-map scalar wrapper: `ContMDiffMap.coe_smul` does not match
          -- this type synonym directly.
          change mvfderiv I ((fun _ : M => c) • ⇑f) x v = c • mvfderiv I f x v
          have h := congr($(mvfderiv_smul hc
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
          calc
            _ = (c • mvfderiv I f x +
                (mvfderiv I (fun _ : M => c) x).smulRight (f x)) v := h
            _ = _ := by simp [mvfderiv_const] }
      fun f g => by
        -- Unfold the pointed smooth-map multiplication wrapper and the evaluation scalar action
        -- (`PointedContMDiffMap.smul_def`): the corresponding `ContMDiffMap.coe_mul` theorem does
        -- not match this type synonym directly.
        change mvfderiv I (⇑f * ⇑g) x v =
          f x * mvfderiv I g x v + g x * mvfderiv I f x v
        exact congr($(mvfderiv_mul
          (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
          (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
  map_add' v w := by
    ext f
    -- Unfold the two bundled linear maps to expose linearity of `mvfderiv` in its tangent vector.
    change mvfderiv I f x (v + w) = _
    exact (mvfderiv I f x).map_add v w
  map_smul' c v := by
    ext f
    -- Unfold the two bundled linear maps to expose scalar linearity of `mvfderiv`.
    change mvfderiv I f x (c • v) = _
    exact (mvfderiv I f x).map_smul c v

/-- The point derivation associated to a tangent vector evaluates a smooth function by its
directional derivative. -/
@[simp]
theorem tangentToPointDerivation_apply (x : M) (v : TangentSpace I x)
    (f : C^∞⟮I, M; 𝕜⟯) : tangentToPointDerivation x v f = mvfderiv I f x v :=
  rfl

/-- On a finite-dimensional Hausdorff real manifold, smooth scalar-valued functions distinguish
tangent vectors. -/
theorem tangentToPointDerivation_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (x : M) :
    Function.Injective (tangentToPointDerivation (I := I) x) := by
  intro v w hvw
  -- The tangent-space type synonym carries no normed-space instance of its own, so expose the
  -- model space before applying the separating-dual theorem.
  change E at v w
  change v = w
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  intro φ
  let b : SmoothBumpFunction I x := Classical.choice inferInstance
  let f : C^∞⟮I, M; ℝ⟯ :=
    ⟨fun y ↦ φ (b y • extChartAt I x y),
      φ.contMDiff.comp (b.contMDiff_smul contMDiffOn_extChartAt)⟩
  have hlocal : (f : M → ℝ) =ᶠ[𝓝 x] φ ∘ extChartAt I x := by
    filter_upwards [b.eventuallyEq_one] with y hy
    simp [f, hy]
  have hfv : mvfderiv I f x v = mvfderiv I f x w := by
    have h := congrArg (fun D ↦ D f) hvw
    -- Unbundle the comparison map after evaluating the two point derivations at `f`.
    change mvfderiv I f x v = mvfderiv I f x w at h
    exact h
  have hderiv (u : TangentSpace I x) : mvfderiv I f x u = φ u := by
    have hφ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) φ (extChartAt I x x) = φ :=
      φ.hasFDerivAt.hasMFDerivAt.mfderiv
    rw [mvfderiv, hlocal.mfderiv_eq,
      mfderiv_comp x φ.mdifferentiableAt
        (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x)),
      hφ, mfderiv_extChartAt_self]
    -- Unwrap the tangent-space synonym and apply the resulting identity linear map; there is no
    -- separate simplification lemma for this final coercion boundary.
    change φ u = φ u
    rfl
  -- The separating-dual goal is stated on the model space after the tangent-space synonym was
  -- exposed above, so return to the corresponding scalar equality before using `hderiv`.
  change φ v = φ w
  rw [← hderiv v, ← hderiv w]
  exact hfv

namespace PointDerivation

/-- A point derivation on a finite-dimensional Hausdorff real manifold depends only on the germ of
a smooth function at its basepoint. -/
theorem congr_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    {x : M} (v : PointDerivation I x) (f g : C^∞⟮I, M; ℝ⟯)
    (hfg : (f : M → ℝ) =ᶠ[𝓝 x] g) :
    v f = v g := by
  have hs : {y | f y = g y} ∈ 𝓝 x := hfg
  obtain ⟨b, -, hb⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) hs).mem_iff.mp hs
  let b' : C^∞⟮I, M; ℝ⟯ := ⟨b, b.contMDiff⟩
  have hprod : b' * (f - g) = 0 := by
    ext y
    -- Unbundle pointwise multiplication and subtraction of smooth maps.
    change b y * (f y - g y) = 0
    by_cases hy : b y = 0
    · simp [hy]
    · have hyb : y ∈ Function.support b := hy
      have hyeq : f y = g y := hb hyb
      simp [hyeq]
  have hx : f x = g x := hfg.eq_of_nhds
  have hleibniz := v.leibniz b' (f - g)
  -- Reinterpret the global smooth-map equality in the pointed type synonym used by `v`.
  have hprodAt : (b' * (f - g) : C^∞⟮I, M; ℝ⟯⟨x⟩) = 0 := hprod
  have hzero : v (b' * (f - g) : C^∞⟮I, M; ℝ⟯⟨x⟩) = 0 := by
    calc
      _ = v 0 := congrArg v hprodAt
      _ = 0 := v.map_zero
  have heq := hzero.symm.trans hleibniz
  -- Unfold the pointed scalar action as evaluation at `x` before simplifying the Leibniz rule.
  change 0 = b x * v (f - g) + (f x - g x) * v b' at heq
  simp [hx] at heq
  have hsub : v (f - g : C^∞⟮I, M; ℝ⟯⟨x⟩) = v f - v g := v.map_sub f g
  exact sub_eq_zero.mp (heq.trans hsub).symm

end PointDerivation

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Sending tangent vectors to point derivations commutes with the differential of a smooth map. -/
theorem tangentToPointDerivation_mfderiv (f : C^∞⟮I, M; I', M'⟯) (x : M)
    (v : TangentSpace I x) :
    tangentToPointDerivation (f x) (mfderiv I I' f x v) =
      𝒅 f x (tangentToPointDerivation x v) := by
  ext g
  -- Unfold the derivation differential and both comparison-map applications before using the
  -- manifold chain rule; their bundled coercions have no separate rewriting lemma.
  change mvfderiv I' g (f x) (mfderiv I I' f x v) =
    tangentToPointDerivation x v (g.comp f)
  rw [tangentToPointDerivation_apply]
  exact (mfderiv_comp_apply x
    (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt v).symm
