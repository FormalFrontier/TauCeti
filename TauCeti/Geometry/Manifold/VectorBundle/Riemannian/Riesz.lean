/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram

/-!
# Smoothness of the fibrewise Riesz dual

This file proves that the inverse of the fibrewise Fréchet–Riesz equivalence of a smooth
finite-dimensional Riemannian bundle carries smoothly varying covectors to a smooth section.
In a chart-local frame, its coefficients are obtained by multiplying the covector evaluations by
the inverse Gram matrix.

The result is the linear-algebraic input needed to construct the Levi–Civita connection from the
Koszul functional: the Koszul formula first produces a covector in the last argument, and the
fibrewise Riesz dual turns it into the value of the connection.

The coordinate formula and smoothness argument are adapted from stages 6–7 of the Apache-2.0
Poincare-Conjecture source file
`DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. The source uses an explicit metric and manually
trivializes the resulting section. Here Mathlib's fibrewise `InnerProductSpace.toDual` and local
frame smoothness API replace those constructions.

## Main results

* `Riemannian.Tensor.rieszDual` is the fibrewise Riesz dual supplied by the canonical metric.
* `Riemannian.Tensor.rieszDual_eq_sum_chartLocalFrame` gives the inverse-Gram-matrix coordinate
  formula for the Riesz dual.
* `Riemannian.Tensor.contMDiffOn_rieszDual` proves smoothness on a chart domain from smoothness
  of the covector's evaluations on the chart-local frame.
* `Riemannian.Tensor.contMDiffAt_rieszDual` is the corresponding pointwise criterion.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
* Poincare-Conjecture, `DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, stages 6–7,
  revision `24f32e4d600878bfaac6bc2f2f9324175571c321` (Apache-2.0).

-/

noncomputable section
public section

open Bundle FiberBundle Manifold Set
open scoped ContDiff Manifold Matrix Topology

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Riesz dual of a continuous linear functional on a tangent fibre, with respect to the
inner product supplied by the canonical Riemannian bundle instance. -/
def rieszDual {x : M} (φ : TangentSpace I x →L[ℝ] ℝ) : TangentSpace I x := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  let _ := FiniteDimensional.complete ℝ (TangentSpace I x)
  exact (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm φ

/-- The Riesz dual represents its functional by the fibre inner product. -/
@[simp]
theorem inner_rieszDual {x : M} (φ : TangentSpace I x →L[ℝ] ℝ)
    (v : TangentSpace I x) : inner ℝ (rieszDual (I := I) φ) v = φ v := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  let _ := FiniteDimensional.complete ℝ (TangentSpace I x)
  exact InnerProductSpace.toDual_symm_apply

/-- A tangent vector is the Riesz dual of `φ` exactly when its inner product against every
vector is the value of `φ` there. -/
theorem eq_rieszDual_iff_inner_eq {x : M} {v : TangentSpace I x}
    {φ : TangentSpace I x →L[ℝ] ℝ} :
    v = rieszDual (I := I) φ ↔ ∀ w, inner ℝ v w = φ w := by
  refine ⟨fun h w ↦ h ▸ inner_rieszDual (I := I) φ w, fun h ↦ ?_⟩
  exact ext_inner_right ℝ fun w ↦ (h w).trans (inner_rieszDual (I := I) φ w).symm

/-- The Riesz dual of the zero functional is zero. -/
@[simp]
theorem rieszDual_zero {x : M} :
    rieszDual (I := I) (0 : TangentSpace I x →L[ℝ] ℝ) = 0 := by
  symm
  rw [eq_rieszDual_iff_inner_eq]
  simp

/-- The Riesz dual is additive in the functional. -/
@[simp]
theorem rieszDual_add {x : M} (φ ψ : TangentSpace I x →L[ℝ] ℝ) :
    rieszDual (I := I) (φ + ψ) = rieszDual (I := I) φ + rieszDual (I := I) ψ := by
  rw [eq_comm, eq_rieszDual_iff_inner_eq]
  simp [inner_add_left]

/-- The Riesz dual commutes with real scalar multiplication. -/
@[simp]
theorem rieszDual_smul {x : M} (c : ℝ) (φ : TangentSpace I x →L[ℝ] ℝ) :
    rieszDual (I := I) (c • φ) = c • rieszDual (I := I) φ := by
  rw [eq_comm, eq_rieszDual_iff_inner_eq]
  simp [real_inner_smul_left]

/-- The coordinate formula for the fibrewise Riesz dual in a chart-local frame. Its coefficient
vector is the inverse Gram matrix applied to the evaluations of the covector on the frame. -/
theorem rieszDual_eq_sum_chartLocalFrame (a : M) {x : M}
    (hx : x ∈ (chartAt H a).source) (φ : TangentSpace I x →L[ℝ] ℝ) :
    rieszDual (I := I) φ =
      ∑ i, ((chartInvGramMatrix (I := I) a x *ᵥ
        fun j ↦ φ (chartLocalFrame (I := I) a j x)) i) •
          chartLocalFrame (I := I) a i x := by
  let G := chartGramMatrix (I := I) a x
  let Ginv := chartInvGramMatrix (I := I) a x
  let v : Fin (Module.finrank ℝ E) → ℝ := fun j ↦ φ (chartLocalFrame (I := I) a j x)
  let e := (trivializationAt E (TangentSpace I) a).basisAt (Module.finBasis ℝ E)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  apply InnerProductSpace.ext_inner_right_basis e
  intro k
  symm
  rw [inner_rieszDual]
  calc
    inner ℝ (∑ i, (Ginv *ᵥ v) i • chartLocalFrame (I := I) a i x) (e k) =
        (G *ᵥ (Ginv *ᵥ v)) k := by
      simp only [sum_inner, real_inner_smul_left, Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      rw [show e k = chartLocalFrame (I := I) a k x by
        simpa only [e] using (chartLocalFrame_apply_of_mem_chart_source (I := I) a hx k).symm]
      have hHermitian := (posDef_chartGramMatrix (I := I) a
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).isHermitian
      rw [show inner ℝ (chartLocalFrame (I := I) a i x)
          (chartLocalFrame (I := I) a k x) = G i k by
        exact (chartGramMatrix_apply (I := I) a x i k).symm]
      rw [show G i k = G k i by
        simpa only [star_trivial] using hHermitian.apply k i]
      ring
    _ = ((G * Ginv) *ᵥ v) k := by rw [Matrix.mulVec_mulVec]
    _ = v k := by
      rw [show G * Ginv = 1 by
        exact chartGramMatrix_mul_chartInvGramMatrix (I := I) a hx]
      exact congrFun (Matrix.one_mulVec v) k
    _ = φ (e k) := by
      rw [show e k = chartLocalFrame (I := I) a k x by
        simpa only [e] using (chartLocalFrame_apply_of_mem_chart_source (I := I) a hx k).symm]

section Smooth

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- A field of covectors has a smooth fibrewise Riesz dual on a chart source if its evaluations
on the chart-local frame are smooth there. -/
theorem contMDiffOn_rieszDual (a : M)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) n (fun y ↦ Φ y (chartLocalFrame (I := I) a j y))
        (chartAt H a).source) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y : M ↦ TotalSpace.mk' E y
        (rieszDual (I := I) (Φ y)))
      (chartAt H a).source := by
  let c : Fin (Module.finrank ℝ E) → M → ℝ := fun i y ↦
    ∑ j, chartInvGramMatrix (I := I) a y i j *
      Φ y (chartLocalFrame (I := I) a j y)
  have hc (i : Fin (Module.finrank ℝ E)) :
      ContMDiffOn I 𝓘(ℝ) n (c i) (chartAt H a).source := by
    dsimp only [c]
    exact contMDiffOn_finsetSum fun j _ ↦
      (show ContMDiffOn I 𝓘(ℝ) n
          (fun y ↦ chartInvGramMatrix (I := I) a y i j) (chartAt H a).source by
        simpa only [TangentBundle.trivializationAt_baseSet] using
          (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) a i j)).mul (hΦ j)
  have hform : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun y : M ↦ TotalSpace.mk' E y
        (∑ i, c i y • chartLocalFrame (I := I) a i y))
      (chartAt H a).source := by
    refine ContMDiffOn.sum_section fun i _ ↦ ?_
    have hframe := contMDiffOn_chartLocalFrame (I := I) (n := n) a i
    have hframe' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
        (fun y : M ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) a i y))
        (chartAt H a).source := by
      simpa only [TangentBundle.trivializationAt_baseSet] using hframe
    exact ContMDiffOn.smul_section (hc i) hframe'
  refine hform.congr fun y hy ↦ ?_
  simpa only [c, Matrix.mulVec, dotProduct] using congrArg (TotalSpace.mk' E y)
    (rieszDual_eq_sum_chartLocalFrame (I := I) a hy (Φ y))

/-- Pointwise version of `contMDiffOn_rieszDual`: smoothness of the frame evaluations at a
point in a chart source implies smoothness of the fibrewise Riesz-dual section there. -/
theorem contMDiffAt_rieszDual (a : M) {x : M} (hx : x ∈ (chartAt H a).source)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) n (fun y ↦ Φ y (chartLocalFrame (I := I) a j y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y : M ↦ TotalSpace.mk' E y
        (rieszDual (I := I) (Φ y))) x := by
  have hopen : IsOpen (chartAt H a).source := (chartAt H a).open_source
  let c : Fin (Module.finrank ℝ E) → M → ℝ := fun i y ↦
    ∑ j, chartInvGramMatrix (I := I) a y i j *
      Φ y (chartLocalFrame (I := I) a j y)
  have hc (i : Fin (Module.finrank ℝ E)) : ContMDiffAt I 𝓘(ℝ) n (c i) x := by
    dsimp only [c]
    exact contMDiffAt_finsetSum fun j _ ↦
      ((show ContMDiffOn I 𝓘(ℝ) n
          (fun y ↦ chartInvGramMatrix (I := I) a y i j) (chartAt H a).source by
        simpa only [TangentBundle.trivializationAt_baseSet] using
          (contMDiffOn_chartInvGramMatrix_entry (I := I) (n := n) a i j)).contMDiffAt
            (hopen.mem_nhds hx)).mul (hΦ j)
  have hframe (i : Fin (Module.finrank ℝ E)) :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
        (fun y : M ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) a i y)) x :=
    (show ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
        (fun y : M ↦ TotalSpace.mk' E y (chartLocalFrame (I := I) a i y))
        (chartAt H a).source by
      simpa only [TangentBundle.trivializationAt_baseSet] using
        (contMDiffOn_chartLocalFrame (I := I) (n := n) a i)).contMDiffAt (hopen.mem_nhds hx)
  have hform : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun y : M ↦ TotalSpace.mk' E y
        (∑ i, c i y • chartLocalFrame (I := I) a i y)) x := by
    refine ContMDiffAt.sum_section fun i _ ↦ ?_
    exact ContMDiffAt.smul_section (hc i) (hframe i)
  refine hform.congr_of_eventuallyEq ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  simpa only [c, Matrix.mulVec, dotProduct] using congrArg (TotalSpace.mk' E y)
    (rieszDual_eq_sum_chartLocalFrame (I := I) a hy (Φ y))

end Smooth

end Tensor
end Riemannian
