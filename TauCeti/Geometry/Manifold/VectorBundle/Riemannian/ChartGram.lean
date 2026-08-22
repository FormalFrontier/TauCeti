/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon Horizon (claude+codex), Axel Delaval, Chunlei Liu,
Jinxuan Chen, Wanxu Yang, Zekun Sheng, Yuxuan Liao, Jie Xu
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Chart Gram matrices of a Riemannian metric

This file constructs the Gram matrix of the metric supplied by a `RiemannianBundle` instance in
the local frame induced by a tangent-bundle trivialization and proves that its entries and the
entries of its inverse are smooth on the trivialization base set. The construction uses
`Bundle.Trivialization.localFrame` and `Bundle.Trivialization.basisAt`, so it applies unchanged
when the model space has dimension zero.

The Gram-matrix and inverse-matrix declarations are adapted from stages 1--5 of the Apache-2.0
Poincare-Conjecture source file
`DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. That source uses an explicit metric and a custom
chart frame; here the metric supplied by Mathlib's `RiemannianBundle` instance and its local-frame
API replace them.

## Main definitions and results

* `Riemannian.Tensor.chartLocalFrame`: the frame induced by the tangent trivialization at a chart
  centre and `Module.finBasis`.
* `Riemannian.Tensor.chartGramMatrix`: the metric Gram matrix in this frame.
* `Riemannian.Tensor.posDef_chartGramMatrix`: positive-definiteness on the base set.
* `Riemannian.Tensor.chartGramMatrix_det_pos`: strict positivity of its determinant there.
* `Riemannian.Tensor.contMDiffOn_chartGramMatrix_entry`: smoothness of Gram-matrix entries.
* `Riemannian.Tensor.chartInvGramMatrix`: the inverse Gram matrix.
* `Riemannian.Tensor.contMDiffOn_chartInvGramMatrix_entry`: smoothness of inverse entries.

## References

* [Geodesics, the exponential map, and the Hopf--Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Regularity of the Levi-Civita connection".
* M. P. do Carmo, *Riemannian Geometry*, Chapter 2.
* Poincare-Conjecture, `DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, stages 1--5,
  revision `24f32e4d600878bfaac6bc2f2f9324175571c321` (Apache-2.0).

-/

noncomputable section
public section

open Bundle FiberBundle Manifold Set
open scoped ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace Riemannian
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The chart-local frame obtained from the tangent-bundle trivialization centred at `α` and
the chosen `Module.finBasis` basis of the model space. Outside the trivialization base set it has
Mathlib's standard junk value `0`. -/
def chartLocalFrame (α : M) :
    Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).localFrame (Module.finBasis ℝ E)

/-- On the chart source, the local frame agrees with the basis supplied by the tangent
trivialization. The source membership is the simplified form of the trivialization base set. -/
@[simp]
theorem chartLocalFrame_apply_of_mem_chart_source (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartLocalFrame (I := I) α i x =
      (trivializationAt E (TangentSpace I) α).basisAt (Module.finBasis ℝ E)
        (by simpa only [TangentBundle.trivializationAt_baseSet] using hx) i := by
  simpa only [chartLocalFrame, TangentBundle.trivializationAt_baseSet] using
    (trivializationAt E (TangentSpace I) α).localFrame_apply_of_mem_baseSet
      (Module.finBasis ℝ E) (i := i) (by
        simpa only [TangentBundle.trivializationAt_baseSet] using hx)

/-- Each member of `chartLocalFrame` is `C^n` on the tangent-trivialization base set. -/
theorem contMDiffOn_chartLocalFrame {n : ℕ∞ω} [IsManifold I (n + 1) M]
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (chartLocalFrame (I := I) α i x))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  let _ : ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  exact (trivializationAt E (TangentSpace I) α).contMDiffOn_localFrame_baseSet
    (n := n) (Module.finBasis ℝ E) i

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The Gram matrix of `chartLocalFrame α` for the fiber inner product supplied by the
`RiemannianBundle` instance at `x`. Its entries are the coordinate metric coefficients used in
do Carmo, *Riemannian Geometry*, Chapter 2. -/
def chartGramMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.gram ℝ fun i ↦ chartLocalFrame (I := I) α i x

/-- An entry of the chart Gram matrix is the inner product of the corresponding frame vectors. -/
@[simp]
theorem chartGramMatrix_apply (α : M) (x : M) (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) α x i j =
      inner ℝ (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α j x) := (rfl)

/-- The Gram matrix of the chart-local frame is positive-definite on the tangent-trivialization
base set. -/
theorem posDef_chartGramMatrix (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix (I := I) α x).PosDef :=
  Matrix.posDef_gram_of_linearIndependent <|
    ((trivializationAt E (TangentSpace I) α).isLocalFrameOn_localFrame_baseSet
      I 0 (Module.finBasis ℝ E)).linearIndependent hx

/-- The determinant of the chart Gram matrix is strictly positive on the tangent-trivialization
base set. -/
theorem chartGramMatrix_det_pos (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < (chartGramMatrix (I := I) α x).det :=
  (posDef_chartGramMatrix (I := I) α hx).det_pos

/-- Smoothness of a matrix determinant follows from smoothness of all matrix entries. -/
private lemma contMDiffOn_matrix_det_of_entries
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {X : Type*} [TopologicalSpace X] [ChartedSpace HB X]
    {n : ℕ∞ω}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : X → Matrix ι ι ℝ} {s : Set X}
    (hA : ∀ i j, ContMDiffOn IB 𝓘(ℝ) n (fun x ↦ A x i j) s) :
    ContMDiffOn IB 𝓘(ℝ) n (fun x ↦ (A x).det) s := by
  classical
  have hexp :
      (fun x : X ↦ (A x).det) =
        fun x : X ↦ ∑ σ : Equiv.Perm ι,
          (Equiv.Perm.sign σ : ℝ) * ∏ i, A x (σ i) i := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum fun σ _ ↦ ?_
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd fun i _ ↦ ?_
  exact hA (σ i) i

section Smooth

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- Every entry of the chart Gram matrix is `C^n` on the tangent-trivialization base set. -/
theorem contMDiffOn_chartGramMatrix_entry
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) n (fun x ↦ chartGramMatrix (I := I) α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  exact ContMDiffOn.inner_bundle (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)
    (contMDiffOn_chartLocalFrame (I := I) (n := n) α i)
    (contMDiffOn_chartLocalFrame (I := I) (n := n) α j)

/-- Every adjugate entry of the chart Gram matrix is `C^n` on the tangent-trivialization base
set. -/
private lemma contMDiffOn_adjugate_chartGramMatrix_entry
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) n
      (fun x : M ↦ (chartGramMatrix (I := I) α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M ↦ (chartGramMatrix (I := I) α x).adjugate i j) =
        fun x : M ↦ ((chartGramMatrix (I := I) α x).updateRow j
          (Pi.single i (1 : ℝ))).det := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  apply contMDiffOn_matrix_det_of_entries
  intro k l
  by_cases hkj : k = j
  · subst k
    simp only [Matrix.updateRow_self]
    exact contMDiffOn_const
  · simp only [Matrix.updateRow_apply, hkj, ite_false]
    exact contMDiffOn_chartGramMatrix_entry (I := I) (n := n) α k l

end Smooth

/-- The inverse coordinate-metric matrix from do Carmo, *Riemannian Geometry*, Chapter 2. On the
tangent-trivialization base set this is the inverse of a positive-definite matrix. -/
def chartInvGramMatrix (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) α x)⁻¹

/-- On the chart source, the inverse Gram matrix is a left inverse. -/
@[simp]
theorem chartInvGramMatrix_mul_chartGramMatrix (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartInvGramMatrix (I := I) α x * chartGramMatrix (I := I) α x = 1 := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) α hx'))
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- On the chart source, the inverse Gram matrix is a right inverse. -/
@[simp]
theorem chartGramMatrix_mul_chartInvGramMatrix (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartGramMatrix (I := I) α x * chartInvGramMatrix (I := I) α x = 1 := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) α hx'))
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

section Smooth

variable {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]

/-- Every entry of the inverse chart Gram matrix is `C^n` on the tangent-trivialization base set. -/
theorem contMDiffOn_chartInvGramMatrix_entry
    (α : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) n (fun x : M ↦ chartInvGramMatrix (I := I) α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) α x i j =
        ((chartGramMatrix (I := I) α x).det)⁻¹ *
          (chartGramMatrix (I := I) α x).adjugate i j := by
    intro x _
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    simp only [Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  have hdet_smooth := contMDiffOn_matrix_det_of_entries
    (fun k l ↦ contMDiffOn_chartGramMatrix_entry (I := I) (n := n) α k l)
  refine ContMDiffOn.congr (ContMDiffOn.mul (hdet_smooth.inv₀ ?_) ?_) hcongr
  · intro x hx
    exact ne_of_gt (chartGramMatrix_det_pos (I := I) α hx)
  · exact contMDiffOn_adjugate_chartGramMatrix_entry (I := I) α i j

end Smooth

end Tensor
end Riemannian
