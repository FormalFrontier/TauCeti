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
public import Mathlib.LinearAlgebra.Basis.Defs
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Chart Gram matrices of a Riemannian metric

This file constructs the Gram matrix of the metric supplied by a `RiemannianBundle` instance in
the local frame induced by a tangent-bundle trivialization and proves that its entries and the
entries of its inverse are smooth on the trivialization base set. The construction uses
`Bundle.Trivialization.localFrame` and `Bundle.Trivialization.basisAt`, so it applies unchanged
when the model space has dimension zero.

The Gram-matrix and inverse-matrix declarations are adapted from stages 1--5 of the Apache-2.0
Poincare-Conjecture source file
`DoCarmoLib/Riemannian/TensorBundle/MusicalIso.lean`, while the chart-transition identities are
adapted from `DoCarmoLib/Riemannian/Geodesic/HopfRinow/MetricBridge.lean`, both at revision
`24f32e4d600878bfaac6bc2f2f9324175571c321`. Those sources use an explicit metric and a custom
chart frame; here the metric supplied by Mathlib's `RiemannianBundle` instance and its local-frame
API replace them.

## Main definitions and results

* `Riemannian.Tensor.chartLocalFrame` and `Riemannian.Tensor.chartLocalFrame_def`: the frame
  induced by the tangent trivialization at a chart centre and `Module.finBasis`, and its
  identification with that trivialization's local frame.
* `Riemannian.Tensor.trivializationAt_symm_eq_sum_chartLocalFrame`: expansion of an inverse
  tangent trivialization in the chart-local frame.
* `Riemannian.Tensor.chartGramMatrix`: the metric Gram matrix in this frame.
* `Riemannian.Tensor.chartGramMatrix_change`: its change-of-chart formula.
* `Riemannian.Tensor.chartGramMatrix_change_quadratic`: the corresponding change-of-chart formula
  for the metric quadratic form on a coordinate velocity.
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
* Poincare-Conjecture, `DoCarmoLib/Riemannian/Geodesic/HopfRinow/MetricBridge.lean`,
  chart-frame and Gram-matrix transition declarations, revision
  `24f32e4d600878bfaac6bc2f2f9324175571c321` (Apache-2.0).

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

/-- The chart-local frame is the local frame of the tangent trivialization at `α` for the
`Module.finBasis` basis. This unfolds `Riemannian.Tensor.chartLocalFrame` outside the module where
it is defined. -/
theorem chartLocalFrame_def (α : M) :
    chartLocalFrame (I := I) α =
      (trivializationAt E (TangentSpace I) α).localFrame (Module.finBasis ℝ E) := (rfl)

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

/-- On the chart source, a chart-local frame vector is the inverse tangent trivialization of the
corresponding model-space basis vector. -/
theorem chartLocalFrame_apply_of_mem_chart_source_eq_symm (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartLocalFrame (I := I) α i x =
      (trivializationAt E (TangentSpace I) α).symm x ((Module.finBasis ℝ E) i) := by
  rw [chartLocalFrame_apply_of_mem_chart_source (I := I) α hx i]
  rfl

/-- The inverse tangent trivialization expands in the canonical chart-local frame. The
  coefficients are the coordinates in `Module.finBasis ℝ E`; the chart-source hypothesis is needed
  because local frames have a junk value outside the trivialization base set. -/
theorem trivializationAt_symm_eq_sum_chartLocalFrame (α : M) (x : M) (v : E)
    (hx : x ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).symm x v =
      ∑ i, (Module.finBasis ℝ E).repr v i • chartLocalFrame (I := I) α i x := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hx']
  conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hx',
    ← chartLocalFrame_apply_of_mem_chart_source_eq_symm (I := I) α hx i]

/-- At a common foot in two chart sources, the `β` chart-local frame vector is the `α`
readback of the tangent coordinate change from `β` to `α`. -/
theorem chartLocalFrame_eq_symm_tangentCoordChange (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartLocalFrame (I := I) β i x =
      (trivializationAt E (TangentSpace I) α).symm x
        (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) := by
  have hα : x ∈ (extChartAt I α).source := by
    simpa only [extChartAt_source] using hxα
  have hβ : x ∈ (extChartAt I β).source := by
    simpa only [extChartAt_source] using hxβ
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [chartLocalFrame_apply_of_mem_chart_source_eq_symm (I := I) β hxβ i,
    TauCeti.Manifold.trivializationAt_symm_eq_tangentCoordChange
      (I := I) hxβ ((Module.finBasis ℝ E) i),
    TauCeti.Manifold.trivializationAt_symm_eq_tangentCoordChange (I := I) hxα
      (tangentCoordChange I β α x ((Module.finBasis ℝ E) i))]
  exact (tangentCoordChange_comp (I := I) ⟨⟨hβ, hα⟩, hx⟩).symm

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

/-- The Gram matrix transforms as a `(0,2)` tensor under a change of chart. At a point in the
overlap, each entry in the `β` frame is a finite double sum of entries in the `α` frame and the
two tangent-coordinate change coefficients. -/
theorem chartGramMatrix_change (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) β x i j =
      ∑ a, ∑ b, chartGramMatrix (I := I) α x a b
        * (Module.finBasis ℝ E).repr
            (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) a
        * (Module.finBasis ℝ E).repr
            (tangentCoordChange I β α x ((Module.finBasis ℝ E) j)) b := by
  let e := trivializationAt E (TangentSpace I) α
  let u := tangentCoordChange I β α x ((Module.finBasis ℝ E) i)
  let v := tangentCoordChange I β α x ((Module.finBasis ℝ E) j)
  have hxα' : x ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hxα
  rw [chartGramMatrix_apply (I := I) β x i j,
    chartLocalFrame_eq_symm_tangentCoordChange (I := I) α β hxα hxβ i,
    chartLocalFrame_eq_symm_tangentCoordChange (I := I) α β hxα hxβ j]
  have hexpand :=
    (LinearMap.sum_repr_mul_repr_mul (Module.finBasis ℝ E) (Module.finBasis ℝ E)
      (B := (innerₗ (TangentSpace I x)).compl₁₂
        (e.symmL ℝ x).toLinearMap (e.symmL ℝ x).toLinearMap) u v).symm
  rw [Finsupp.sum_fintype] at hexpand
  · have hinner (a : Fin (Module.finrank ℝ E)) :
        ((Module.finBasis ℝ E).repr v).sum (fun b yb ↦
            (Module.finBasis ℝ E).repr u a • yb •
              (innerₗ (TangentSpace I x)).compl₁₂
                (e.symmL ℝ x).toLinearMap (e.symmL ℝ x).toLinearMap
                ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) b)) =
          ∑ b, (Module.finBasis ℝ E).repr u a •
            (Module.finBasis ℝ E).repr v b •
              (innerₗ (TangentSpace I x)).compl₁₂
                (e.symmL ℝ x).toLinearMap (e.symmL ℝ x).toLinearMap
                ((Module.finBasis ℝ E) a) ((Module.finBasis ℝ E) b) :=
      Finsupp.sum_fintype _ _ (fun _ ↦ by simp)
    simp_rw [hinner] at hexpand
    simp only [e] at hexpand
    have hsymmL (z : E) :
        (trivializationAt E (TangentSpace I) α).symmL ℝ x z =
          (trivializationAt E (TangentSpace I) α).symm x z :=
      Bundle.Trivialization.symmL_apply (R := ℝ)
        (trivializationAt E (TangentSpace I) α)
        (by simpa only [e] using hxα') z
    simp only [LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe,
      innerₗ_apply_apply] at hexpand
    have hsymmL_fun :
        ((trivializationAt E (TangentSpace I) α).symmL ℝ x :
          E → TangentSpace I x) =
            (trivializationAt E (TangentSpace I) α).symm x :=
      funext hsymmL
    rw [hsymmL_fun] at hexpand
    simpa only [u, v, smul_eq_mul,
      chartLocalFrame_apply_of_mem_chart_source_eq_symm (I := I) α hxα,
      chartGramMatrix_apply (I := I) α x, mul_assoc, mul_comm, mul_left_comm] using hexpand
  · intro
    simp

/-- The metric quadratic form of a coordinate velocity is invariant under the chart change: the
  coefficients in the `β` frame are first converted to the `α` frame by the tangent-coordinate
  change, and the `α` Gram matrix then evaluates the quadratic form. -/
theorem chartGramMatrix_change_quadratic (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, chartGramMatrix (I := I) β x i j * c i * c j) =
      ∑ a, ∑ b, chartGramMatrix (I := I) α x a b *
        (∑ i, (Module.finBasis ℝ E).repr
          (tangentCoordChange I β α x ((Module.finBasis ℝ E) i)) a * c i) *
        (∑ j, (Module.finBasis ℝ E).repr
          (tangentCoordChange I β α x ((Module.finBasis ℝ E) j)) b * c j) := by
  classical
  simp_rw [chartGramMatrix_change (I := I) α β hxα hxβ]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [mul_assoc]
  simp_rw [Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Finset.sum_comm]

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
