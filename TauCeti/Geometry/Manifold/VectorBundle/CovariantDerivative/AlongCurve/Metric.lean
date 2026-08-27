/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# Metric compatibility along a curve

This file proves the product rule for a metric-compatible covariant derivative acting on tangent
fields along a curve:

`(d/dt) ⟪V, W⟫ = ⟪D V / dt, W⟫ + ⟪V, D W / dt⟫`.

The proof first handles fields pulled back from smooth local-frame fields, where the result is
Mathlib's ambient `CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq` and the chain rule.
A differentiable field along the curve is locally a finite linear combination of those pullbacks;
the additive and scalar Leibniz laws of `CovariantDerivative.alongCurve` finish the argument.

## Main result

* `CovariantDerivative.IsMetricCompatible.deriv_inner_alongCurve`: the metric product rule for
  two differentiable tangent fields along a differentiable real curve.

## References

* M. P. do Carmo, *Riemannian Geometry*, Chapter 2, Proposition 3.2.
* The proof organization is adapted from
  `DoCarmoLib/Riemannian/Connection/MetricCompatibilityAlong.lean` in the Apache-2.0
  [`frenzymath/Poincare-Conjecture`](https://github.com/frenzymath/Poincare-Conjecture)
  repository, revision `24f32e4d600878bfaac6bc2f2f9324175571c321`, replacing its custom connection
  and metric APIs with Mathlib's `CovariantDerivative.IsMetricCompatible` and Tau Ceti's
  moving-chart derivative.
-/

public section

open Bundle Filter Function
open scoped Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {γ : ℝ → M} {t : ℝ}

/-- The product-rule statement at one parameter, packaged for the local-frame induction. -/
private def HasMetricProductRuleAt
    (V W : ∀ r, TangentSpace I (γ r)) : Prop :=
  DifferentiableAt ℝ (fun r ↦ inner ℝ (V r) (W r)) t ∧
    deriv (fun r ↦ inner ℝ (V r) (W r)) t =
      inner ℝ (alongCurve cov γ V t) (W t) +
        inner ℝ (V t) (alongCurve cov γ W t)

/-- Metric compatibility along a curve for fields pulled back from ambient differentiable
sections. -/
private theorem IsMetricCompatible.hasMetricProductRuleAt_pullback
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {X Y : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) (γ t)) (hY : MDiffAt (T% Y) (γ t)) :
    HasMetricProductRuleAt (cov := cov) (γ := γ) (t := t) (fun r ↦ X (γ r))
      (fun r ↦ Y (γ r)) := by
  rw [HasMetricProductRuleAt]
  let v := curveVelocity I γ t
  let Z : (x : M) → TangentSpace I x := FiberBundle.extend E v
  have hinner : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x ↦ inner ℝ (X x) (Y x)) (γ t) :=
    MDifferentiableAt.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY
  have hchain := hasDerivAt_comp_curve hinner
    (hasMFDerivAt_curveVelocity hγ)
  have hmetric := hcov.mvfderiv_inner_eq Z hX hY
  have hZ : Z (γ t) = curveVelocity I γ t := by
    exact FiberBundle.extend_apply_self E v
  dsimp only at hmetric
  rw [hZ] at hmetric
  have hmetric' :
      mvfderiv I (fun x ↦ inner ℝ (X x) (Y x)) (γ t) (curveVelocity I γ t) =
        inner ℝ (cov X (γ t) (curveVelocity I γ t)) (Y (γ t)) +
          inner ℝ (X (γ t)) (cov Y (γ t) (curveVelocity I γ t)) := by
    simpa only [Function.comp_apply] using hmetric
  rw [hmetric'] at hchain
  rw [alongCurve_pullback cov γ X (hasMFDerivAt_curveVelocity hγ) hX,
    alongCurve_pullback cov γ Y (hasMFDerivAt_curveVelocity hγ) hY]
  exact ⟨hchain.differentiableAt, hchain.deriv⟩

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is additive in its first field. -/
private lemma HasMetricProductRuleAt.add_left
    {V V' W : ∀ r, TangentSpace I (γ r)}
    (hV : HasMetricProductRuleAt (cov := cov) (t := t) V W)
    (hV' : HasMetricProductRuleAt (cov := cov) (t := t) V' W)
    (hcoordV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hcoordV' : DifferentiableAt ℝ (sectionCoord (F := E) γ V' (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) (fun r ↦ V r + V' r) W := by
  rw [HasMetricProductRuleAt] at hV hV' ⊢
  have hfun : (fun r ↦ inner ℝ (V r + V' r) (W r)) =
      (fun r ↦ inner ℝ (V r) (W r) + inner ℝ (V' r) (W r)) := by
    funext r
    exact inner_add_left _ _ _
  constructor
  · rw [hfun]
    exact hV.1.add hV'.1
  · have hd := deriv_add hV.1 hV'.1
    change deriv (fun r ↦ inner ℝ (V r) (W r) + inner ℝ (V' r) (W r)) t = _ at hd
    rw [hfun, hd, hV.2, hV'.2,
      alongCurve_add cov γ V V' hcoordV hcoordV']
    simp only [inner_add_left]
    ring

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is additive in its second field. -/
private lemma HasMetricProductRuleAt.add_right
    {V W W' : ∀ r, TangentSpace I (γ r)}
    (hW : HasMetricProductRuleAt (cov := cov) (t := t) V W)
    (hW' : HasMetricProductRuleAt (cov := cov) (t := t) V W')
    (hcoordW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t)
    (hcoordW' : DifferentiableAt ℝ (sectionCoord (F := E) γ W' (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) V (fun r ↦ W r + W' r) := by
  rw [HasMetricProductRuleAt] at hW hW' ⊢
  have hfun : (fun r ↦ inner ℝ (V r) (W r + W' r)) =
      (fun r ↦ inner ℝ (V r) (W r) + inner ℝ (V r) (W' r)) := by
    funext r
    exact inner_add_right _ _ _
  constructor
  · rw [hfun]
    exact hW.1.add hW'.1
  · have hd := deriv_add hW.1 hW'.1
    change deriv (fun r ↦ inner ℝ (V r) (W r) + inner ℝ (V r) (W' r)) t = _ at hd
    rw [hfun, hd, hW.2, hW'.2,
      alongCurve_add cov γ W W' hcoordW hcoordW']
    simp only [inner_add_right]
    ring

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by multiplying its first field by a differentiable scalar. -/
private lemma HasMetricProductRuleAt.smul_left
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hV : HasMetricProductRuleAt (cov := cov) (t := t) V W)
    (hf : DifferentiableAt ℝ f t)
    (hcoordV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) (fun r ↦ f r • V r) W := by
  rw [HasMetricProductRuleAt] at hV ⊢
  have hfun : (fun r ↦ inner ℝ (f r • V r) (W r)) =
      (fun r ↦ f r * inner ℝ (V r) (W r)) := by
    funext r
    exact real_inner_smul_left _ _ _
  constructor
  · rw [hfun]
    exact hf.mul hV.1
  · have hd := deriv_mul hf hV.1
    change deriv (fun r ↦ f r * inner ℝ (V r) (W r)) t = _ at hd
    rw [hfun, hd, hV.2, alongCurve_smul cov γ V f hf hcoordV]
    simp only [inner_add_left, real_inner_smul_left]
    ring

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by multiplying its second field by a differentiable scalar. -/
private lemma HasMetricProductRuleAt.smul_right
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hW : HasMetricProductRuleAt (cov := cov) (t := t) V W)
    (hf : DifferentiableAt ℝ f t)
    (hcoordW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) V (fun r ↦ f r • W r) := by
  rw [HasMetricProductRuleAt] at hW ⊢
  have hfun : (fun r ↦ inner ℝ (V r) (f r • W r)) =
      (fun r ↦ f r * inner ℝ (V r) (W r)) := by
    funext r
    rw [real_inner_smul_right, mul_comm]
  constructor
  · rw [hfun]
    exact hf.mul hW.1
  · have hd := deriv_mul hf hW.1
    change deriv (fun r ↦ f r * inner ℝ (V r) (W r)) t = _ at hd
    rw [hfun, hd, hW.2, alongCurve_smul cov γ W f hf hcoordW]
    simp only [inner_add_right, real_inner_smul_right]
    ring

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- A finite sum of fields with differentiable coordinate readings again has a differentiable
coordinate reading. -/
private lemma differentiableAt_sectionCoord_finsetSum
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A, DifferentiableAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) t) :
    DifferentiableAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ ∑ i ∈ A, U i r) (γ t)) t := by
  classical
  have hfun : sectionCoord (F := E) γ (fun r ↦ ∑ i ∈ A, U i r) (γ t) =
      fun r ↦ ∑ i ∈ A, sectionCoord (F := E) γ (U i) (γ t) r := by
    funext r
    simp only [sectionCoord_apply, map_sum]
  rw [hfun]
  exact DifferentiableAt.fun_sum hU

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by a finite sum in its first field. -/
private lemma HasMetricProductRuleAt.finsetSum_left
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    {W : ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A, HasMetricProductRuleAt (cov := cov) (t := t) (U i) W)
    (hcoordU : ∀ i ∈ A,
      DifferentiableAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) (fun r ↦ ∑ i ∈ A, U i r) W := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      rw [HasMetricProductRuleAt]
      simp
  | @insert a A ha ih =>
      have ha_rule := hU a (Finset.mem_insert_self a A)
      have hA_rule := ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi))
      have hsum := ha_rule.add_left hA_rule
        (hcoordU a (Finset.mem_insert_self a A))
        (differentiableAt_sectionCoord_finsetSum
          (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sum_insert ha, Pi.add_apply] using hsum

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by a finite sum in its second field. -/
private lemma HasMetricProductRuleAt.finsetSum_right
    {ι : Type*} {A : Finset ι} {V : ∀ r, TangentSpace I (γ r)}
    {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A, HasMetricProductRuleAt (cov := cov) (t := t) V (U i))
    (hcoordU : ∀ i ∈ A,
      DifferentiableAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) V (fun r ↦ ∑ i ∈ A, U i r) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      rw [HasMetricProductRuleAt]
      simp
  | @insert a A ha ih =>
      have ha_rule := hU a (Finset.mem_insert_self a A)
      have hA_rule := ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi))
      have hsum := ha_rule.add_right hA_rule
        (hcoordU a (Finset.mem_insert_self a A))
        (differentiableAt_sectionCoord_finsetSum
          (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sum_insert ha, Pi.add_apply] using hsum

/-- The metric product rule for arbitrary differentiable fields along a curve. -/
private theorem IsMetricCompatible.hasMetricProductRuleAt
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    HasMetricProductRuleAt (cov := cov) (t := t) V W := by
  classical
  let e := trivializationAt E (TangentSpace I) (γ t)
  let b := Module.finBasis ℝ E
  let X : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x :=
    fun i ↦ e.localFrame b i
  let aV : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    b.repr (sectionCoord (F := E) γ V (γ t) r) i
  let aW : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    b.repr (sectionCoord (F := E) γ W (γ t) r) i
  let U : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aV i r • X i (γ r)
  let Z : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aW i r • X i (γ r)
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hframe (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (X i)) (γ t) := by
    exact (((e.isLocalFrameOn_localFrame_baseSet I 1 b).contMDiffOn i).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e.open_baseSet.mem_nhds hbase)
  have haV (i : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ (aV i) t := by
    change DifferentiableAt ℝ ((b.coord i) ∘ sectionCoord (F := E) γ V (γ t)) t
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp t hV
  have haW (i : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ (aW i) t := by
    change DifferentiableAt ℝ ((b.coord i) ∘ sectionCoord (F := E) γ W (γ t)) t
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt.comp t hW
  have hcoordX (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t)) t := by
    exact differentiableAt_sectionCoord γ (fun r ↦ X i (γ r))
      ((hframe i).comp t hγ) hbase
  have hcoordU (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) t := by
    rw [show sectionCoord (F := E) γ (U i) (γ t) =
      aV i • sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t) by
        exact sectionCoord_smul γ (fun r ↦ X i (γ r)) (aV i) (γ t)]
    exact (haV i).smul (hcoordX i)
  have hcoordZ (i : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (sectionCoord (F := E) γ (Z i) (γ t)) t := by
    rw [show sectionCoord (F := E) γ (Z i) (γ t) =
      aW i • sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t) by
        exact sectionCoord_smul γ (fun r ↦ X i (γ r)) (aW i) (γ t)]
    exact (haW i).smul (hcoordX i)
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      HasMetricProductRuleAt (cov := cov) (t := t) (U i) (Z j) := by
    exact ((hcov.hasMetricProductRuleAt_pullback hγ (hframe i) (hframe j)).smul_left
      (haV i) (hcoordX i)).smul_right (haW j) (hcoordX j)
  have hsum : HasMetricProductRuleAt (cov := cov) (t := t)
      (fun r ↦ ∑ i, U i r) (fun r ↦ ∑ j, Z j r) := by
    refine HasMetricProductRuleAt.finsetSum_left
      (A := Finset.univ) (U := U) (W := fun r ↦ ∑ j, Z j r) ?_ ?_
    · intro i hi
      exact HasMetricProductRuleAt.finsetSum_right
        (A := Finset.univ) (hU := fun j _ ↦ hterm i j) (fun j _ ↦ hcoordZ j)
    · exact fun i _ ↦ hcoordU i
  have hnear : ∀ᶠ r in 𝓝 t, γ r ∈ e.baseSet :=
    hγ.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)
  have hVsum : V =ᶠ[𝓝 t] fun r ↦ ∑ i, U i r := by
    filter_upwards [hnear] with r hr
    calc
      V r = e.symmL ℝ (γ r) (sectionCoord (F := E) γ V (γ t) r) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hr]
      _ = e.symmL ℝ (γ r)
          (∑ i, b.repr (sectionCoord (F := E) γ V (γ t) r) i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i, U i r := by
        simp only [map_sum, map_smul, U, aV, X, symmL_basis_eq_localFrame b hr]
  have hWsum : W =ᶠ[𝓝 t] fun r ↦ ∑ i, Z i r := by
    filter_upwards [hnear] with r hr
    calc
      W r = e.symmL ℝ (γ r) (sectionCoord (F := E) γ W (γ t) r) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hr]
      _ = e.symmL ℝ (γ r)
          (∑ i, b.repr (sectionCoord (F := E) γ W (γ t) r) i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i, Z i r := by
        simp only [map_sum, map_smul, Z, aW, X, symmL_basis_eq_localFrame b hr]
  have hinner : (fun r ↦ inner ℝ (V r) (W r)) =ᶠ[𝓝 t]
      fun r ↦ inner ℝ (∑ i, U i r) (∑ j, Z j r) := by
    filter_upwards [hVsum, hWsum] with r hVr hWr
    rw [hVr, hWr]
    rfl
  have hDV : alongCurve cov γ V t =
      alongCurve cov γ (fun r ↦ ∑ i, U i r) t :=
    alongCurve_congr cov γ V hVsum
  have hDW : alongCurve cov γ W t =
      alongCurve cov γ (fun r ↦ ∑ i, Z i r) t :=
    alongCurve_congr cov γ W hWsum
  have hVt : V t = ∑ i, U i t := hVsum.self_of_nhds
  have hWt : W t = ∑ i, Z i t := hWsum.self_of_nhds
  rw [HasMetricProductRuleAt] at hsum ⊢
  constructor
  · exact hinner.differentiableAt_iff.mpr hsum.1
  · calc
      deriv (fun r ↦ inner ℝ (V r) (W r)) t =
          deriv (fun r ↦ inner ℝ (∑ i, U i r) (∑ j, Z j r)) t := hinner.deriv_eq
      _ = inner ℝ (alongCurve cov γ (fun r ↦ ∑ i, U i r) t) (∑ j, Z j t) +
          inner ℝ (∑ i, U i t) (alongCurve cov γ (fun r ↦ ∑ j, Z j r) t) := hsum.2
      _ = inner ℝ (alongCurve cov γ V t) (W t) +
          inner ℝ (V t) (alongCurve cov γ W t) := by
        rw [hDV, hDW, hVt, hWt]

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable. -/
theorem IsMetricCompatible.differentiableAt_inner_alongCurve
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    DifferentiableAt ℝ (fun r ↦ inner ℝ (V r) (W r)) t :=
  (hcov.hasMetricProductRuleAt hγ hV hW).1

/-- The product rule for a metric-compatible covariant derivative acting on two differentiable
tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.deriv_inner_alongCurve
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    deriv (fun r ↦ inner ℝ (V r) (W r)) t =
      inner ℝ (alongCurve cov γ V t) (W t) +
        inner ℝ (V t) (alongCurve cov γ W t) :=
  (hcov.hasMetricProductRuleAt hγ hV hW).2

end CovariantDerivative

end
