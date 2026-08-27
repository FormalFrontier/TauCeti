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
the additive and scalar Leibniz laws of `CovariantDerivative.alongCurveWithin` finish the argument.

## Main results

* `CovariantDerivative.IsMetricCompatible.hasDerivWithinAt_inner_alongCurveWithin`: the
  within-set metric product rule for two differentiable tangent fields along a differentiable
  real curve.
* `CovariantDerivative.IsMetricCompatible.differentiableWithinAt_inner` and
  `CovariantDerivative.IsMetricCompatible.derivWithin_inner_alongCurveWithin`: its two principal
  consequences.
* `CovariantDerivative.IsMetricCompatible.hasDerivAt_inner_alongCurve`: the unrestricted form,
  with `CovariantDerivative.IsMetricCompatible.differentiableAt_inner` and
  `CovariantDerivative.IsMetricCompatible.deriv_inner_alongCurve` as consequences.

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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {cov : _root_.CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  {γ : ℝ → M} {s : Set ℝ} {t : ℝ}

/-- The within-set product-rule statement at one parameter, packaged for the local-frame
induction. -/
private abbrev HasMetricProductRuleWithinAt
    (V W : ∀ r, TangentSpace I (γ r)) : Prop :=
  HasDerivWithinAt (fun r ↦ inner ℝ (V r) (W r))
    (inner ℝ (alongCurveWithin cov γ V s t) (W t) +
      inner ℝ (V t) (alongCurveWithin cov γ W s t)) s t

/-- Metric compatibility along a curve for fields pulled back from ambient differentiable
sections. -/
private theorem IsMetricCompatible.hasMetricProductRuleWithinAt_pullback
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {X Y : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) (γ t)) (hY : MDiffAt (T% Y) (γ t)) :
    HasMetricProductRuleWithinAt (cov := cov) (γ := γ) (s := s) (t := t) (fun r ↦ X (γ r))
      (fun r ↦ Y (γ r)) := by
  let v := curveVelocityWithin I γ s t
  let Z : (x : M) → TangentSpace I x := FiberBundle.extend E v
  have hinner : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x ↦ inner ℝ (X x) (Y x)) (γ t) :=
    MDifferentiableAt.inner_bundle (IB := I) (F := E)
      (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY
  have hchain := hasDerivWithinAt_comp_curve hinner
    (hasMFDerivWithinAt_curveVelocityWithin hγ)
  have hmetric := hcov.mvfderiv_inner_eq Z hX hY
  have hZ : Z (γ t) = curveVelocityWithin I γ s t := FiberBundle.extend_apply_self E v
  have hmetric' :
      mvfderiv I (fun x ↦ inner ℝ (X x) (Y x)) (γ t) (curveVelocityWithin I γ s t) =
        inner ℝ (cov X (γ t) (curveVelocityWithin I γ s t)) (Y (γ t)) +
          inner ℝ (X (γ t)) (cov Y (γ t) (curveVelocityWithin I γ s t)) := by
    simpa only [Function.comp_apply, hZ] using hmetric
  rw [hmetric'] at hchain
  dsimp only [HasMetricProductRuleWithinAt]
  rw [alongCurveWithin_pullback_curveVelocityWithin cov γ X hu hγ hX,
    alongCurveWithin_pullback_curveVelocityWithin cov γ Y hu hγ hY]
  -- The chain-rule result uses a definitionally equal real normed-space instance.
  convert hchain using 1 <;> rfl

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is symmetric in its fields. -/
private lemma HasMetricProductRuleWithinAt.symm
    {V W : ∀ r, TangentSpace I (γ r)}
    (h : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) W V := by
  dsimp only [HasMetricProductRuleWithinAt] at h ⊢
  have hfun : (fun r ↦ inner ℝ (W r) (V r)) = fun r ↦ inner ℝ (V r) (W r) := by
    funext r
    exact real_inner_comm _ _
  rw [hfun]
  refine h.congr_deriv ?_
  rw [real_inner_comm (alongCurveWithin cov γ V s t) (W t),
    real_inner_comm (V t) (alongCurveWithin cov γ W s t), add_comm]

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is additive in its first field. -/
private lemma HasMetricProductRuleWithinAt.add_left
    {V V' W : ∀ r, TangentSpace I (γ r)}
    (hV : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W)
    (hV' : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V' W)
    (hcoordV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hcoordV' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V' (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun r ↦ V r + V' r) W := by
  dsimp only [HasMetricProductRuleWithinAt] at hV hV' ⊢
  have hfun : (fun r ↦ inner ℝ (V r + V' r) (W r)) =
      fun r ↦ inner ℝ (V r) (W r) + inner ℝ (V' r) (W r) := by
    funext r
    exact inner_add_left _ _ _
  rw [hfun]
  refine (hV.add hV').congr_deriv ?_
  rw [alongCurveWithin_add cov γ V V' s hcoordV hcoordV']
  simp only [inner_add_left]
  ring

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is additive in its second field. -/
private lemma HasMetricProductRuleWithinAt.add_right
    {V W W' : ∀ r, TangentSpace I (γ r)}
    (hW : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W)
    (hW' : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W')
    (hcoordW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t)
    (hcoordW' : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W' (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V
      (fun r ↦ W r + W' r) :=
  (hW.symm.add_left hW'.symm hcoordW hcoordW').symm

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by multiplying its first field by a differentiable scalar. -/
private lemma HasMetricProductRuleWithinAt.smul_left
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hV : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W)
    (hf : DifferentiableWithinAt ℝ f s t)
    (hcoordV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun r ↦ f r • V r) W := by
  dsimp only [HasMetricProductRuleWithinAt] at hV ⊢
  have hfun : (fun r ↦ inner ℝ (f r • V r) (W r)) =
      fun r ↦ f r * inner ℝ (V r) (W r) := by
    funext r
    exact real_inner_smul_left _ _ _
  rw [hfun]
  refine (hf.hasDerivWithinAt.mul hV).congr_deriv ?_
  rw [alongCurveWithin_smul cov γ V f s hf hcoordV]
  simp only [inner_add_left, real_inner_smul_left]
  ring

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by multiplying its second field by a differentiable scalar. -/
private lemma HasMetricProductRuleWithinAt.smul_right
    {V W : ∀ r, TangentSpace I (γ r)} {f : ℝ → ℝ}
    (hW : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W)
    (hf : DifferentiableWithinAt ℝ f s t)
    (hcoordW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V
      (fun r ↦ f r • W r) :=
  (hW.symm.smul_left hf hcoordW).symm

omit [FiniteDimensional ℝ E]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- A finite sum of fields with differentiable coordinate readings again has a differentiable
coordinate reading. -/
private lemma differentiableWithinAt_sectionCoord_finsetSum
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    DifferentiableWithinAt ℝ
      (sectionCoord (F := E) γ (fun r ↦ ∑ i ∈ A, U i r) (γ t)) s t := by
  rw [sectionCoord_sum]
  exact DifferentiableWithinAt.fun_sum hU

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by a finite sum in its first field. -/
private lemma HasMetricProductRuleWithinAt.finsetSum_left
    {ι : Type*} {A : Finset ι} {U : ι → ∀ r, TangentSpace I (γ r)}
    {W : ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) (U i) W)
    (hcoordU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun r ↦ ∑ i ∈ A, U i r) W := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      simpa [HasMetricProductRuleWithinAt] using
        (hasDerivWithinAt_const (x := t) (s := s) (c := (0 : ℝ)))
  | @insert a A ha ih =>
      have ha_rule := hU a (Finset.mem_insert_self a A)
      have hA_rule := ih (fun i hi ↦ hU i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi))
      have hsum := ha_rule.add_left hA_rule
        (hcoordU a (Finset.mem_insert_self a A))
        (differentiableWithinAt_sectionCoord_finsetSum
          (fun i hi ↦ hcoordU i (Finset.mem_insert_of_mem hi)))
      simpa only [Finset.sum_insert ha, Pi.add_apply] using hsum

omit [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- The product rule is preserved by a finite sum in its second field. -/
private lemma HasMetricProductRuleWithinAt.finsetSum_right
    {ι : Type*} {A : Finset ι} {V : ∀ r, TangentSpace I (γ r)}
    {U : ι → ∀ r, TangentSpace I (γ r)}
    (hU : ∀ i ∈ A,
      HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V (U i))
    (hcoordU : ∀ i ∈ A,
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V
      (fun r ↦ ∑ i ∈ A, U i r) :=
  ((HasMetricProductRuleWithinAt.finsetSum_left
    (hU := fun i hi ↦ (hU i hi).symm) hcoordU).symm)

/-- The metric product rule for arbitrary differentiable fields along a curve, within a parameter
set. -/
private theorem IsMetricCompatible.hasMetricProductRuleWithinAt
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) V W := by
  classical
  -- Choose a smooth local frame around the point of the curve.
  let e := trivializationAt E (TangentSpace I) (γ t)
  let b := Module.finBasis ℝ E
  let X : Fin (Module.finrank ℝ E) → (x : M) → TangentSpace I x :=
    fun i ↦ e.localFrame b i
  let aV : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    b.coord i (sectionCoord (F := E) γ V (γ t) r)
  let aW : Fin (Module.finrank ℝ E) → ℝ → ℝ := fun i r ↦
    b.coord i (sectionCoord (F := E) γ W (γ t) r)
  let U : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aV i r • X i (γ r)
  let Z : Fin (Module.finrank ℝ E) → ∀ r, TangentSpace I (γ r) :=
    fun i r ↦ aW i r • X i (γ r)
  have hbase : γ t ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hframe (i : Fin (Module.finrank ℝ E)) : MDiffAt (T% (X i)) (γ t) := by
    exact (((e.isLocalFrameOn_localFrame_baseSet I 1 b).contMDiffOn i).mdifferentiableOn
      one_ne_zero).mdifferentiableAt (e.open_baseSet.mem_nhds hbase)
  -- Coordinate coefficients and pulled-back frame fields are differentiable within the set.
  have haV (i : Fin (Module.finrank ℝ E)) : DifferentiableWithinAt ℝ (aV i) s t := by
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt
      |>.comp_differentiableWithinAt t hV
  have haW (i : Fin (Module.finrank ℝ E)) : DifferentiableWithinAt ℝ (aW i) s t := by
    exact (LinearMap.toContinuousLinearMap (b.coord i)).differentiableAt
      |>.comp_differentiableWithinAt t hW
  have hcoordX (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ X i (γ r)) (γ t)) s t := by
    exact differentiableWithinAt_sectionCoord γ (fun r ↦ X i (γ r))
      ((hframe i).comp_mdifferentiableWithinAt t hγ) hbase
  have hcoordTerm (a : Fin (Module.finrank ℝ E) → ℝ → ℝ)
      (ha : ∀ i, DifferentiableWithinAt ℝ (a i) s t)
      (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ
        (sectionCoord (F := E) γ (fun r ↦ a i r • X i (γ r)) (γ t)) s t := by
    rw [sectionCoord_smul]
    exact (ha i).smul (hcoordX i)
  have hcoordU (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (U i) (γ t)) s t :=
    hcoordTerm aV haV i
  have hcoordZ (i : Fin (Module.finrank ℝ E)) :
      DifferentiableWithinAt ℝ (sectionCoord (F := E) γ (Z i) (γ t)) s t :=
    hcoordTerm aW haW i
  -- Apply metric compatibility termwise, then sum both frame expansions.
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t) (U i) (Z j) := by
    exact ((hcov.hasMetricProductRuleWithinAt_pullback hu hγ (hframe i) (hframe j)).smul_left
      (haV i) (hcoordX i)).smul_right (haW j) (hcoordX j)
  have hsum : HasMetricProductRuleWithinAt (cov := cov) (s := s) (t := t)
      (fun r ↦ ∑ i, U i r) (fun r ↦ ∑ j, Z j r) := by
    refine HasMetricProductRuleWithinAt.finsetSum_left
      (A := Finset.univ) (U := U) (W := fun r ↦ ∑ j, Z j r) ?_ ?_
    · intro i hi
      exact HasMetricProductRuleWithinAt.finsetSum_right
        (A := Finset.univ) (hU := fun j _ ↦ hterm i j) (fun j _ ↦ hcoordZ j)
    · exact fun i _ ↦ hcoordU i
  -- The chosen frame expansion agrees with each original field near `t` and at `t` itself.
  have hnear : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hbase)
  have frameExpansion (Q : ∀ r, TangentSpace I (γ r)) :
      Q =ᶠ[𝓝[s] t] fun r ↦ ∑ i,
        b.repr (sectionCoord (F := E) γ Q (γ t) r) i • X i (γ r) := by
    filter_upwards [hnear] with r hr
    calc
      Q r = e.symmL ℝ (γ r) (sectionCoord (F := E) γ Q (γ t) r) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hr]
      _ = e.symmL ℝ (γ r)
          (∑ i, b.repr (sectionCoord (F := E) γ Q (γ t) r) i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i, b.repr (sectionCoord (F := E) γ Q (γ t) r) i • X i (γ r) := by
        simp only [map_sum, map_smul, X, symmL_basis_eq_localFrame b hr]
  have frameExpansionAt (Q : ∀ r, TangentSpace I (γ r)) :
      Q t = ∑ i, b.repr (sectionCoord (F := E) γ Q (γ t) t) i • X i (γ t) := by
    calc
      Q t = e.symmL ℝ (γ t) (sectionCoord (F := E) γ Q (γ t) t) := by
        rw [sectionCoord_apply, e.symmL_continuousLinearMapAt (R := ℝ) hbase]
      _ = e.symmL ℝ (γ t)
          (∑ i, b.repr (sectionCoord (F := E) γ Q (γ t) t) i • b i) := by
        rw [b.sum_repr]
      _ = ∑ i, b.repr (sectionCoord (F := E) γ Q (γ t) t) i • X i (γ t) := by
        simp only [map_sum, map_smul, X, symmL_basis_eq_localFrame b hbase]
  have hVsum : V =ᶠ[𝓝[s] t] fun r ↦ ∑ i, U i r := by
    simpa only [U, aV, b.coord_apply] using frameExpansion V
  have hWsum : W =ᶠ[𝓝[s] t] fun r ↦ ∑ i, Z i r := by
    simpa only [Z, aW, b.coord_apply] using frameExpansion W
  have hVt : V t = ∑ i, U i t := by
    simpa only [U, aV, b.coord_apply] using frameExpansionAt V
  have hWt : W t = ∑ i, Z i t := by
    simpa only [Z, aW, b.coord_apply] using frameExpansionAt W
  have hinner : (fun r ↦ inner ℝ (V r) (W r)) =ᶠ[𝓝[s] t]
      fun r ↦ inner ℝ (∑ i, U i r) (∑ j, Z j r) := by
    filter_upwards [hVsum, hWsum] with r hVr hWr
    rw [hVr, hWr]
    rfl
  have hDV : alongCurveWithin cov γ V s t =
      alongCurveWithin cov γ (fun r ↦ ∑ i, U i r) s t :=
    alongCurveWithin_congr cov γ V hVsum hVt
  have hDW : alongCurveWithin cov γ W s t =
      alongCurveWithin cov γ (fun r ↦ ∑ i, Z i r) s t :=
    alongCurveWithin_congr cov γ W hWsum hWt
  have hinnerAt : inner ℝ (V t) (W t) = inner ℝ (∑ i, U i t) (∑ j, Z j t) := by
    rw [hVt, hWt]
  refine (hsum.congr_of_eventuallyEq hinner hinnerAt).congr_deriv ?_
  rw [hDV, hDW, hVt, hWt]

/-- The within-set product rule for a metric-compatible covariant derivative acting on two
differentiable tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.hasDerivWithinAt_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    HasDerivWithinAt (fun r ↦ inner ℝ (V r) (W r))
      (inner ℝ (alongCurveWithin cov γ V s t) (W t) +
        inner ℝ (V t) (alongCurveWithin cov γ W s t)) s t :=
  hcov.hasMetricProductRuleWithinAt hu hγ hV hW

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable within the parameter set. -/
theorem IsMetricCompatible.differentiableWithinAt_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    DifferentiableWithinAt ℝ (fun r ↦ inner ℝ (V r) (W r)) s t :=
  (hcov.hasDerivWithinAt_inner_alongCurveWithin hu hγ hV hW).differentiableWithinAt

/-- The derivative identity supplied by metric compatibility within a parameter set. -/
theorem IsMetricCompatible.derivWithin_inner_alongCurveWithin
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hu : UniqueDiffWithinAt ℝ s t)
    (hγ : MDifferentiableWithinAt 𝓘(ℝ, ℝ) I γ s t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ V (γ t)) s t)
    (hW : DifferentiableWithinAt ℝ (sectionCoord (F := E) γ W (γ t)) s t) :
    derivWithin (fun r ↦ inner ℝ (V r) (W r)) s t =
      inner ℝ (alongCurveWithin cov γ V s t) (W t) +
        inner ℝ (V t) (alongCurveWithin cov γ W s t) :=
  (hcov.hasDerivWithinAt_inner_alongCurveWithin hu hγ hV hW).derivWithin hu

/-- The unrestricted product rule for a metric-compatible covariant derivative acting on two
differentiable tangent fields along a differentiable real curve. -/
theorem IsMetricCompatible.hasDerivAt_inner_alongCurve
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    HasDerivAt (fun r ↦ inner ℝ (V r) (W r))
      (inner ℝ (alongCurve cov γ V t) (W t) +
        inner ℝ (V t) (alongCurve cov γ W t)) t := by
  apply hasDerivWithinAt_univ.mp
  simpa only [alongCurveWithin_univ] using
    hcov.hasDerivWithinAt_inner_alongCurveWithin uniqueDiffWithinAt_univ
      hγ.mdifferentiableWithinAt hV.differentiableWithinAt hW.differentiableWithinAt

/-- The fibrewise inner product of two differentiable tangent fields along a differentiable curve
is differentiable. -/
theorem IsMetricCompatible.differentiableAt_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun x : M ↦ TangentSpace I x) cov)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    {V W : ∀ r, TangentSpace I (γ r)}
    (hV : DifferentiableAt ℝ (sectionCoord (F := E) γ V (γ t)) t)
    (hW : DifferentiableAt ℝ (sectionCoord (F := E) γ W (γ t)) t) :
    DifferentiableAt ℝ (fun r ↦ inner ℝ (V r) (W r)) t :=
  (hcov.hasDerivAt_inner_alongCurve hγ hV hW).differentiableAt

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
  (hcov.hasDerivAt_inner_alongCurve hγ hV hW).deriv

end CovariantDerivative

end
