/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Analysis.Calculus.Morse.Stable
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The split quadratic model of a Morse flow

This file studies the standard split-quadratic example of a negative-gradient flow.  On a product
of real Hilbert spaces, put

`q(x, y) = (‖x‖² - ‖y‖²) / 2`.

Its gradient is `(x, -y)`, so its negative-gradient flow is

`φ t (x, y) = (exp (-t) • x, exp t • y)`.

This file constructs that flow and computes its stable and unstable sets exactly.  The stable set
of the origin is the first coordinate plane and the unstable set is the second coordinate plane.
Thus the two sets in this normalized linear example are genuine closed linear subspaces, rather
than only sets defined by asymptotic convergence.  For a general Morse critical point, the metric
and Hessian determine the corresponding linearized gradient flow and its contraction rates.

## Main declarations

* `TauCeti.splitQuadratic`: the standard split quadratic function.
* `TauCeti.gradient_splitQuadratic`: its gradient is `(x, -y)`.
* `TauCeti.lipschitzWith_gradient_splitQuadratic`: its gradient is globally `1`-Lipschitz.
* `TauCeti.isNondegenerateCriticalPoint_splitQuadratic_zero`: the origin is nondegenerate.
* `TauCeti.splitQuadraticFlow`: its explicit negative-gradient flow.
* `Flow.isNegativeGradient_splitQuadraticFlow`: the flow solves the negative-gradient equation.
* `TauCeti.negativeGradientFlow_splitQuadratic`: the general construction of the negative gradient
  flow returns this explicit flow.
* `Flow.stableSet_splitQuadraticFlow_zero`: the stable set is the first coordinate plane.
* `Flow.unstableSet_splitQuadraticFlow_zero`: the unstable set is the second coordinate plane.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapters 1--2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace Set Topology
open scoped Gradient

noncomputable section

variable {Eₛ Eᵤ : Type*}
  [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]

namespace TauCeti

/-- The standard split quadratic function, positive on the first factor and negative on the
second.  The factor `2⁻¹` normalizes its gradient to `(x, -y)`. -/
def splitQuadratic (z : WithLp 2 (Eₛ × Eᵤ)) : ℝ :=
  (‖z.fst‖ ^ 2 - ‖z.snd‖ ^ 2) / 2

/-- Evaluation of the standard split quadratic function. -/
@[simp]
theorem splitQuadratic_apply (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitQuadratic z = (‖z.fst‖ ^ 2 - ‖z.snd‖ ^ 2) / 2 :=
  (rfl)

/-- The gradient of the split quadratic function is the identity on the first factor and minus
the identity on the second. -/
theorem hasGradientAt_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    HasGradientAt (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
      (WithLp.toLp 2 (z.fst, -z.snd)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert
    ((((WithLp.fstL 2 ℝ Eₛ Eᵤ).hasFDerivAt (x := z)).norm_sq.sub
      (((WithLp.sndL 2 ℝ Eₛ Eᵤ).hasFDerivAt (x := z)).norm_sq)).const_mul (2 : ℝ)⁻¹) using 1 <;>
    ext w <;>
    simp [splitQuadratic, WithLp.prod_inner_apply] <;> ring

/-- Formula for the gradient of the split quadratic function. -/
@[simp]
theorem gradient_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    ∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z =
      WithLp.toLp 2 (z.fst, -z.snd) := by
  exact (hasGradientAt_splitQuadratic z).gradient

/-- The origin is the unique critical point of the split quadratic function. -/
theorem gradient_splitQuadratic_eq_zero_iff [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ]
    (z : WithLp 2 (Eₛ × Eᵤ)) :
    ∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) z = 0 ↔ z = 0 := by
  rw [gradient_splitQuadratic]
  constructor
  · intro h
    apply WithLp.ofLp_injective
    apply Prod.ext
    · simpa using congrArg WithLp.fst h
    · simpa using congrArg WithLp.snd h
  · rintro rfl
    simp

/-- The gradient of the split quadratic function is an isometry of the underlying space, hence in
particular globally `1`-Lipschitz.  This is the hypothesis under which the negative gradient flow
of a function exists on the whole line. -/
theorem lipschitzWith_gradient_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    LipschitzWith 1 (∇ (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))) := by
  refine LipschitzWith.of_dist_le_mul fun z w ↦ ?_
  rw [NNReal.coe_one, one_mul, gradient_splitQuadratic, gradient_splitQuadratic,
    WithLp.prod_dist_eq_of_L2, WithLp.prod_dist_eq_of_L2]
  simp

/-- The origin is a nondegenerate critical point of the split quadratic function. -/
theorem isNondegenerateCriticalPoint_splitQuadratic_zero
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    IsNondegenerateCriticalPoint (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 := by
  -- Polarize the quadratic using the involution `(x, y) ↦ (x, -y)` and the Riesz equivalence.
  let e : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) :=
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ Eₛ)
      (LinearIsometryEquiv.neg ℝ : Eᵤ ≃ₗᵢ[ℝ] Eᵤ)).toContinuousLinearEquiv
  let half : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ)⁻¹ (by norm_num))
  let BEquiv : WithLp 2 (Eₛ × Eᵤ) ≃L[ℝ] WithLp 2 (Eₛ × Eᵤ) →L[ℝ] ℝ :=
    (e.trans half).trans
      (InnerProductSpace.toDual ℝ (WithLp 2 (Eₛ × Eᵤ))).toContinuousLinearEquiv
  let B : WithLp 2 (Eₛ × Eᵤ) →L[ℝ] WithLp 2 (Eₛ × Eᵤ) →L[ℝ] ℝ :=
    BEquiv
  have hsymm : B.flip = B := by
    ext z w
    simp [B, BEquiv, half, e, WithLp.prod_inner_apply, real_inner_comm]
  have hB : B.IsInvertible := by
    exact ⟨BEquiv, rfl⟩
  have h := ContinuousLinearMap.isNondegenerateCriticalPoint_apply_self_of_flip_eq_self B hsymm hB
  convert h using 1
  funext z
  simp [B, BEquiv, half, e, splitQuadratic, WithLp.prod_inner_apply]
  ring

section

variable [NormedSpace ℝ Eₛ] [NormedSpace ℝ Eᵤ]

/-- The explicit hyperbolic flow of the split quadratic function.  Its first coordinate contracts
in forward time and its second coordinate contracts in backward time. -/
def splitQuadraticFlow : _root_.Flow ℝ (WithLp 2 (Eₛ × Eᵤ)) where
  toFun t z := WithLp.toLp 2 (Real.exp (-t) • z.fst, Real.exp t • z.snd)
  cont' := by fun_prop
  map_add' t u z := by
    apply WithLp.ofLp_injective
    ext <;> simp [Real.exp_add, mul_smul, mul_comm]
  map_zero' z := by
    apply WithLp.ofLp_injective
    simp only [Real.exp_zero, neg_zero, one_smul]
    exact Prod.eta _

/-- Evaluation of the split quadratic flow. -/
@[simp]
theorem splitQuadraticFlow_apply (t : ℝ) (z : WithLp 2 (Eₛ × Eᵤ)) :
    splitQuadraticFlow t z =
      WithLp.toLp 2 (Real.exp (-t) • z.fst, Real.exp t • z.snd) :=
  (rfl)

end

end TauCeti

/-- Every orbit of the explicit split flow solves the negative-gradient equation for
`TauCeti.splitQuadratic`. -/
theorem Flow.isNegativeGradient_splitQuadraticFlow
    [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    Flow.IsNegativeGradient (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ))
      (TauCeti.splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ)) := by
  rw [Flow.isNegativeGradient_iff]
  intro z t
  have hs : HasDerivAt (fun u : ℝ ↦ Real.exp (-u) • z.fst)
      (-Real.exp (-t) • z.fst) t := by
    convert ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).smul_const z.fst using 1 <;>
      simp
  have hu : HasDerivAt (fun u : ℝ ↦ Real.exp u • z.snd) (Real.exp t • z.snd) t :=
    (Real.hasDerivAt_exp t).smul_const z.snd
  have hprod := hs.hasFDerivAt.prodMk hu.hasFDerivAt
  have htoLp :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ Eₛ Eᵤ).symm.hasFDerivAt.comp t hprod
  convert htoLp.hasDerivAt using 1
  · funext u
    simp only [TauCeti.splitQuadraticFlow_apply, Function.comp_apply,
      WithLp.prodContinuousLinearEquiv_symm_apply]
  · -- Expose the vector-field value so the explicit gradient formula rewrites the goal.
    change -∇ TauCeti.splitQuadratic
        (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ) t z) = _
    rw [TauCeti.gradient_splitQuadratic]
    apply WithLp.ofLp_injective
    ext <;> simp

namespace TauCeti

/-- On the split quadratic model, the negative gradient flow built from a globally Lipschitz
gradient is the explicit hyperbolic flow. -/
theorem negativeGradientFlow_splitQuadratic [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ]
    [CompleteSpace Eₛ] [CompleteSpace Eᵤ] :
    negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
        lipschitzWith_gradient_splitQuadratic = splitQuadraticFlow := by
  refine _root_.Flow.ext fun t z ↦ ?_
  have hγ := (Flow.isNegativeGradient_splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)).isIntegralCurve z
  have h := eq_negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
    lipschitzWith_gradient_splitQuadratic hγ t
  have h0 : splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 z = z := _root_.Flow.map_zero_apply _ z
  rw [h0] at h
  exact h.symm

end TauCeti

variable [NormedSpace ℝ Eₛ] [NormedSpace ℝ Eᵤ]

namespace TauCeti

private theorem tendsto_exp_neg_smul_atTop (x : Eₛ) :
    Tendsto (fun t : ℝ ↦ Real.exp (-t) • x) atTop (𝓝 0) :=
  by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.smul_const x

private theorem tendsto_exp_smul_atBot (y : Eᵤ) :
    Tendsto (fun t : ℝ ↦ Real.exp t • y) atBot (𝓝 0) :=
  by simpa using Real.tendsto_exp_atBot.smul_const y

private theorem eq_zero_of_tendsto_exp_smul_atTop {y : Eᵤ}
    (h : Tendsto (fun t : ℝ ↦ Real.exp t • y) atTop (𝓝 0)) : y = 0 := by
  have h' := Real.tendsto_exp_neg_atTop_nhds_zero.smul h
  have hy : Tendsto (fun _ : ℝ ↦ y) atTop (𝓝 0) := by
    convert h' using 1 <;> simp [smul_smul, ← Real.exp_add]
  exact tendsto_nhds_unique tendsto_const_nhds hy

private theorem eq_zero_of_tendsto_exp_neg_smul_atBot {x : Eₛ}
    (h : Tendsto (fun t : ℝ ↦ Real.exp (-t) • x) atBot (𝓝 0)) : x = 0 := by
  have h' := Real.tendsto_exp_atBot.smul h
  have hx : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 0) := by
    convert h' using 1 <;> simp [smul_smul, ← Real.exp_add]
  exact tendsto_nhds_unique tendsto_const_nhds hx

/-- A point converges to the origin in forward time exactly when its expanding coordinate
vanishes. -/
theorem tendsto_splitQuadraticFlow_atTop_nhds_zero_iff (z : WithLp 2 (Eₛ × Eᵤ)) :
    Tendsto (fun t ↦ splitQuadraticFlow t z) atTop (𝓝 0) ↔ z.snd = 0 := by
  constructor
  · intro h
    exact eq_zero_of_tendsto_exp_smul_atTop
      (((WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.tendsto.comp h).congr'
        (Eventually.of_forall fun t ↦ by
          simp only [Function.comp_apply, splitQuadraticFlow_apply, WithLp.sndL_apply,
            WithLp.toLp_snd]))
  · intro hz
    have hzero : Tendsto (fun _ : ℝ ↦ (0 : Eᵤ)) atTop (𝓝 0) := tendsto_const_nhds
    have hprod := (tendsto_exp_neg_smul_atTop z.fst).prodMk_nhds
      hzero
    have hto := (WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp hprod
    convert hto using 1
    · simp [Function.comp_def, hz]
    · exact congrArg 𝓝 (WithLp.toLp_zero (V := Eₛ × Eᵤ) 2).symm

/-- A point converges to the origin in backward time exactly when its expanding-backward
coordinate vanishes. -/
theorem tendsto_splitQuadraticFlow_atBot_nhds_zero_iff (z : WithLp 2 (Eₛ × Eᵤ)) :
    Tendsto (fun t ↦ splitQuadraticFlow t z) atBot (𝓝 0) ↔ z.fst = 0 := by
  constructor
  · intro h
    exact eq_zero_of_tendsto_exp_neg_smul_atBot
      (((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.tendsto.comp h).congr'
        (Eventually.of_forall fun t ↦ by
          simp only [Function.comp_apply, splitQuadraticFlow_apply, WithLp.fstL_apply,
            WithLp.toLp_fst]))
  · intro hz
    have hzero : Tendsto (fun _ : ℝ ↦ (0 : Eₛ)) atBot (𝓝 0) := tendsto_const_nhds
    have hprod := hzero.prodMk_nhds (tendsto_exp_smul_atBot z.snd)
    have hto := (WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).continuousAt.tendsto.comp hprod
    convert hto using 1
    · simp [Function.comp_def, hz]
    · exact congrArg 𝓝 (WithLp.toLp_zero (V := Eₛ × Eᵤ) 2).symm

end TauCeti

namespace Flow

/-- The stable set of the split quadratic flow at the origin is the first coordinate plane. -/
@[simp]
theorem stableSet_splitQuadraticFlow_zero :
    stableSet (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 =
      {z : WithLp 2 (Eₛ × Eᵤ) | z.snd = 0} := by
  ext z
  rw [mem_stableSet, TauCeti.tendsto_splitQuadraticFlow_atTop_nhds_zero_iff]
  rfl

/-- The unstable set of the split quadratic flow at the origin is the second coordinate plane. -/
@[simp]
theorem unstableSet_splitQuadraticFlow_zero :
    unstableSet (TauCeti.splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)) 0 =
      {z : WithLp 2 (Eₛ × Eᵤ) | z.fst = 0} := by
  ext z
  rw [mem_unstableSet, TauCeti.tendsto_splitQuadraticFlow_atBot_nhds_zero_iff]
  rfl

end Flow

end
