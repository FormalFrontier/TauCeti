/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep
public import TauCeti.Analysis.Sobolev.W1p.Basic

/-!
# Arbitrary-order weak Sobolev spaces

This file constructs the real-valued Sobolev space `W^{k,p}(Ω)` for every positive integer
`k`, on an open subset of a finite-dimensional real inner product space.  The first-order stage
is `TauCeti.W1p`.  Every successor stage applies `TauCeti.WeakDerivStep` to the highest weak
derivative of the preceding stage.  Thus an element of `W^{k+1,p}(Ω)` records an element of
`W^{k,p}(Ω)` and an `Lᵖ` weak derivative of its order-`k` derivative.

The iterated derivative fields are basis-free.  `TauCeti.IteratedGradient E 0` is `E`, the weak
gradient identified with a linear functional by the real inner product, and
`TauCeti.IteratedGradient E (j+1)` is `E →L[ℝ] IteratedGradient E j`.  Consequently the highest
field of `W^{k+1,p}` has type `Lᵖ(Ω; IteratedGradient E k)`.

Every stage is a closed weak-derivative graph, hence complete.  No boundedness or boundary
regularity of `Ω` is used.  The graph norm is obtained recursively from Euclidean product norms;
at exponent two its square is the sum of the squared `L²` norms of the value and all weak
derivatives through order `k`.

## Main declarations

* `TauCeti.IteratedGradient`: the basis-free target of an iterated weak derivative.
* `TauCeti.Wkp`: `W^{k,p}(Ω)`, with `Wkp 0 = Lᵖ(Ω)` and `Wkp 1 = W1p`.
* `TauCeti.Wkp.lowerOrder`: the continuous projection `W^{k+1,p} → W^{k,p}`.
* `TauCeti.Wkp.deriv`: the highest weak derivative of a positive-order Sobolev function.
* `TauCeti.Wkp.hasWeakFDerivOn_deriv`: adjacent recorded derivatives satisfy the weak
  derivative identity.

## References

This completes the arbitrary-order space and completeness part of Lane A.1, target 1, in
`TauCetiRoadmap/PDE/README.md`.  The iterated weak-derivative definition and closed-graph
completeness argument follow L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

universe u

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 <= p)]

/-- The normed-space data underlying an iterated weak gradient. -/
structure IteratedGradientModel (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The carrier space for the iterated weak gradient. -/
  Space : Type u
  /-- The normed additive commutative group structure on `Space`. -/
  [normedAddCommGroup : NormedAddCommGroup Space]
  /-- The normed `ℝ`-space structure on `Space`. -/
  [normedSpace : NormedSpace ℝ Space]

/-- The recursively bundled target of an iterated weak gradient. -/
@[reducible, expose] noncomputable def iteratedGradientModel (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : ℕ → IteratedGradientModel E
  | 0 => { Space := E }
  | j + 1 =>
      let S := iteratedGradientModel E j
      letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
      letI : NormedSpace ℝ S.Space := S.normedSpace
      { Space := E →L[ℝ] S.Space }

/-- The target of the iterated weak gradient of order `j + 1`.  Order zero is the gradient
vector `E`; each successor adds one continuous-linear derivative direction on the left. -/
abbrev IteratedGradient (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (j : ℕ) : Type u :=
  (iteratedGradientModel E j).Space

noncomputable instance (j : ℕ) : NormedAddCommGroup (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedAddCommGroup

noncomputable instance (j : ℕ) : NormedSpace ℝ (IteratedGradient E j) :=
  (iteratedGradientModel E j).normedSpace

noncomputable instance [CompleteSpace E] (j : ℕ) : CompleteSpace (IteratedGradient E j) := by
  induction j with
  | zero => exact inferInstance
  | succ j ih =>
      let _ : CompleteSpace (IteratedGradient E j) := ih
      exact inferInstance

/-- The bundled data used to iterate weak-derivative graph spaces.  Its `j`th stage carries the
space of order `j + 1`, its one-order-lower projection, and its highest derivative projection. -/
structure SobolevStage (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] (j : ℕ) where
  /-- The Sobolev space of order `j + 1`. -/
  Space : Type u
  /-- The normed additive commutative group structure on the order-`j + 1` Sobolev space. -/
  [normedAddCommGroup : NormedAddCommGroup Space]
  /-- The normed `ℝ`-space structure on the order-`j + 1` Sobolev space. -/
  [normedSpace : NormedSpace ℝ Space]
  /-- The completeness instance for the order-`j + 1` Sobolev space. -/
  [completeSpace : CompleteSpace Space]
  /-- The Sobolev space of order `j`. -/
  Lower : Type u
  /-- The normed additive commutative group structure on the order-`j` Sobolev space. -/
  [lowerNormedAddCommGroup : NormedAddCommGroup Lower]
  /-- The normed `ℝ`-space structure on the order-`j` Sobolev space. -/
  [lowerNormedSpace : NormedSpace ℝ Lower]
  /-- The continuous projection to the one-order-lower Sobolev space. -/
  lowerL : Space →L[ℝ] Lower
  /-- The continuous projection to the highest weak derivative field. -/
  derivL : Space →L[ℝ] Lp (IteratedGradient E j) p (mu.restrict Omega)

/-- The first stage of the arbitrary-order construction is `W1p`, with value and gradient as
its lower-order and highest-derivative projections. -/
@[reducible, expose] noncomputable def firstSobolevStage : SobolevStage mu Omega p 0 where
  Space := W1p mu Omega p
  Lower := Lp ℝ p (mu.restrict Omega)
  lowerL := W1p.valueL
  derivL := W1p.gradientL

/-- Adjoin the weak derivative of a stage's highest derivative field. -/
@[reducible, expose] noncomputable def SobolevStage.next (S : SobolevStage mu Omega p j) :
    SobolevStage mu Omega p (j + 1) := by
  letI : NormedAddCommGroup S.Space := S.normedAddCommGroup
  letI : NormedSpace ℝ S.Space := S.normedSpace
  letI : CompleteSpace S.Space := S.completeSpace
  exact
    { Space := WeakDerivStep mu Omega p S.derivL
      Lower := S.Space
      lowerL := WeakDerivStep.prevL S.derivL
      derivL := WeakDerivStep.weakFDerivL S.derivL }

/-- The `j`th iterated weak-derivative stage, representing Sobolev order `j + 1`. -/
@[reducible, expose] noncomputable def sobolevStage : (j : ℕ) → SobolevStage mu Omega p j
  | 0 => firstSobolevStage
  | j + 1 => (sobolevStage j).next

@[instance_reducible, expose] noncomputable def SobolevStage.instNormedAddCommGroup
    (j : ℕ) : NormedAddCommGroup
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedAddCommGroup

attribute [instance] SobolevStage.instNormedAddCommGroup

@[instance_reducible, expose] noncomputable def SobolevStage.instNormedSpace
    (j : ℕ) : NormedSpace ℝ
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).normedSpace

attribute [instance] SobolevStage.instNormedSpace

theorem SobolevStage.instCompleteSpace (j : ℕ) :
    CompleteSpace (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).Space :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) j).completeSpace

attribute [instance] SobolevStage.instCompleteSpace

/-- The arbitrary-order, real-valued weak Sobolev space `W^{k,p}(Ω)`.  At order zero this is
`Lᵖ(Ω)`; order one is `W1p`; every further order adjoins the weak derivative of the highest
derivative field from the preceding order. -/
@[reducible, expose] noncomputable def Wkp (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 <= p)] : ℕ → Type u
  | 0 => Lp ℝ p (mu.restrict Omega)
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).Space

@[instance_reducible, expose] noncomputable def Wkp.instNormedAddCommGroup :
    (k : ℕ) → NormedAddCommGroup (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedAddCommGroup

attribute [instance] Wkp.instNormedAddCommGroup

@[instance_reducible, expose] noncomputable def Wkp.instNormedSpace :
    (k : ℕ) → NormedSpace ℝ (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).normedSpace

attribute [instance] Wkp.instNormedSpace

/-- Every weak Sobolev space `W^{k,p}(Ω)` is complete in its iterated graph norm. -/
theorem Wkp.instCompleteSpace :
    (k : ℕ) → CompleteSpace (Wkp mu Omega p k)
  | 0 => inferInstance
  | k + 1 => (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).completeSpace

attribute [instance] Wkp.instCompleteSpace

namespace Wkp

/-- The continuous projection that forgets the highest weak derivative. -/
@[expose] def lowerOrderL : (k : ℕ) → Wkp mu Omega p (k + 1) →L[ℝ] Wkp mu Omega p k
  | 0 => W1p.valueL
  | k + 1 => WeakDerivStep.prevL
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL

/-- A positive-order Sobolev function regarded as a Sobolev function of one lower order. -/
@[expose] def lowerOrder (k : ℕ) (u : Wkp mu Omega p (k + 1)) : Wkp mu Omega p k :=
  lowerOrderL k u

/-- Evaluating the continuous lower-order projection equals `lowerOrder`. -/
theorem lowerOrderL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    lowerOrderL k u = lowerOrder k u :=
  (rfl)

/-- The continuous projection to the highest weak derivative of a positive-order Sobolev
function.  For `W^{k+1,p}` its target is `Lᵖ(Ω; IteratedGradient E k)`. -/
@[expose] def derivL (k : ℕ) : Wkp mu Omega p (k + 1) →L[ℝ]
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL

/-- The highest weak derivative recorded by a positive-order Sobolev function. -/
@[expose] def deriv (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  derivL k u

/-- Evaluating the continuous highest-derivative projection equals `deriv`. -/
theorem derivL_apply (k : ℕ) (u : Wkp mu Omega p (k + 1)) : derivL k u = deriv k u :=
  (rfl)

/-- The continuous projection of a Sobolev function to its `Lᵖ` value component. -/
@[expose] def valueL : (k : ℕ) → Wkp mu Omega p k →L[ℝ] Lp ℝ p (mu.restrict Omega)
  | 0 => ContinuousLinearMap.id ℝ _
  | k + 1 => (valueL k).comp (lowerOrderL k)

/-- The `Lᵖ` value component of an arbitrary-order Sobolev function. -/
@[expose] def value (k : ℕ) (u : Wkp mu Omega p k) : Lp ℝ p (mu.restrict Omega) :=
  valueL k u

@[simp]
theorem valueL_apply (k : ℕ) (u : Wkp mu Omega p k) : valueL k u = value k u :=
  (rfl)

@[simp]
theorem value_zero (u : Wkp mu Omega p 0) : value 0 u = u :=
  by simp only [value, valueL, ContinuousLinearMap.id_apply]

/-- Taking the value component commutes with forgetting the highest derivative. -/
theorem value_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    value (k + 1) u = value k (lowerOrder k u) :=
  by simp only [value, valueL, lowerOrder, ContinuousLinearMap.comp_apply]

/-- At first order, the generic lower-order projection is the `W1p` value projection. -/
theorem lowerOrder_zero (u : Wkp mu Omega p 1) : lowerOrder 0 u = W1p.value u :=
  by
    simpa only [lowerOrder, lowerOrderL, Wkp, sobolevStage, firstSobolevStage] using
      W1p.valueL_apply u

/-- At first order, the generic highest derivative is the `W1p` weak gradient. -/
theorem deriv_zero (u : Wkp mu Omega p 1) : deriv 0 u = W1p.gradient u :=
  by
    simpa only [deriv, derivL, Wkp, sobolevStage, firstSobolevStage] using
      W1p.gradientL_apply u

/-- The highest derivative projection is the one stored in the corresponding recursive stage. -/
theorem deriv_eq_stage (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    deriv k u = (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u :=
  rfl

/-- Above first order, the lower-order projection is the preceding-component projection of the
generic weak-derivative graph step. -/
theorem lowerOrder_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    lowerOrder (k + 1) u = WeakDerivStep.prev
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u := by
  exact WeakDerivStep.prevL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

/-- Above first order, the highest derivative is the derivative component of the generic
weak-derivative graph step. -/
theorem deriv_succ (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    deriv (k + 1) u = WeakDerivStep.weakFDeriv
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u := by
  exact WeakDerivStep.weakFDerivL_apply
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

/-- The first weak derivative identity, with the gradient identified with a linear functional
through the real inner product. -/
theorem hasWeakFDerivOn_value (u : Wkp mu Omega p 1) :
    HasWeakFDerivOn mu Omega (value 1 u) (fun x => innerSL ℝ (deriv 0 u x)) := by
  simpa only [value_succ, value_zero, lowerOrder_zero, deriv_zero] using W1p.hasWeakFDerivOn u

/-- Construct an order-`k+2` Sobolev function from an order-`k+1` function and a weak
derivative of its highest derivative. -/
def mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (deriv k u) D) : Wkp mu Omega p (k + 2) := by
  exact WeakDerivStep.mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u D
      (by simpa only [deriv_eq_stage] using h)

@[simp]
theorem lowerOrder_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (deriv k u) D) :
    lowerOrder (k + 1) (mk k u D h) = u := by
  rw [lowerOrder_succ]
  have h' := h
  rw [deriv_eq_stage] at h'
  exact WeakDerivStep.prev_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u D h'

@[simp]
theorem deriv_mk (k : ℕ) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (deriv k u) D) : deriv (k + 1) (mk k u D h) = D := by
  rw [deriv_succ]
  have h' := h
  rw [deriv_eq_stage] at h'
  exact WeakDerivStep.weakFDeriv_mk
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u D h'

/-- The highest derivative of an order-`k+2` Sobolev function is the weak Fréchet derivative
of the highest derivative of its order-`k+1` projection. -/
theorem hasWeakFDerivOn_deriv (k : ℕ) (u : Wkp mu Omega p (k + 2)) :
    HasWeakFDerivOn mu Omega (deriv k (lowerOrder (k + 1) u)) (deriv (k + 1) u) := by
  rw [deriv_eq_stage, lowerOrder_succ, deriv_succ]
  exact WeakDerivStep.hasWeakFDerivOn_base_prev
    (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

/-- Two order-`k+2` Sobolev functions are equal when their lower-order components and highest
derivatives are equal. -/
theorem ext_lowerOrder_deriv (k : ℕ) {u v : Wkp mu Omega p (k + 2)}
    (hlower : lowerOrder (k + 1) u = lowerOrder (k + 1) v)
    (hderiv : deriv (k + 1) u = deriv (k + 1) v) : u = v := by
  rw [lowerOrder_succ, lowerOrder_succ] at hlower
  rw [deriv_succ, deriv_succ] at hderiv
  exact WeakDerivStep.ext_prev_weakFDeriv hlower hderiv

/-- Two order-`k+2` Sobolev functions are equal when their lower-order components are equal;
uniqueness of weak derivatives determines the highest components. -/
theorem ext_lowerOrder (k : ℕ) {u v : Wkp mu Omega p (k + 2)}
    (h : lowerOrder (k + 1) u = lowerOrder (k + 1) v) : u = v := by
  rw [lowerOrder_succ, lowerOrder_succ] at h
  exact WeakDerivStep.ext h

/-- Two arbitrary-order Sobolev functions are equal when their `Lᵖ` value components are equal.
Successive uniqueness of weak derivatives determines every higher component. -/
@[ext]
theorem ext : ∀ (k : ℕ) {u v : Wkp mu Omega p k}, value k u = value k v → u = v
  | 0, _, _, h => by simpa only [value_zero] using h
  | 1, _, _, h => W1p.ext_value (by
      simpa only [value_succ, value_zero, lowerOrder_zero] using h)
  | k + 2, _, _, h => ext_lowerOrder k (ext (k + 1) (by
      simpa only [value_succ] using h))

/-- The graph norm controls the one-order-lower Sobolev component. -/
theorem norm_lowerOrder_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ‖lowerOrder k u‖ ≤ ‖u‖ := by
  cases k with
  | zero => simpa only [lowerOrder_zero] using W1p.norm_value_le u
  | succ k =>
      simpa only [lowerOrder_succ] using WeakDerivStep.norm_prev_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

/-- The iterated graph norm controls the `Lᵖ` value component at every order. -/
theorem norm_value_le : ∀ (k : ℕ) (u : Wkp mu Omega p k), ‖value k u‖ ≤ ‖u‖
  | 0, u => by simpa only [value_zero] using le_rfl
  | k + 1, u =>
      (norm_value_le k (lowerOrder k u)).trans (norm_lowerOrder_le k u)

/-- The graph norm controls the highest weak derivative. -/
theorem norm_deriv_le (k : ℕ) (u : Wkp mu Omega p (k + 1)) : ‖deriv k u‖ ≤ ‖u‖ := by
  cases k with
  | zero => simpa only [deriv_zero] using W1p.norm_gradient_le u
  | succ k =>
      simpa only [deriv_succ] using WeakDerivStep.norm_weakFDeriv_le
        (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

/-- From second order onward, the squared graph norm is the sum of the squared norm of the
lower-order component and the squared norm of the highest weak derivative. -/
theorem norm_sq_eq_norm_lowerOrder_sq_add_norm_deriv_sq (k : ℕ)
    (u : Wkp mu Omega p (k + 2)) :
    ‖u‖ ^ 2 = ‖lowerOrder (k + 1) u‖ ^ 2 + ‖deriv (k + 1) u‖ ^ 2 := by
  simpa only [lowerOrder_succ, deriv_succ] using
    WeakDerivStep.norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq
      (sobolevStage (mu := mu) (Omega := Omega) (p := p) k).derivL u

end Wkp

end TauCeti
