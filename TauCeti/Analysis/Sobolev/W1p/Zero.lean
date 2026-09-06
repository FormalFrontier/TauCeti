/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic

import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The Sobolev space `W^{1,p}_0(Ω)`

This file builds `W^{1,p}_0(Ω)`, the closure of the test functions `C_c^∞(Ω)` inside the weak
Sobolev space `W^{1,p}(Ω)` of `TauCeti/Analysis/Sobolev/W1p/Basic.lean`. This is the
`C_c^∞(Ω)`-closure half of Lane A.2 of `TauCetiRoadmap/PDE/README.md`; Meyers--Serrin density is
not proved here.

## Test functions as Sobolev functions

The embedding `C_c^∞(Ω) → W^{1,p}(Ω)` sends `φ` to the value-gradient jet `(φ, ∇φ)`, where `∇`
is Mathlib's `gradient`, the Riesz representative of the Fréchet derivative. Two things have to be
checked, and both are easy for a test function: the jet is `Lᵖ`, because `φ` and `∇φ` are
continuous with compact support; and the weak-derivative identity holds, because `∇φ` represents
the *classical* derivative, which is a weak derivative by
`TauCeti.hasWeakFDerivOn_of_differentiableOn`. The embedding is linear
(`TauCeti.W1p.ofTestFunctionₗ`), which is what makes its range a subspace.

## Why the closure, and why not all of `W^{1,p}(Ω)`

`W^{1,p}_0(Ω)` is defined as `TauCeti.w1p0Submodule`, the topological closure of that range. It is
the Sobolev-space stand-in for the homogeneous Dirichlet boundary condition `u|_{∂Ω} = 0`: no
boundary regularity of `Ω` is assumed, and no trace operator is needed to state it. The
distinction from `W^{1,p}(Ω)` is real: for example, the Poincaré inequality holds on this closed
subspace under a suitable geometric hypothesis but not on all of `W^{1,p}(Ω)`.

## Main declarations

* `TauCeti.W1p.ofTestFunctionₗ` and `TauCeti.W1p.ofTestFunctionₗ_injective`: the linear embedding
  `C_c^∞(Ω) → W^{1,p}(Ω)`, and its injectivity.
* `TauCeti.w1p0Submodule` and `TauCeti.W1p0`: the space `W^{1,p}_0(Ω)`, complete for the graph
  norm.
* `TauCeti.W1p0.valueL`: the canonical continuous value map into `Lᵖ(Ω)`.
* `TauCeti.W1p0.denseRange_valueL_two`: test functions make the value map from
  `W^{1,2}_0(Ω)` dense in `L²(Ω)`, and `TauCeti.W1p0.valueL_ne_zero`: on a nonempty `Ω` the value
  map is nonzero for every `p`.
* `TauCeti.w1p0Submodule_subset_of_isClosed`: a closed set containing every test-function jet
  contains `W^{1,p}_0(Ω)`, which is how a property is extended from test functions to the whole
  space.

## References

The `C_c^∞(Ω)`-closure half of Lane A.2 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans,
*Partial Differential Equations*, Section 5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Test functions as Sobolev functions -/

omit [Fact (1 ≤ p)] in
private theorem hasWeakFDerivOn_testFunctionLp (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (testFunctionLp (mu := mu) p phi)
      fun x => innerSL ℝ (gradientTestFunctionLp (mu := mu) p phi x) := by
  refine ((hasWeakFDerivOn_testFunction (μ := mu) phi).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [testFunctionLp_apply_ae (mu := mu) p phi] with x hx using hx.symm
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) p phi] with x hx
    rw [hx]

/-- **The test functions inside `W^{1,p}(Ω)`**: the linear embedding sending `φ ∈ C_c^∞(Ω)` to the
value-gradient jet `(φ, ∇φ)`. Linearity is what makes the range a subspace, hence its closure
`TauCeti.w1p0Submodule` a subspace too. -/
def W1p.ofTestFunctionₗ (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : 𝓓(Omega, ℝ) →ₗ[ℝ] W1p mu Omega p where
  toFun phi := W1p.mk (testFunctionLp p phi) (gradientTestFunctionLp p phi)
    (hasWeakFDerivOn_testFunctionLp phi)
  map_add' phi psi := by
    apply W1p.ext <;>
      simp only [← W1p.valueL_apply, ← W1p.gradientL_apply, map_add] <;> simp
  map_smul' c phi := by
    apply W1p.ext <;>
      simp only [← W1p.valueL_apply, ← W1p.gradientL_apply, map_smul] <;> simp

@[simp]
theorem W1p.value_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    W1p.value (W1p.ofTestFunctionₗ mu Omega p phi) = testFunctionLp p phi :=
  W1p.value_mk _ _ _

@[simp]
theorem W1p.gradient_ofTestFunctionₗ (phi : 𝓓(Omega, ℝ)) :
    W1p.gradient (W1p.ofTestFunctionₗ mu Omega p phi) = gradientTestFunctionLp p phi :=
  W1p.gradient_mk _ _ _

/-- The embedding of the test functions is **injective**: two test functions with the same jet
agree almost everywhere on `Ω`, hence everywhere, being continuous, supported in `Ω`, and measured
by a Haar measure, which is positive on nonempty open sets. So `W^{1,p}(Ω)` really does contain a
copy of `C_c^∞(Ω)`, not just a quotient of it. -/
theorem W1p.ofTestFunctionₗ_injective :
    Function.Injective (W1p.ofTestFunctionₗ mu Omega p) := by
  intro phi psi h
  apply testFunctionLp_injective (nu := mu) (U := Omega) p
  simpa using congrArg W1p.value h

/-! ### The space `W^{1,p}_0(Ω)` -/

/-- **The closed subspace `W^{1,p}_0(Ω)` of `W^{1,p}(Ω)`**: the closure of the test functions
`C_c^∞(Ω)`, the Sobolev formulation of the homogeneous Dirichlet boundary condition. No
regularity, and no boundedness, of `Ω` is assumed. -/
def w1p0Submodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : ClosedSubmodule ℝ (W1p mu Omega p) :=
  (LinearMap.range (W1p.ofTestFunctionₗ mu Omega p)).closure

/-- `W^{1,p}_0(Ω)` is the closure of the set of test-function jets. -/
theorem coe_w1p0Submodule :
    (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) =
      closure (Set.range (W1p.ofTestFunctionₗ mu Omega p)) := by
  rw [w1p0Submodule, Submodule.coe_closure, LinearMap.coe_range]

/-- A test function, viewed in `W^{1,p}(Ω)`, lies in `W^{1,p}_0(Ω)`. -/
theorem W1p.ofTestFunctionₗ_mem_w1p0Submodule (phi : 𝓓(Omega, ℝ)) :
    W1p.ofTestFunctionₗ mu Omega p phi ∈ w1p0Submodule mu Omega p :=
  Submodule.mem_closure_iff.2 (Submodule.le_topologicalClosure _ ⟨phi, rfl⟩)

/-- **Minimality of the closure**: a closed set containing every test-function jet contains all
of `W^{1,p}_0(Ω)`. -/
theorem w1p0Submodule_subset_of_isClosed {s : Set (W1p mu Omega p)} (hs : IsClosed s)
    (h : ∀ phi, W1p.ofTestFunctionₗ mu Omega p phi ∈ s) :
    (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) ⊆ s := by
  rw [coe_w1p0Submodule]
  exact closure_minimal (by rintro _ ⟨phi, rfl⟩; exact h phi) hs

/-- **The Sobolev space `W^{1,p}_0(Ω)`**, the closure of `C_c^∞(Ω)` in `W^{1,p}(Ω)`. -/
abbrev W1p0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] := (w1p0Submodule mu Omega p).toSubmodule

/-- Shortcut instance for the norm `W^{1,p}_0(Ω)` inherits through the two nested Sobolev
subspaces; instance search does not find it on its own. -/
noncomputable instance instSeminormedAddCommGroupW1p0 :
    SeminormedAddCommGroup (W1p0 mu Omega p) := inferInstance

/-- Shortcut instance for the scalar action `W^{1,p}_0(Ω)` inherits through the two nested
Sobolev subspaces. -/
noncomputable instance instNormedSpaceW1p0 : NormedSpace ℝ (W1p0 mu Omega p) := inferInstance

/-- **The canonical value map of `W^{1,p}_0(Ω)`**, the value component of the Sobolev jet read
off a zero-boundary function, as a continuous linear map into `Lᵖ(Ω)`. -/
def W1p0.valueL : W1p0 mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) :=
  W1p.valueL.comp (w1p0Submodule mu Omega p).toSubmodule.subtypeL

@[simp]
theorem W1p0.valueL_apply (u : W1p0 mu Omega p) :
    W1p0.valueL u = W1p.value (u : W1p mu Omega p) :=
  by simp [W1p0.valueL]

/-- The value map `W^{1,2}_0(Ω) → L²(Ω)` has dense range.  Indeed, its range contains
all test functions, and an `L²` function orthogonal to every test function vanishes almost
everywhere by the fundamental lemma of the calculus of variations. -/
theorem W1p0.denseRange_valueL_two :
    DenseRange (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) := by
  have hcoe : (LinearMap.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2) :
      W1p0 mu Omega 2 →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) :
        Set (Lp ℝ 2 (mu.restrict Omega))) =
      Set.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2)) := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  have hdense : Dense ((LinearMap.range (W1p0.valueL (mu := mu) (Omega := Omega) (p := 2) :
      W1p0 mu Omega 2 →ₗ[ℝ] Lp ℝ 2 (mu.restrict Omega)) :
        Set (Lp ℝ 2 (mu.restrict Omega)))) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro f hf
    apply Lp.ext
    have hzero : ∀ᵐ x ∂mu.restrict Omega, f x = 0 := by
      rw [ae_restrict_iff' Omega.isOpen.measurableSet]
      refine Omega.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((Lp.memLp f).locallyIntegrable (by simp))) fun g hg hgc hgs => ?_
      let phi : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
      let u : W1p0 mu Omega 2 :=
        ⟨W1p.ofTestFunctionₗ mu Omega 2 phi, W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩
      have hinner : ⟪W1p0.valueL u, f⟫_ℝ = 0 := hf _ ⟨u, rfl⟩
      rw [L2.inner_def, W1p0.valueL_apply, W1p.value_ofTestFunctionₗ] at hinner
      calc
        ∫ x, g x • f x ∂mu = ∫ x in Omega, g x • f x ∂mu := by
          rw [← integral_indicator Omega.isOpen.measurableSet]
          congr 1
          symm
          apply Set.indicator_eq_self.2
          exact (Function.support_smul_subset_left g fun x => f x).trans
            ((subset_tsupport g).trans hgs)
        _ = 0 := by
          rw [← hinner]
          apply integral_congr_ae
          filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 phi] with x hx
          rw [hx]
          exact mul_comm _ _
    exact Filter.EventuallyEq.trans hzero
      (Lp.coeFn_zero ℝ 2 (mu.restrict Omega)).symm
  rw [hcoe] at hdense
  exact hdense

/-- A nonempty open set contains a zero-boundary Sobolev function with nonzero `Lᵖ` value. -/
theorem W1p0.exists_value_ne_zero (hOmega : (Omega : Set E).Nonempty) :
    ∃ w : W1p0 mu Omega p, W1p.value (w : W1p mu Omega p) ≠ 0 := by
  obtain ⟨x, hx⟩ := hOmega
  obtain ⟨g, hgs, hgc, hg, _, hgx⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (Omega.isOpen.mem_nhds hx)
  let phi : 𝓓(Omega, ℝ) := ⟨g, hg, hgc, hgs⟩
  let w : W1p0 mu Omega p :=
    ⟨W1p.ofTestFunctionₗ mu Omega p phi, W1p.ofTestFunctionₗ_mem_w1p0Submodule phi⟩
  refine ⟨w, ?_⟩
  rw [W1p.value_ofTestFunctionₗ]
  intro hzero
  have hzeroTest : testFunctionLp (mu := mu) (Omega := Omega) p (0 : 𝓓(Omega, ℝ)) = 0 := by
    apply Lp.ext
    exact Filter.EventuallyEq.trans
      (testFunctionLp_apply_ae (mu := mu) p (0 : 𝓓(Omega, ℝ)))
      (Lp.coeFn_zero ℝ p (mu.restrict Omega)).symm
  have hphi : phi = 0 := testFunctionLp_injective p (hzero.trans hzeroTest.symm)
  have : g x = 0 := by
    have := congrArg (fun q : 𝓓(Omega, ℝ) => q x) hphi
    simpa [phi] using this
  linarith

/-- On a nonempty open set the value map `W^{1,p}_0(Ω) → Lᵖ(Ω)` is nonzero: it does not kill the
test function of `TauCeti.W1p0.exists_value_ne_zero`. -/
theorem W1p0.valueL_ne_zero (hOmega : (Omega : Set E).Nonempty) :
    (W1p0.valueL (mu := mu) (Omega := Omega) (p := p)) ≠ 0 := by
  obtain ⟨w, hw⟩ := W1p0.exists_value_ne_zero (mu := mu) (Omega := Omega) (p := p) hOmega
  exact fun hzero => hw (by rw [← W1p0.valueL_apply, hzero, zero_apply])

/-- `W^{1,p}_0(Ω)` is complete: it is a closed subspace of the complete space `W^{1,p}(Ω)`. -/
instance : CompleteSpace (W1p0 mu Omega p) :=
  (w1p0Submodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
