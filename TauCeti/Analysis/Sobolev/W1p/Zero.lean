/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Basic

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
    apply W1p.ext
    · rw [W1p.value_mk, testFunctionLp_add, ← W1p.valueL_apply, map_add]
      simp
    · rw [W1p.gradient_mk, gradientTestFunctionLp_add, ← W1p.gradientL_apply, map_add]
      simp
  map_smul' c phi := by
    apply W1p.ext
    · rw [W1p.value_mk, testFunctionLp_smul, ← W1p.valueL_apply, map_smul]
      simp
    · rw [W1p.gradient_mk, gradientTestFunctionLp_smul, ← W1p.gradientL_apply, map_smul]
      simp

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
  have hLp : testFunctionLp (mu := mu) p phi = testFunctionLp (mu := mu) p psi := by
    simpa using congrArg W1p.value h
  have hae : (phi : E → ℝ) =ᵐ[mu.restrict Omega] (psi : E → ℝ) := by
    filter_upwards [testFunctionLp_apply_ae (mu := mu) p phi,
      testFunctionLp_apply_ae (mu := mu) p psi] with x hx hy
    rw [← hx, ← hy, hLp]
  have hsubset : {x | (phi : E → ℝ) x ≠ psi x} ⊆ (Omega : Set E) := by
    intro x hx
    by_contra hxO
    exact hx (by rw [image_eq_zero_of_notMem_tsupport fun hc => hxO (phi.tsupport_subset hc),
      image_eq_zero_of_notMem_tsupport fun hc => hxO (psi.tsupport_subset hc)])
  have hzero : mu {x | (phi : E → ℝ) x ≠ psi x} = 0 := by
    have := ae_iff.1 hae
    rwa [Measure.restrict_apply' Omega.isOpen.measurableSet,
      Set.inter_eq_self_of_subset_left hsubset] at this
  have hempty := (isOpen_ne_fun phi.continuous psi.continuous).measure_eq_zero_iff mu |>.1 hzero
  exact TestFunction.ext fun x => not_not.1 fun hx => Set.eq_empty_iff_forall_notMem.1 hempty x hx

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

/-- `W^{1,p}_0(Ω)` is complete: it is a closed subspace of the complete space `W^{1,p}(Ω)`. -/
instance : CompleteSpace (W1p0 mu Omega p) :=
  (w1p0Submodule mu Omega p).isClosed.completeSpace_coe

end TauCeti
