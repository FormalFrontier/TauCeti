/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# The Sobolev spaces `W^{k,p}_0(Ω)`

This file constructs `TauCeti.Wkp0 μ Ω p k`, the closure of the smooth compactly supported
functions in the arbitrary-order weak Sobolev space `TauCeti.Wkp μ Ω p k`.  It extends the
first-order construction `TauCeti.W1p0`; the equality
`TauCeti.wkp0Submodule_one` verifies that the two closed subspaces agree at order one.

A test function enters `W^{k,p}` together with all of its classical derivatives through order
`k`.  The derivative fields are defined recursively: order one is Mathlib's gradient, identified
with the derivative by the real inner product, and every further order is a Fréchet derivative.
Each field is smooth and compactly supported, hence belongs to every `Lᵖ` space, and a classical
derivative is a weak derivative by `TauCeti.hasWeakFDerivOn_of_differentiableOn`.  This produces
the injective linear map `TauCeti.Wkp.ofTestFunctionₗ`, whose range is then closed to define
`TauCeti.wkp0Submodule`.

No boundedness or boundary regularity of `Ω` is required.  Meyers--Serrin density of smooth
Sobolev functions and density results comparing different domains are not proved here.

## Main declarations

* `TauCeti.testFunctionIteratedGradient`: the recursively bundled classical derivatives of a
  test function.
* `TauCeti.Wkp.ofTestFunctionₗ`: the injective linear embedding `C_c^∞(Ω) → W^{k,p}(Ω)`.
* `TauCeti.wkp0Submodule` and `TauCeti.Wkp0`: the closure of the test functions in `W^{k,p}(Ω)`
  and its complete normed-space type.
* `TauCeti.wkp0Submodule_subset_of_isClosed`: the closure induction principle used to extend a
  closed property from test functions to `W^{k,p}_0(Ω)`.

## References

This is the arbitrary-order `C_c^∞(Ω)`-closure part of Lane A.2 in
`TauCetiRoadmap/PDE/README.md`.  The construction follows L. C. Evans, *Partial Differential
Equations*, Section 5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace

universe u

variable {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### Test functions and their iterated gradients -/

/-- The classical derivative fields of a test function, in the basis-free nested-linear-map
types used by `TauCeti.Wkp`.  Order zero is the gradient and each successor is the Fréchet
derivative of the preceding field. -/
noncomputable def testFunctionIteratedGradient (phi : 𝓓(Omega, ℝ)) :
    (k : ℕ) → E → IteratedGradient E k
  | 0 => fun x => gradient (phi : E → ℝ) x
  | k + 1 => fderiv ℝ (testFunctionIteratedGradient phi k)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every iterated gradient of a test function is smooth. -/
theorem contDiff_testFunctionIteratedGradient (phi : 𝓓(Omega, ℝ)) :
    ∀ k, ContDiff ℝ ∞ (testFunctionIteratedGradient phi k)
  | 0 => by
      dsimp [testFunctionIteratedGradient]
      exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp
        (contDiff_infty_iff_fderiv.mp phi.contDiff).2
  | k + 1 => by
      rw [testFunctionIteratedGradient]
      exact (contDiff_infty_iff_fderiv.mp (contDiff_testFunctionIteratedGradient phi k)).2

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every iterated gradient of a test function has compact support. -/
theorem hasCompactSupport_testFunctionIteratedGradient (phi : 𝓓(Omega, ℝ)) :
    ∀ k, HasCompactSupport (testFunctionIteratedGradient phi k)
  | 0 => by
      simpa only [testFunctionIteratedGradient] using hasCompactSupport_gradient_testFunction phi
  | k + 1 => by
      rw [testFunctionIteratedGradient]
      exact (hasCompactSupport_testFunctionIteratedGradient phi k).fderiv ℝ

omit [Fact (1 ≤ p)] in
/-- Every iterated gradient of a test function belongs to `Lᵖ(Ω)` for every exponent. -/
theorem memLp_testFunctionIteratedGradient (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    MemLp (testFunctionIteratedGradient phi k) p (mu.restrict Omega) :=
  (contDiff_testFunctionIteratedGradient phi k).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_testFunctionIteratedGradient phi k)

/-- The `k`th iterated gradient of a test function, as an `Lᵖ(Ω)` class. -/
noncomputable def iteratedGradientTestFunctionLp (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Lp (IteratedGradient E k) p (mu.restrict Omega) :=
  (memLp_testFunctionIteratedGradient (mu := mu) (p := p) phi k).toLp _

omit [Fact (1 ≤ p)] in
@[simp]
theorem iteratedGradientTestFunctionLp_apply_ae (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega,
      iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi x =
        testFunctionIteratedGradient phi k x :=
  (memLp_testFunctionIteratedGradient (mu := mu) (p := p) phi k).coeFn_toLp

omit [Fact (1 ≤ p)] in
/-- Consecutive iterated-gradient fields of a test function satisfy the weak derivative
identity. -/
theorem hasWeakFDerivOn_iteratedGradientTestFunctionLp (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi)
      (iteratedGradientTestFunctionLp (mu := mu) (p := p) (k + 1) phi) := by
  have hsmooth := contDiff_testFunctionIteratedGradient phi k
  have hclassical : HasWeakFDerivOn mu Omega (testFunctionIteratedGradient phi k)
      (fderiv ℝ (testFunctionIteratedGradient phi k)) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hsmooth.continuous.locallyIntegrable (μ := mu)).locallyIntegrableOn (Omega : Set E))
      (((contDiff_infty_iff_fderiv.mp hsmooth).2.continuous.locallyIntegrable
        (μ := mu)).locallyIntegrableOn (Omega : Set E))
      fun x _ => (hsmooth.differentiable (by simp)) x
  refine (hclassical.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) (p := p) k phi]
      with x hx using hx.symm
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) (p := p) (k + 1) phi]
      with x hx
    simpa only [testFunctionIteratedGradient] using hx.symm

/-! ### Test functions inside arbitrary-order Sobolev spaces -/

private structure TestFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) (k : ℕ) where
  element : Wkp mu Omega p (k + 1)
  value_eq : Wkp.value (k + 1) element = testFunctionLp p phi
  iteratedGradient_eq : Wkp.iteratedGradient k element =
    iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi

private noncomputable def testFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) :
    (k : ℕ) → TestFunctionWkpPackage (mu := mu) (p := p) phi k
  | 0 =>
      { element := W1p.ofTestFunctionₗ mu Omega p phi
        value_eq := by
          simpa only [Wkp.value_succ, Wkp.value_zero, Wkp.lowerOrder_zero] using
            W1p.value_ofTestFunctionₗ (mu := mu) (p := p) phi
        iteratedGradient_eq := by
          rw [Wkp.iteratedGradient_zero, W1p.gradient_ofTestFunctionₗ]
          apply Lp.ext
          filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) p phi,
            iteratedGradientTestFunctionLp_apply_ae (mu := mu) (p := p) 0 phi] with x hx hy
          simpa only [testFunctionIteratedGradient] using hx.trans hy.symm }
  | k + 1 =>
      let previous := testFunctionWkpPackage phi k
      let hweak : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient k previous.element)
          (iteratedGradientTestFunctionLp (mu := mu) (p := p) (k + 1) phi) := by
        rw [previous.iteratedGradient_eq]
        exact hasWeakFDerivOn_iteratedGradientTestFunctionLp k phi
      { element := Wkp.mk k previous.element
          (iteratedGradientTestFunctionLp (mu := mu) (p := p) (k + 1) phi) hweak
        value_eq := by
          rw [Wkp.value_succ, Wkp.lowerOrder_mk]
          exact previous.value_eq
        iteratedGradient_eq := Wkp.iteratedGradient_mk k previous.element _ hweak }

private noncomputable def Wkp.ofTestFunction (k : ℕ) (phi : 𝓓(Omega, ℝ)) : Wkp mu Omega p k :=
  match k with
  | 0 => testFunctionLp p phi
  | k + 1 => (testFunctionWkpPackage (mu := mu) (p := p) phi k).element

private theorem Wkp.value_ofTestFunction (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.value k (Wkp.ofTestFunction (mu := mu) (p := p) k phi) = testFunctionLp p phi := by
  cases k with
  | zero => simp [Wkp.ofTestFunction]
  | succ k => exact (testFunctionWkpPackage (mu := mu) (p := p) phi k).value_eq

private theorem Wkp.iteratedGradient_ofTestFunction (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.iteratedGradient k (Wkp.ofTestFunction (mu := mu) (p := p) (k + 1) phi) =
      iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi :=
  (testFunctionWkpPackage (mu := mu) (p := p) phi k).iteratedGradient_eq

/-- The linear embedding of test functions into `W^{k,p}(Ω)`. -/
noncomputable def Wkp.ofTestFunctionₗ (k : ℕ) : 𝓓(Omega, ℝ) →ₗ[ℝ] Wkp mu Omega p k where
  toFun := Wkp.ofTestFunction (mu := mu) (p := p) k
  map_add' phi psi := by
    apply Wkp.ext k
    simp only [← Wkp.valueL_apply, map_add]
    simp only [Wkp.valueL_apply, Wkp.value_ofTestFunction, testFunctionLp_add]
  map_smul' c phi := by
    apply Wkp.ext k
    simp only [RingHom.id_apply, ← Wkp.valueL_apply, map_smul]
    simp only [Wkp.valueL_apply, Wkp.value_ofTestFunction, testFunctionLp_smul]

private theorem Wkp.ofTestFunctionₗ_apply (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi = Wkp.ofTestFunction k phi :=
  rfl

/-- The value component of an embedded test function is its `Lᵖ` class. -/
@[simp]
theorem Wkp.value_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.value k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi) = testFunctionLp p phi := by
  rw [Wkp.ofTestFunctionₗ_apply]
  exact Wkp.value_ofTestFunction k phi

/-- The highest iterated-gradient component of an embedded test function is its classical
iterated gradient as an `Lᵖ` class. -/
@[simp]
theorem Wkp.iteratedGradient_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.iteratedGradient k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi := by
  rw [Wkp.ofTestFunctionₗ_apply]
  exact Wkp.iteratedGradient_ofTestFunction k phi

@[simp]
theorem iteratedGradientTestFunctionLp_add (k : ℕ) (phi psi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) (p := p) k (phi + psi) =
      iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi +
        iteratedGradientTestFunctionLp (mu := mu) (p := p) k psi := by
  simp only [← Wkp.iteratedGradient_ofTestFunctionₗ,
    ← Wkp.iteratedGradientL_apply, map_add]

@[simp]
theorem iteratedGradientTestFunctionLp_smul (k : ℕ) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) (p := p) k (c • phi) =
      c • iteratedGradientTestFunctionLp (mu := mu) (p := p) k phi := by
  simp only [← Wkp.iteratedGradient_ofTestFunctionₗ,
    ← Wkp.iteratedGradientL_apply, map_smul]

/-- The test-function embedding into `W^{k,p}(Ω)` is injective. -/
theorem Wkp.ofTestFunctionₗ_injective (k : ℕ) :
    Function.Injective (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k) := by
  intro phi psi h
  apply W1p.ofTestFunctionₗ_injective (mu := mu) (Omega := Omega) (p := p)
  apply W1p.ext_value
  have hvalue := congrArg (Wkp.value k) h
  simpa only [Wkp.value_ofTestFunctionₗ,
    W1p.value_ofTestFunctionₗ] using hvalue

/-- At order one, the arbitrary-order test-function embedding is the existing embedding into
`W^{1,p}(Ω)`. -/
@[simp]
theorem Wkp.ofTestFunctionₗ_one :
    Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) 1 =
      W1p.ofTestFunctionₗ mu Omega p := by
  apply LinearMap.ext
  intro phi
  apply W1p.ext_value
  have hvalue : W1p.value (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 phi) =
      testFunctionLp p phi := by
    simpa only [Wkp.value_succ, Wkp.value_zero, Wkp.lowerOrder_zero] using
      Wkp.value_ofTestFunctionₗ (mu := mu) (p := p) 1 phi
  exact hvalue.trans (W1p.value_ofTestFunctionₗ (mu := mu) (p := p) phi).symm

/-! ### The spaces `W^{k,p}_0(Ω)` -/

/-- The closed subspace `W^{k,p}_0(Ω)` of `W^{k,p}(Ω)`: the closure of the test functions
`C_c^∞(Ω)` in the iterated graph norm. -/
noncomputable def wkp0Submodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] (k : ℕ) : ClosedSubmodule ℝ (Wkp mu Omega p k) :=
  (LinearMap.range (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k)).closure

/-- `W^{k,p}_0(Ω)` is the closure of the set of test-function jets. -/
theorem coe_wkp0Submodule (k : ℕ) :
    (wkp0Submodule mu Omega p k : Set (Wkp mu Omega p k)) =
      closure (Set.range (Wkp.ofTestFunctionₗ (mu := mu) (p := p) k)) := by
  rw [wkp0Submodule, Submodule.coe_closure, LinearMap.coe_range]

/-- A test function, viewed in `W^{k,p}(Ω)`, lies in `W^{k,p}_0(Ω)`. -/
theorem Wkp.ofTestFunctionₗ_mem_wkp0Submodule (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi ∈ wkp0Submodule mu Omega p k :=
  Submodule.mem_closure_iff.2 (Submodule.le_topologicalClosure _ ⟨phi, rfl⟩)

/-- A closed set containing every test-function jet contains all of `W^{k,p}_0(Ω)`. -/
theorem wkp0Submodule_subset_of_isClosed (k : ℕ) {s : Set (Wkp mu Omega p k)}
    (hs : IsClosed s) (h : ∀ phi, Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi ∈ s) :
    (wkp0Submodule mu Omega p k : Set (Wkp mu Omega p k)) ⊆ s := by
  rw [coe_wkp0Submodule]
  exact closure_minimal (by rintro _ ⟨phi, rfl⟩; exact h phi) hs

/-- At order one, the arbitrary-order zero-boundary subspace is the existing
`TauCeti.w1p0Submodule`. -/
@[simp]
theorem wkp0Submodule_one : wkp0Submodule mu Omega p 1 = w1p0Submodule mu Omega p := by
  apply SetLike.coe_injective
  rw [coe_wkp0Submodule, coe_w1p0Submodule, Wkp.ofTestFunctionₗ_one]

/-- The Sobolev space `W^{k,p}_0(Ω)`, the closure of `C_c^∞(Ω)` in `W^{k,p}(Ω)`. -/
noncomputable abbrev Wkp0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] (k : ℕ) := (wkp0Submodule mu Omega p k).toSubmodule

/-- `W^{k,p}_0(Ω)` is complete in the iterated graph norm. -/
instance (k : ℕ) : CompleteSpace (Wkp0 mu Omega p k) :=
  (wkp0Submodule mu Omega p k).isClosed.completeSpace_coe

end TauCeti
