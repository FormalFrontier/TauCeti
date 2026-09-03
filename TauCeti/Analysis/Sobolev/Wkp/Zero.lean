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
`k`. The derivative field of index `j` is the `(j+1)`-st classical derivative, valued in
`TauCeti.IteratedGradient E j`; index zero is Mathlib's gradient, identified with the derivative
by the real inner product, and every successor is a Fréchet derivative. Each field is smooth and
compactly supported, hence belongs to every `Lᵖ` space, and a classical derivative is a weak
derivative by `TauCeti.hasWeakFDerivOn_of_differentiableOn`. This produces the injective linear
map `TauCeti.Wkp.ofTestFunctionₗ`, whose range is then closed to define `TauCeti.wkp0Submodule`.

No boundedness or boundary regularity of `Ω` is required.  Meyers--Serrin density of smooth
Sobolev functions and density results comparing different domains are not proved here.

## Main declarations

* `TauCeti.iteratedGradientTestFunction`: the recursively bundled classical derivatives of a
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

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Omega : Opens E}

/-! ### Test functions and their iterated gradients -/

section TestFunctionIteratedGradient

variable [CompleteSpace E]

/-- The classical derivative fields of a test function, indexed so that index zero is its
gradient and each successor is the Fréchet derivative of the preceding field. -/
noncomputable def iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    E → IteratedGradient E k :=
  iteratedGradientChain (phi : E → ℝ) k

@[simp]
theorem iteratedGradientTestFunction_zero (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction phi 0 = fun x => gradient (phi : E → ℝ) x :=
  by rw [iteratedGradientTestFunction, iteratedGradientChain_zero]

@[simp]
theorem iteratedGradientTestFunction_succ (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    iteratedGradientTestFunction phi (k + 1) =
      fderiv ℝ (iteratedGradientTestFunction phi k) :=
  by simp only [iteratedGradientTestFunction, iteratedGradientChain_succ]

/-- Every iterated gradient of a test function is smooth. -/
theorem contDiff_iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedGradientTestFunction phi k) :=
  contDiff_iteratedGradientChain phi.contDiff k

/-- Every iterated gradient of a test function has compact support. -/
theorem hasCompactSupport_iteratedGradientTestFunction (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    HasCompactSupport (iteratedGradientTestFunction phi k) :=
  hasCompactSupport_iteratedGradientChain phi.hasCompactSupport k

variable [MeasurableSpace E] [OpensMeasurableSpace E] {mu : Measure E}
  [IsFiniteMeasureOnCompacts mu]

/-- Every iterated gradient of a test function belongs to `Lᵖ(Ω)` for every exponent. -/
theorem memLp_iteratedGradientTestFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) (k : ℕ) :
    MemLp (iteratedGradientTestFunction phi k) q (mu.restrict Omega) :=
  (contDiff_iteratedGradientTestFunction phi k).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_iteratedGradientTestFunction phi k)

/-- The index-`k` derivative field of `phi`, i.e. its `(k+1)`-st classical derivative valued in
`IteratedGradient E k`, as an `Lᵖ(Ω)` class. -/
noncomputable def iteratedGradientTestFunctionLp (q : ENNReal) (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) : Lp (IteratedGradient E k) q (mu.restrict Omega) :=
  (memLp_iteratedGradientTestFunction (mu := mu) q phi k).toLp _

@[simp]
theorem iteratedGradientTestFunctionLp_apply_ae (q : ENNReal) (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega,
      iteratedGradientTestFunctionLp (mu := mu) q k phi x =
        iteratedGradientTestFunction phi k x :=
  (memLp_iteratedGradientTestFunction (mu := mu) q phi k).coeFn_toLp

/-- At index zero, the iterated-gradient `Lᵖ` class is the existing gradient class. -/
@[simp]
theorem iteratedGradientTestFunctionLp_zero (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q 0 phi = gradientTestFunctionLp q phi :=
  by
    apply Lp.ext
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q phi,
      iteratedGradientTestFunctionLp_apply_ae (mu := mu) q 0 phi] with x hx hy
    exact hy.trans ((congrFun (iteratedGradientTestFunction_zero phi) x).trans hx.symm)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedGradientTestFunction_add (k : ℕ) (phi psi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction (phi + psi) k =
      iteratedGradientTestFunction phi k + iteratedGradientTestFunction psi k := by
  induction k with
  | zero =>
      funext x
      simp only [Pi.add_apply]
      rw [congrFun (iteratedGradientTestFunction_zero (phi + psi)) x,
        congrFun (iteratedGradientTestFunction_zero phi) x,
        congrFun (iteratedGradientTestFunction_zero psi) x]
      simpa using gradient_add ((phi.contDiff.differentiable (by simp)) x)
        ((psi.contDiff.differentiable (by simp)) x)
  | succ k ih =>
      rw [iteratedGradientTestFunction_succ, iteratedGradientTestFunction_succ,
        iteratedGradientTestFunction_succ, ih]
      funext x
      exact fderiv_add
        ((contDiff_iteratedGradientTestFunction phi k).differentiable (by simp) x)
        ((contDiff_iteratedGradientTestFunction psi k).differentiable (by simp) x)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
private theorem iteratedGradientTestFunction_smul (k : ℕ) (c : ℝ)
    (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunction (c • phi) k =
      c • iteratedGradientTestFunction phi k := by
  induction k with
  | zero =>
      funext x
      simp only [Pi.smul_apply]
      rw [congrFun (iteratedGradientTestFunction_zero (c • phi)) x,
        congrFun (iteratedGradientTestFunction_zero phi) x]
      simpa using gradient_const_smul (f := (phi : E → ℝ)) (x := x) c
  | succ k ih =>
      rw [iteratedGradientTestFunction_succ, iteratedGradientTestFunction_succ, ih]
      funext x
      exact fderiv_const_smul
        ((contDiff_iteratedGradientTestFunction phi k).differentiable (by simp) x) c

@[simp]
theorem iteratedGradientTestFunctionLp_add (q : ENNReal) (k : ℕ)
    (phi psi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q k (phi + psi) =
      iteratedGradientTestFunctionLp (mu := mu) q k phi +
        iteratedGradientTestFunctionLp (mu := mu) q k psi := by
  rw [iteratedGradientTestFunctionLp, iteratedGradientTestFunctionLp,
    iteratedGradientTestFunctionLp, ← MemLp.toLp_add]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (iteratedGradientTestFunction_add k phi psi) x

@[simp]
theorem iteratedGradientTestFunctionLp_smul (q : ENNReal) (k : ℕ) (c : ℝ)
    (phi : 𝓓(Omega, ℝ)) :
    iteratedGradientTestFunctionLp (mu := mu) q k (c • phi) =
      c • iteratedGradientTestFunctionLp (mu := mu) q k phi := by
  rw [iteratedGradientTestFunctionLp, iteratedGradientTestFunctionLp,
    ← MemLp.toLp_const_smul]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => congrFun (iteratedGradientTestFunction_smul k c phi) x

end TestFunctionIteratedGradient

section WkpZero

variable [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E]
  {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Consecutive iterated-gradient fields of a test function satisfy the weak derivative
identity. -/
theorem hasWeakFDerivOn_iteratedGradientTestFunctionLp (k : ℕ)
    (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (iteratedGradientTestFunctionLp (mu := mu) p k phi)
      (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) := by
  have hsmooth := contDiff_iteratedGradientTestFunction phi k
  have hclassical : HasWeakFDerivOn mu Omega (iteratedGradientTestFunction phi k)
      (fderiv ℝ (iteratedGradientTestFunction phi k)) :=
    hasWeakFDerivOn_of_differentiableOn
      ((hsmooth.continuous.locallyIntegrable (μ := mu)).locallyIntegrableOn (Omega : Set E))
      (((contDiff_infty_iff_fderiv.mp hsmooth).2.continuous.locallyIntegrable
        (μ := mu)).locallyIntegrableOn (Omega : Set E))
      fun x _ => (hsmooth.differentiable (by simp)) x
  refine (hclassical.congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p k phi]
      with x hx using hx.symm
  · filter_upwards [iteratedGradientTestFunctionLp_apply_ae (mu := mu) p (k + 1) phi]
      with x hx
    simpa only [iteratedGradientTestFunction_succ] using hx.symm

/-! ### Test functions inside arbitrary-order Sobolev spaces -/

private structure TestFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) (k : ℕ) where
  element : Wkp mu Omega p (k + 1)
  value_eq : Wkp.value (k + 1) element = testFunctionLp p phi
  iteratedGradient_eq : Wkp.iteratedGradient k element =
    iteratedGradientTestFunctionLp (mu := mu) p k phi

private noncomputable def testFunctionWkpPackage (phi : 𝓓(Omega, ℝ)) :
    (k : ℕ) → TestFunctionWkpPackage (mu := mu) (p := p) phi k
  | 0 =>
      -- `Wkp mu Omega p 1` reduces to `W1p mu Omega p` through the reducible stage definitions.
      { element := W1p.ofTestFunctionₗ mu Omega p phi
        value_eq := by
          exact (Wkp.value_one (W1p.ofTestFunctionₗ mu Omega p phi)).trans
            (W1p.value_ofTestFunctionₗ (mu := mu) (p := p) phi)
        iteratedGradient_eq := by
          simp only [Wkp.iteratedGradient_zero, W1p.gradient_ofTestFunctionₗ,
            iteratedGradientTestFunctionLp_zero] }
  | k + 1 =>
      let previous := testFunctionWkpPackage phi k
      let hweak : HasWeakFDerivOn mu Omega (Wkp.iteratedGradient k previous.element)
          (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) := by
        rw [previous.iteratedGradient_eq]
        exact hasWeakFDerivOn_iteratedGradientTestFunctionLp k phi
      { element := Wkp.mk k previous.element
          (iteratedGradientTestFunctionLp (mu := mu) p (k + 1) phi) hweak
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
theorem Wkp.iteratedGradient_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.iteratedGradient k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      iteratedGradientTestFunctionLp (mu := mu) p k phi :=
  (testFunctionWkpPackage (mu := mu) (p := p) phi k).iteratedGradient_eq

/-- Forgetting the highest derivative of an embedded test function gives its embedding at the
preceding order. This is intentionally not a simp lemma: the dependent index prevents the rule
from matching during simplification, which `simpNF` reports as a rule that will never apply. -/
theorem Wkp.lowerOrder_ofTestFunctionₗ (k : ℕ) (phi : 𝓓(Omega, ℝ)) :
    Wkp.lowerOrder k (Wkp.ofTestFunctionₗ (mu := mu) (p := p) (k + 1) phi) =
      Wkp.ofTestFunctionₗ (mu := mu) (p := p) k phi := by
  apply Wkp.ext k
  rw [← Wkp.value_succ, Wkp.value_ofTestFunctionₗ, Wkp.value_ofTestFunctionₗ]

/-- The test-function embedding into `W^{k,p}(Ω)` is injective. -/
theorem Wkp.ofTestFunctionₗ_injective (k : ℕ) :
    Function.Injective (Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) k) := by
  intro phi psi h
  apply testFunctionLp_injective (nu := mu) (U := Omega) p
  simpa only [Wkp.value_ofTestFunctionₗ] using congrArg (Wkp.value k) h

/-- At order one, the arbitrary-order test-function embedding is the existing embedding into
`W^{1,p}(Ω)`. -/
@[simp]
theorem Wkp.ofTestFunctionₗ_one :
    Wkp.ofTestFunctionₗ (mu := mu) (Omega := Omega) (p := p) 1 =
      W1p.ofTestFunctionₗ mu Omega p := by
  -- The order-one codomain reduces to `W1p`, as in the package base case above.
  apply LinearMap.ext
  intro phi
  apply W1p.ext_value
  have hvalue : W1p.value (Wkp.ofTestFunctionₗ (mu := mu) (p := p) 1 phi) =
      testFunctionLp p phi := by
    simpa only [Wkp.value_one] using
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
  -- Both closed submodules have the definitionally equal order-one ambient space noted above.
  apply SetLike.coe_injective
  rw [coe_wkp0Submodule, coe_w1p0Submodule, Wkp.ofTestFunctionₗ_one]

/-- The Sobolev space `W^{k,p}_0(Ω)`, the closure of `C_c^∞(Ω)` in `W^{k,p}(Ω)`. -/
noncomputable abbrev Wkp0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E)
    (p : ENNReal) [Fact (1 ≤ p)] (k : ℕ) := (wkp0Submodule mu Omega p k).toSubmodule

/-- `W^{k,p}_0(Ω)` is complete in the iterated graph norm. -/
instance (k : ℕ) : CompleteSpace (Wkp0 mu Omega p k) :=
  (wkp0Submodule mu Omega p k).isClosed.completeSpace_coe

end WkpZero

end TauCeti
