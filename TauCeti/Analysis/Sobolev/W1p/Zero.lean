/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Sobolev.W1p.Basic
-- The slab inequality is consumed inside the Poincaré proofs below; its module is imported
-- publicly because it also carries the Lebesgue measure of `EuclideanSpace ℝ (Fin (n + 1))`,
-- which the Poincaré statements mention.
public import TauCeti.Analysis.Sobolev.Poincare.Slab
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Sobolev space `W^{1,p}_0(Ω)` and its Poincaré inequality

This file builds `W^{1,p}_0(Ω)`, the closure of the test functions `C_c^∞(Ω)` inside the weak
Sobolev space `W^{1,p}(Ω)` of `TauCeti/Analysis/Sobolev/W1p/Basic.lean`, and proves the
**Poincaré inequality** on it: for a domain `Ω ⊆ ℝ^{n+1}` trapped between two parallel
hyperplanes at distance `b - a`,

`‖u‖_p ≤ (b - a) ‖∇u‖_p` for every `u ∈ W^{1,p}_0(Ω)`.

This is Lane A, items 2 and 5, of `TauCetiRoadmap/PDE/README.md`.

## Test functions as Sobolev functions

The embedding `C_c^∞(Ω) → W^{1,p}(Ω)` sends `φ` to the value-gradient jet `(φ, ∇φ)`, where `∇`
is Mathlib's `gradient`, the Riesz representative of the Fréchet derivative. Two things have to be
checked, and both are easy for a test function: the jet is `Lᵖ`, because `φ` and `∇φ` are
continuous with compact support; and the weak-derivative identity holds, because `∇φ` represents
the *classical* derivative, which is a weak derivative by
`TauCeti.hasWeakFDerivOn_of_differentiableOn`. The embedding is linear
(`TauCeti.W1p.ofTestFunctionLM`), which is what makes its range a subspace — and that is essential
below, since the Poincaré inequality is preserved by limits but *not* by sums.

## Why the closure, and why not all of `W^{1,p}(Ω)`

`W^{1,p}_0(Ω)` is defined as `TauCeti.w1p0Submodule`, the topological closure of that range. It is
the Sobolev-space stand-in for the homogeneous Dirichlet boundary condition `u|_{∂Ω} = 0`: no
boundary regularity of `Ω` is assumed, and no trace operator is needed to state it. The
distinction from `W^{1,p}(Ω)` is real and is exactly what the Poincaré inequality sees — the
constant function `1` on a bounded `Ω` lies in `W^{1,p}(Ω)` and has vanishing gradient, so it
cannot satisfy any inequality `‖u‖_p ≤ C ‖∇u‖_p`.

## The Poincaré inequality

The estimate for a *single* test function is Mathlib-free classical calculus and is already
available as `TauCeti.eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab`. What this file adds is
the passage to the closure. The two steps are:

* the set `{u | ‖u‖_p ≤ C ‖∇u‖_p}` is **closed**, because both components of a Sobolev function
  depend continuously on it; and
* it **contains the range** of the test-function embedding, by the slab inequality together with
  `‖∇φ‖ = ‖Dφ‖` (`TauCeti.norm_gradient`) and the fact that restricting the measure to `Ω`
  does not change the `Lᵖ` norm of a function supported in `Ω`.

Since the range is a *subspace*, its closure is `W^{1,p}_0(Ω)` and `closure_minimal` finishes.
The set above is closed but is *not* a subspace — `‖u + v‖_p ≤ C‖∇u‖_p + C‖∇v‖_p` says nothing
about `‖∇(u + v)‖_p` — which is why linearity of the embedding is load-bearing rather than
cosmetic: the estimate must already hold on the whole span of the test functions, and that span
is the range only because the embedding is linear.

The hypothesis is that `Ω` lies in a slab, i.e. is bounded *in one direction*; boundedness of `Ω`
is not needed, and some such hypothesis is: no inequality of this shape holds on the whole space,
by `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`.

## Main declarations

* `TauCeti.gradientTestFunctionLp`: the gradient of a test function as an `Lᵖ` class, with its
  additivity and homogeneity.
* `TauCeti.hasWeakFDerivOn_testFunction`: a test function is weakly differentiable, with weak
  derivative its gradient.
* `TauCeti.W1p.ofTestFunctionLM`: the linear embedding `C_c^∞(Ω) → W^{1,p}(Ω)`.
* `TauCeti.w1p0Submodule` and `TauCeti.W1p0`: the space `W^{1,p}_0(Ω)`, complete for the graph
  norm.
* `TauCeti.norm_value_le_of_mem_w1p0Submodule_of_subset_slab` and
  `TauCeti.norm_value_le_of_mem_w1p0Submodule_of_subset_ball`: the Poincaré inequality.

## References

Lane A.2 and A.5 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential
Equations*, Sections 5.2 and 5.6.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Omega : Opens E}

/-! ### The gradient of a test function -/

omit [CompleteSpace E] in
/-- A test function is differentiable. -/
theorem differentiableAt_testFunction (phi : 𝓓(Omega, ℝ)) (x : E) :
    DifferentiableAt ℝ (phi : E → ℝ) x :=
  (phi.contDiff.differentiable (by simp)).differentiableAt

/-- The gradient of a test function is continuous. -/
theorem continuous_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    Continuous fun x => ∇ (phi : E → ℝ) x :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (phi.contDiff.continuous_fderiv (by simp))

/-- The gradient of a test function has compact support. -/
theorem hasCompactSupport_gradient_testFunction (phi : 𝓓(Omega, ℝ)) :
    HasCompactSupport fun x => ∇ (phi : E → ℝ) x :=
  (phi.hasCompactSupport.fderiv ℝ).comp_left (map_zero _)

/-- The gradient of a test function on `Ω` vanishes outside `Ω`. -/
theorem support_gradient_testFunction_subset (phi : 𝓓(Omega, ℝ)) :
    Function.support (fun x => ∇ (phi : E → ℝ) x) ⊆ (Omega : Set E) :=
  (Function.support_comp_subset (map_zero (InnerProductSpace.toDual ℝ E).symm) _).trans <|
    (subset_tsupport _).trans <| (tsupport_fderiv_subset ℝ).trans phi.tsupport_subset

end Calculus

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### The gradient of a test function in `Lᵖ` -/

/-- The gradient of a test function on `Ω` is continuous with compact support, so it lies in every
`Lᵠ(Ω)`. -/
theorem memLp_gradient_testFunction (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    MemLp (fun x => ∇ (phi : E → ℝ) x) q (mu.restrict Omega) :=
  (continuous_gradient_testFunction phi).memLp_of_hasCompactSupport
    (hasCompactSupport_gradient_testFunction phi)

/-- The gradient of a test function on `Ω`, as an element of `Lᵠ(Ω, E)`. -/
def gradientTestFunctionLp (q : ENNReal) (phi : 𝓓(Omega, ℝ)) : Lp E q (mu.restrict Omega) :=
  (memLp_gradient_testFunction (mu := mu) q phi).toLp _

@[simp]
theorem gradientTestFunctionLp_apply_ae (q : ENNReal) (phi : 𝓓(Omega, ℝ)) :
    ∀ᵐ x ∂mu.restrict Omega, gradientTestFunctionLp (mu := mu) q phi x = ∇ (phi : E → ℝ) x :=
  (memLp_gradient_testFunction (mu := mu) q phi).coeFn_toLp

@[simp]
theorem gradientTestFunctionLp_add (q : ENNReal) (phi psi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (phi + psi) =
      gradientTestFunctionLp (mu := mu) q phi + gradientTestFunctionLp (mu := mu) q psi := by
  apply Lp.ext
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q (phi + psi),
    gradientTestFunctionLp_apply_ae (mu := mu) q phi,
    gradientTestFunctionLp_apply_ae (mu := mu) q psi,
    Lp.coeFn_add (gradientTestFunctionLp (mu := mu) q phi)
      (gradientTestFunctionLp (mu := mu) q psi)] with x hsum hphi hpsi hadd
  rw [hsum, hadd, Pi.add_apply, hphi, hpsi,
    show ((phi + psi : 𝓓(Omega, ℝ)) : E → ℝ) = (phi : E → ℝ) + (psi : E → ℝ) from rfl,
    gradient_add (differentiableAt_testFunction phi x) (differentiableAt_testFunction psi x)]

@[simp]
theorem gradientTestFunctionLp_smul (q : ENNReal) (c : ℝ) (phi : 𝓓(Omega, ℝ)) :
    gradientTestFunctionLp (mu := mu) q (c • phi) =
      c • gradientTestFunctionLp (mu := mu) q phi := by
  apply Lp.ext
  filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) q (c • phi),
    gradientTestFunctionLp_apply_ae (mu := mu) q phi,
    Lp.coeFn_smul c (gradientTestFunctionLp (mu := mu) q phi)] with x hsmul hphi hc
  rw [hsmul, hc, Pi.smul_apply, hphi,
    show ((c • phi : 𝓓(Omega, ℝ)) : E → ℝ) = c • (phi : E → ℝ) from rfl,
    gradient_const_smul (differentiableAt_testFunction phi x) c]
  simp

/-! ### Test functions as Sobolev functions -/

/-- **A test function is weakly differentiable**, with weak derivative the continuous linear
functional represented by its gradient. This is the classical derivative, which is a weak one
because the test function is smooth and everything in sight is locally integrable. -/
theorem hasWeakFDerivOn_testFunction (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (phi : E → ℝ) fun x => innerSL ℝ (∇ (phi : E → ℝ) x) := by
  have hcoe : (fun x => innerSL ℝ (∇ (phi : E → ℝ) x)) = fderiv ℝ (phi : E → ℝ) := by
    funext x
    ext y
    simp [inner_gradient_left (𝕜 := ℝ) (f := (phi : E → ℝ)) (x := x) (y := y)]
  rw [hcoe]
  refine hasWeakFDerivOn_of_differentiableOn ?_ ?_ fun x _ => differentiableAt_testFunction phi x
  · exact phi.continuous.locallyIntegrable.locallyIntegrableOn _
  · exact (phi.contDiff.continuous_fderiv (by simp)).locallyIntegrable.locallyIntegrableOn _

omit [Fact (1 ≤ p)] in
private theorem hasWeakFDerivOn_testFunctionLp (phi : 𝓓(Omega, ℝ)) :
    HasWeakFDerivOn mu Omega (testFunctionLp (mu := mu) p phi)
      fun x => innerSL ℝ (gradientTestFunctionLp (mu := mu) p phi x) := by
  refine ((hasWeakFDerivOn_testFunction (mu := mu) phi).congr_ae ?_).congr_ae_deriv ?_
  · filter_upwards [testFunctionLp_apply_ae (mu := mu) p phi] with x hx using hx.symm
  · filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) p phi] with x hx
    rw [hx]

/-- **The test functions inside `W^{1,p}(Ω)`**: the linear embedding sending `φ ∈ C_c^∞(Ω)` to the
value-gradient jet `(φ, ∇φ)`. Linearity is what makes the range a subspace, hence its closure
`TauCeti.w1p0Submodule` a subspace too. -/
def W1p.ofTestFunctionLM (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : 𝓓(Omega, ℝ) →ₗ[ℝ] W1p mu Omega p where
  toFun phi := W1p.mk (testFunctionLp p phi) (gradientTestFunctionLp p phi)
    (hasWeakFDerivOn_testFunctionLp phi)
  map_add' phi psi := by
    refine W1p.ext ?_ ?_ <;> simp [W1p.value_add, W1p.gradient_add]
  map_smul' c phi := by
    refine W1p.ext ?_ ?_ <;> simp [W1p.value_smul, W1p.gradient_smul]

@[simp]
theorem W1p.value_ofTestFunctionLM (phi : 𝓓(Omega, ℝ)) :
    W1p.value (W1p.ofTestFunctionLM mu Omega p phi) = testFunctionLp p phi :=
  W1p.value_mk _ _ _

@[simp]
theorem W1p.gradient_ofTestFunctionLM (phi : 𝓓(Omega, ℝ)) :
    W1p.gradient (W1p.ofTestFunctionLM mu Omega p phi) = gradientTestFunctionLp p phi :=
  W1p.gradient_mk _ _ _

/-! ### The space `W^{1,p}_0(Ω)` -/

/-- **The closed subspace `W^{1,p}_0(Ω)` of `W^{1,p}(Ω)`**: the closure of the test functions
`C_c^∞(Ω)`, the Sobolev formulation of the homogeneous Dirichlet boundary condition. No
regularity, and no boundedness, of `Ω` is assumed. -/
def w1p0Submodule (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] : ClosedSubmodule ℝ (W1p mu Omega p) :=
  (LinearMap.range (W1p.ofTestFunctionLM mu Omega p)).closure

/-- `W^{1,p}_0(Ω)` is the closure of the set of test-function jets. -/
theorem coe_w1p0Submodule :
    (w1p0Submodule mu Omega p : Set (W1p mu Omega p)) =
      closure (Set.range (W1p.ofTestFunctionLM mu Omega p)) := by
  rw [w1p0Submodule, Submodule.coe_closure, LinearMap.coe_range]

/-- A test function, viewed in `W^{1,p}(Ω)`, lies in `W^{1,p}_0(Ω)`. -/
theorem W1p.ofTestFunctionLM_mem_w1p0Submodule (phi : 𝓓(Omega, ℝ)) :
    W1p.ofTestFunctionLM mu Omega p phi ∈ w1p0Submodule mu Omega p :=
  Submodule.mem_closure_iff.2 (Submodule.le_topologicalClosure _ ⟨phi, rfl⟩)

/-- **The Sobolev space `W^{1,p}_0(Ω)`**, the closure of `C_c^∞(Ω)` in `W^{1,p}(Ω)`. -/
abbrev W1p0 (mu : Measure E) [mu.IsAddHaarMeasure] (Omega : Opens E) (p : ENNReal)
    [Fact (1 ≤ p)] := (w1p0Submodule mu Omega p).toSubmodule

/-- `W^{1,p}_0(Ω)` is complete: it is a closed subspace of the complete space `W^{1,p}(Ω)`. -/
instance : CompleteSpace (W1p0 mu Omega p) :=
  (w1p0Submodule mu Omega p).isClosed.completeSpace_coe

/-! ### The Poincaré inequality -/

section Poincare

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {p : ENNReal} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` norm of a test function on `Ω` is computed by the ambient Lebesgue measure: the
function vanishes outside `Ω`, so restricting the measure changes nothing. -/
private theorem norm_testFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := volume) p phi‖ = (eLpNorm (phi : _ → ℝ) p volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (testFunctionLp_apply_ae (mu := volume) p phi),
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans phi.tsupport_subset)]

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` norm of the gradient of a test function on `Ω`, computed by the ambient Lebesgue
measure and expressed through the Fréchet derivative. -/
private theorem norm_gradientTestFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := volume) p phi‖ =
      (eLpNorm (fderiv ℝ (phi : _ → ℝ)) p volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (gradientTestFunctionLp_apply_ae (mu := volume) p phi),
    eLpNorm_restrict_eq_of_support_subset (support_gradient_testFunction_subset phi),
    eLpNorm_congr_norm_ae (ae_of_all _ fun x => norm_gradient (𝕜 := ℝ) (phi : _ → ℝ) x)]

/-- **The Poincaré inequality for a single test function** whose domain lies in a slab: the shape
in which `TauCeti.eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab` is consumed below. -/
private theorem norm_testFunctionLp_le_of_subset_slab (hp : p ≠ ∞) {i : Fin (n + 1)} {a b : ℝ}
    (hab : a ≤ b)
    (hOmega : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc a b)
    (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := volume) p phi‖ ≤
      (b - a) * ‖gradientTestFunctionLp (mu := volume) p phi‖ := by
  have hfinite : eLpNorm (fderiv ℝ (phi : _ → ℝ)) p volume ≠ ∞ :=
    ((phi.contDiff.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      (phi.hasCompactSupport.fderiv ℝ)).2.ne
  have hslab := eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab (i := i)
    (phi.contDiff.of_le (by simp)) hab
    (fun x hx => hOmega x (phi.tsupport_subset (subset_tsupport _ hx))) Fact.out hp
  rw [norm_testFunctionLp_eq, norm_gradientTestFunctionLp_eq,
    ← ENNReal.toReal_ofReal (sub_nonneg.2 hab), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness) hslab

/-- **The Poincaré inequality on `W^{1,p}_0(Ω)`.** If the domain `Ω ⊆ ℝ^{n+1}` is trapped between
the hyperplanes `xᵢ = a` and `xᵢ = b`, then every `u ∈ W^{1,p}_0(Ω)` satisfies
`‖u‖_p ≤ (b - a) ‖∇u‖_p`.

Only the width of the slab enters, so `Ω` need not be bounded — bounded in one direction is
enough. Some such hypothesis is required: the inequality fails outright on the whole space, by
`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`. So is the boundary condition: the
constant function `1` on a bounded `Ω` lies in `W^{1,p}(Ω)` with zero gradient. -/
theorem norm_value_le_of_mem_w1p0Submodule_of_subset_slab (hp : p ≠ ∞) {i : Fin (n + 1)}
    {a b : ℝ} (hab : a ≤ b)
    (hOmega : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc a b)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ (b - a) * ‖W1p.gradient u‖ := by
  have hclosed : IsClosed {v : W1p volume Omega p |
      ‖W1p.value v‖ ≤ (b - a) * ‖W1p.gradient v‖} :=
    isClosed_le W1p.continuous_value.norm (W1p.continuous_gradient.norm.const_mul _)
  have hsub : (w1p0Submodule volume Omega p : Set (W1p volume Omega p)) ⊆
      {v : W1p volume Omega p | ‖W1p.value v‖ ≤ (b - a) * ‖W1p.gradient v‖} := by
    rw [coe_w1p0Submodule]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨phi, rfl⟩
    simpa using norm_testFunctionLp_le_of_subset_slab hp hab hOmega phi
  exact hsub hu

/-- **The Poincaré inequality on `W^{1,p}_0(Ω)` for a bounded domain**: if `Ω ⊆ ℝ^{n+1}` is
contained in the ball of radius `R` about the origin, then `‖u‖_p ≤ 2R ‖∇u‖_p` for every
`u ∈ W^{1,p}_0(Ω)`.

The constant `2R` is not sharp — for the ball itself the optimal constant is smaller — but it is
explicit and depends only on `R`, as the roadmap asks. -/
theorem norm_value_le_of_mem_w1p0Submodule_of_subset_ball (hp : p ≠ ∞) {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball 0 R)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ 2 * R * ‖W1p.gradient u‖ := by
  rcases le_or_gt R 0 with hR | hR
  · -- The domain is empty, so the restricted measure is zero and both sides vanish.
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R = ∅ :=
      Metric.ball_eq_empty.2 hR
    have hempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ∅ :=
      subset_empty_iff.1 (hball ▸ hOmega)
    have hzeroR : ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
        eLpNorm f p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) = 0 := by
      intro f
      rw [hempty, Measure.restrict_empty, eLpNorm_measure_zero]
    have hzeroE : ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        eLpNorm f p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) = 0 := by
      intro f
      rw [hempty, Measure.restrict_empty, eLpNorm_measure_zero]
    rw [Lp.norm_def, Lp.norm_def, hzeroR, hzeroE]
    simp
  have hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      x (0 : Fin (n + 1)) ∈ Icc (-R) R := by
    intro x hx
    have hnorm : ‖x‖ < R := by simpa using hOmega hx
    have := (PiLp.norm_apply_le x (0 : Fin (n + 1))).trans hnorm.le
    rwa [Real.norm_eq_abs, abs_le] at this
  have hwidth : R - -R = 2 * R := by ring
  simpa [hwidth] using
    norm_value_le_of_mem_w1p0Submodule_of_subset_slab hp (by linarith : (-R : ℝ) ≤ R) hslab hu

end Poincare

end TauCeti
