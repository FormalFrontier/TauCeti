/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Poincare.Slab
public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The Poincaré inequality on `W^{1,p}_0(Ω)`

This file proves the **Poincaré inequality** on `W^{1,p}_0(Ω)`: for `1 ≤ p < ∞` and a domain
`Ω ⊆ ℝ^{n+1}` trapped between two parallel hyperplanes at distance `b - a`,

`‖u‖_p ≤ (b - a) ‖∇u‖_p` for every `u ∈ W^{1,p}_0(Ω)`.

This is the `W^{1,p}_0` half of Lane A.5 of `TauCetiRoadmap/PDE/README.md`;
Poincaré--Wirtinger is not proved here.

The estimate for a single test function is
`TauCeti.eLpNorm_le_eLpNorm_fderiv_of_support_subset_slab`. The set
`{u | ‖u‖_p ≤ C ‖∇u‖_p}` is closed and contains every test-function jet, so
`TauCeti.mem_of_mem_w1p0Submodule` passes the estimate to their closure.

The slab hypothesis is load-bearing: no such inequality holds on the whole space, by
`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`. So is the boundary condition: the
constant function `1` on a nonempty bounded open `Ω` lies in `W^{1,p}(Ω)` with zero gradient.

## Main declarations

* `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_slab`: Poincaré on a slab-contained
  domain.
* `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_subset_ball`: the bounded-ball corollary.

## References

The `W^{1,p}_0` half of Lane A.5 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans,
*Partial Differential Equations*, Sections 5.2 and 5.6.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Gradient InnerProductSpace

variable {n : ℕ} {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {p : ENNReal} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` norm of a test function on `Ω` is computed by the ambient Lebesgue measure: the
function vanishes outside `Ω`, so restricting the measure changes nothing. -/
private theorem norm_testFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖testFunctionLp (mu := volume) p phi‖ = (eLpNorm (phi : _ → ℝ) p volume).toReal := by
  rw [norm_testFunctionLp,
    eLpNorm_restrict_eq_of_support_subset ((subset_tsupport _).trans phi.tsupport_subset)]

omit [Fact (1 ≤ p)] in
/-- The `Lᵖ` norm of the gradient of a test function on `Ω`, computed by the ambient Lebesgue
measure and expressed through the Fréchet derivative. -/
private theorem norm_gradientTestFunctionLp_eq (phi : 𝓓(Omega, ℝ)) :
    ‖gradientTestFunctionLp (mu := volume) p phi‖ =
      (eLpNorm (fderiv ℝ (phi : _ → ℝ)) p volume).toReal := by
  rw [norm_gradientTestFunctionLp,
    eLpNorm_restrict_eq_of_support_subset (support_gradient_testFunction_subset phi),
    eLpNorm_congr_norm_ae
      (ae_of_all _ fun x => norm_gradient_eq_norm_fderiv (𝕜 := ℝ) (phi : _ → ℝ) x)]

/-- The Poincaré inequality for a single test function whose domain lies in a slab. -/
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
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by finiteness) hfinite) hslab

/-- **The Poincaré inequality on `W^{1,p}_0(Ω)`.** If `1 ≤ p < ∞` and the domain
`Ω ⊆ ℝ^{n+1}` is trapped between the hyperplanes `xᵢ = a` and `xᵢ = b`, then every
`u ∈ W^{1,p}_0(Ω)` satisfies `‖u‖_p ≤ (b - a) ‖∇u‖_p`.

Only the width of the slab enters, so `Ω` need not be bounded; boundedness in one direction is
enough. -/
theorem W1p.norm_value_le_mul_norm_gradient_of_subset_slab (hp : p ≠ ∞) {i : Fin (n + 1)}
    {a b : ℝ} (hab : a ≤ b)
    (hOmega : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))), x i ∈ Icc a b)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ (b - a) * ‖W1p.gradient u‖ := by
  have hclosedL : IsClosed {v : W1p volume Omega p |
      ‖W1p.valueL v‖ ≤ (b - a) * ‖W1p.gradientL v‖} :=
    isClosed_le (W1p.valueL (mu := volume) (Omega := Omega) (p := p)).continuous.norm
      ((W1p.gradientL (mu := volume) (Omega := Omega) (p := p)).continuous.norm.const_mul _)
  have hclosed : IsClosed {v : W1p volume Omega p |
      ‖W1p.value v‖ ≤ (b - a) * ‖W1p.gradient v‖} := by
    simpa only [W1p.valueL_apply, W1p.gradientL_apply] using hclosedL
  apply mem_of_mem_w1p0Submodule hclosed _ hu
  intro phi
  simpa using norm_testFunctionLp_le_of_subset_slab hp hab hOmega phi

omit [Fact (1 ≤ p)] in
private theorem eLpNorm_restrict_eq_zero_of_coe_eq_empty
    {F : Type*} [NormedAddCommGroup F]
    (hempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ∅)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → F) :
    eLpNorm f p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) = 0 := by
  rw [hempty, Measure.restrict_empty, eLpNorm_measure_zero]

/-- **The Poincaré inequality on `W^{1,p}_0(Ω)` for a bounded domain.** If `1 ≤ p < ∞` and
`Ω ⊆ ℝ^{n+1}` is contained in a ball of radius `R`, then
`‖u‖_p ≤ 2R ‖∇u‖_p` for every `u ∈ W^{1,p}_0(Ω)`.

The constant `2R` is not sharp, but it is explicit and independent of the centre. -/
theorem W1p.norm_value_le_mul_norm_gradient_of_subset_ball
    {c : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ≠ ∞) {R : ℝ}
    (hOmega : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Metric.ball c R)
    {u : W1p volume Omega p} (hu : u ∈ w1p0Submodule volume Omega p) :
    ‖W1p.value u‖ ≤ 2 * R * ‖W1p.gradient u‖ := by
  rcases le_or_gt R 0 with hR | hR
  · have hball : Metric.ball c R = ∅ := Metric.ball_eq_empty.2 hR
    have hempty : (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ∅ :=
      subset_empty_iff.1 (hball ▸ hOmega)
    rw [Lp.norm_def, Lp.norm_def,
      eLpNorm_restrict_eq_zero_of_coe_eq_empty hempty,
      eLpNorm_restrict_eq_zero_of_coe_eq_empty hempty]
    simp
  have hslab : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      x (0 : Fin (n + 1)) ∈ Icc (c 0 - R) (c 0 + R) :=
    fun x hx => apply_mem_Icc_of_mem_ball (hOmega hx) 0
  have hwidth : (c 0 + R) - (c 0 - R) = 2 * R := by ring
  simpa only [hwidth] using W1p.norm_value_le_mul_norm_gradient_of_subset_slab hp
    (by linarith : c 0 - R ≤ c 0 + R) hslab hu

end TauCeti
