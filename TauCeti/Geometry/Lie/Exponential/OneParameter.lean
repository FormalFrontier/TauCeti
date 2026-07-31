/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Lie.Exponential.Units

/-!
# One-parameter subgroups from the Banach algebra exponential

For an element `x` of a complete normed real algebra, `TauCeti.expUnitHom` bundles
`t ↦ expUnit (t • x)` as a continuous one-parameter subgroup. This file records the smoothness
and initial velocity of its underlying curve, and characterizes the subgroup by that velocity.

This is the concrete Banach-algebra model for the one-parameter subgroups associated to a future
abstract Lie-group exponential map.

## Main results

* `TauCeti.contDiff_exp_smul`: the algebra-valued exponential curve is smooth.
* `TauCeti.contMDiff_expUnit_smul`: the corresponding units-valued curve is smooth.
* `TauCeti.contMDiff_expUnitHom`: the bundled subgroup's underlying curve is smooth.
* `TauCeti.hasDerivAt_expUnitHom_val_zero`: its initial velocity is `x`.
* `TauCeti.continuousMonoidHom_eq_expUnitHom_of_hasDerivAt`: it is the unique continuous
  one-parameter subgroup with that initial velocity.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "One-parameter subgroups" and "The matrix and circle shadows".
-/

public section

namespace TauCeti

open scoped ContDiff Manifold

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] normedAlgebraRatOfReal

/-- The algebra-valued exponential curve `t ↦ exp (t • x)` is smooth. -/
theorem contDiff_exp_smul (x : R) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp (t • x)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have h : AnalyticAt ℝ (fun s : ℝ => s • x) t := by fun_prop
  change ContDiffAt ℝ ∞ (NormedSpace.exp ∘ fun s : ℝ => s • x) t
  exact (AnalyticAt.comp (f := fun s : ℝ => s • x)
    (NormedSpace.exp_analytic (𝕂 := ℝ) (t • x)) h).contDiffAt

/-- The units-valued exponential curve `t ↦ expUnit (t • x)` is smooth. -/
theorem contMDiff_expUnit_smul (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ∞ (fun t : ℝ => expUnit (t • x)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [show Units.val ∘ (fun t : ℝ => expUnit (t • x)) =
      fun t : ℝ => NormedSpace.exp (t • x) by
    funext t
    exact expUnit_coe (t • x)]
  exact (contDiff_exp_smul x).contMDiff

/-- The curve underlying `expUnitHom x` is smooth. -/
theorem contMDiff_expUnitHom (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ∞
      (fun t : ℝ => expUnitHom x (Multiplicative.ofAdd t)) := by
  simpa only [expUnitHom_apply] using contMDiff_expUnit_smul x

/-- After embedding `Rˣ` in its model space `R`, the initial velocity of `expUnitHom x` is `x`.

Since the manifold structure on `Rˣ` is induced by this open embedding, this is the concrete
tangent-space statement for the one-parameter subgroup. -/
theorem hasDerivAt_expUnitHom_val_zero (x : R) :
    HasDerivAt (fun t : ℝ => (expUnitHom x (Multiplicative.ofAdd t) : R)) x 0 := by
  simpa only [expUnitHom_apply, expUnit_coe, zero_smul, NormedSpace.exp_zero, one_mul] using
    hasDerivAt_exp_smul_const x (0 : ℝ)

/-- A continuous one-parameter subgroup of `Rˣ` is determined by its initial velocity in `R`.

The homomorphism law transports the derivative at zero to the autonomous ODE `f' = f * x` at
every time. Global uniqueness for that Lipschitz ODE then identifies the subgroup with
`expUnitHom x`. -/
theorem continuousMonoidHom_eq_expUnitHom_of_hasDerivAt
    (φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ) (x : R)
    (hφ : HasDerivAt (fun t : ℝ => (φ (Multiplicative.ofAdd t) : R)) x 0) :
    φ = expUnitHom x := by
  let f : ℝ → R := fun t => (φ (Multiplicative.ofAdd t) : R)
  let g : ℝ → R := fun t => NormedSpace.exp (t • x)
  have hφ' : HasDerivAt f x 0 := hφ
  have hf (t : ℝ) : HasDerivAt f (f t * x) t := by
    have hshift : f = fun s => f t * f (s - t) := by
      funext s
      dsimp only [f]
      rw [← Units.val_mul]
      apply congrArg Units.val
      rw [← map_mul]
      rw [← ofAdd_add]
      congr 1
      abel_nf
    have hcomp := hφ'.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
    have hderiv : HasDerivAt (fun s => f t * f (s - t)) (f t * x) t := by
      simpa only [Function.comp_apply, id_eq, one_smul] using hcomp.const_mul (f t)
    convert hderiv using 1
  have hg (t : ℝ) : HasDerivAt g (g t * x) t := by
    exact hasDerivAt_exp_smul_const x t
  have hv : ∀ _ : ℝ, LipschitzOnWith ‖x‖₊ (fun y : R => y * x) Set.univ := by
    intro _
    apply LipschitzOnWith.of_dist_le_mul
    intro a _ b _
    simpa only [dist_eq_norm, ← sub_mul, coe_nnnorm, mul_comm] using
      norm_mul_le (a - b) x
  have hfg : f = g := ODE_solution_unique_univ (K := ‖x‖₊)
    (v := fun (_ : ℝ) (y : R) => y * x) (s := fun _ => Set.univ) (t₀ := 0) hv
    (fun t => ⟨hf t, Set.mem_univ _⟩) (fun t => ⟨hg t, Set.mem_univ _⟩) (by
      simp [f, g])
  apply ContinuousMonoidHom.ext
  intro t
  rw [show t = Multiplicative.ofAdd (Multiplicative.toAdd t) by rfl, expUnitHom_apply]
  apply Units.ext
  rw [expUnit_coe]
  exact congrFun hfg (Multiplicative.toAdd t)

end TauCeti
