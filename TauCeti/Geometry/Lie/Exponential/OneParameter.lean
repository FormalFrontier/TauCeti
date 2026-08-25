/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Lie.Exponential.Units.Basic

/-!
# One-parameter subgroups from the Banach algebra exponential

For an element `x` of a complete normed real algebra, `TauCeti.expUnitHom` bundles
`t ↦ expUnit (t • x)` as a continuous one-parameter subgroup. This file records the smoothness
and initial velocity of its underlying curve, and characterizes the subgroup by that velocity.

This is the concrete Banach-algebra model for the one-parameter subgroups associated to a future
abstract Lie-group exponential map.

## Main results

* `TauCeti.contDiff_exp_smul`: the algebra-valued exponential curve is real analytic.
* `TauCeti.contMDiff_expUnit_smul`: the corresponding units-valued curve is real analytic.
* `TauCeti.contMDiff_expUnitHom`: the bundled subgroup's underlying curve is real analytic.
* `TauCeti.hasDerivAt_expUnitHom_val_zero`: its initial velocity is `x`.
* `TauCeti.continuousMonoidHom_eq_expUnitHom_of_hasDerivAt`: it is the unique continuous
  one-parameter subgroup with that initial velocity.
* `TauCeti.expUnitHom_injective`: distinct velocities generate distinct one-parameter subgroups.
* `TauCeti.expUnitHom_inj`: the resulting equality normal form.
* `TauCeti.existsUnique_eq_expUnitHom`: a continuous one-parameter subgroup of `Rˣ` whose
  underlying curve is differentiable at `0` is `expUnitHom x` for a unique `x : R`.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "One-parameter subgroups" and "The matrix and circle shadows".
-/

public section

namespace TauCeti

open scoped ContDiff Manifold

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The algebra-valued exponential curve `t ↦ exp (t • x)` is real analytic. -/
@[fun_prop]
theorem contDiff_exp_smul (x : R) :
    ContDiff ℝ ω (fun t : ℝ => NormedSpace.exp (t • x)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have h : AnalyticAt ℝ (fun s : ℝ => s • x) t := by fun_prop
  -- Expose the composition so `AnalyticAt.comp` applies to the scalar-line map.
  change ContDiffAt ℝ ω (NormedSpace.exp ∘ fun s : ℝ => s • x) t
  exact (AnalyticAt.comp (f := fun s : ℝ => s • x)
    (NormedSpace.exp_analytic (𝕂 := ℝ) (t • x)) h).contDiffAt

/-- The units-valued exponential curve `t ↦ expUnit (t • x)` is real analytic. -/
theorem contMDiff_expUnit_smul (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ω (fun t : ℝ => expUnit (t • x)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [show Units.val ∘ (fun t : ℝ => expUnit (t • x)) =
      fun t : ℝ => NormedSpace.exp (t • x) by
    funext t
    exact expUnit_coe (t • x)]
  exact (contDiff_exp_smul x).contMDiff

/-- The curve underlying `expUnitHom x` is real analytic. -/
theorem contMDiff_expUnitHom (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ω
      (fun t : ℝ => expUnitHom x (Multiplicative.ofAdd t)) := by
  simpa only [expUnitHom_apply] using contMDiff_expUnit_smul x

/-- After embedding `Rˣ` in its model space `R`, the initial velocity of `expUnitHom x` is `x`.

Since the manifold structure on `Rˣ` is induced by this open embedding, this is the concrete
tangent-space statement for the one-parameter subgroup. -/
theorem hasDerivAt_expUnitHom_val_zero (x : R) :
    HasDerivAt (fun t : ℝ => (expUnitHom x (Multiplicative.ofAdd t) : R)) x 0 := by
  simpa only [expUnitHom_apply, expUnit_coe, zero_smul, NormedSpace.exp_zero, one_mul] using
    hasDerivAt_exp_smul_const x (0 : ℝ)

/-- A continuous one-parameter subgroup of `Rˣ` is determined by its initial velocity in `R`. -/
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
    rw [← hshift] at hderiv
    exact hderiv
  have hg (t : ℝ) : HasDerivAt g (g t * x) t := hasDerivAt_exp_smul_const x t
  let rightMul : R →L[ℝ] R := ContinuousLinearMap.mulLeftRight ℝ R 1 x
  have hv : ∀ _ : ℝ, LipschitzOnWith ‖rightMul‖₊ rightMul Set.univ :=
    fun _ => rightMul.lipschitz.lipschitzOnWith
  have hfg : f = g := ODE_solution_unique_univ (K := ‖rightMul‖₊)
    (v := fun _ => rightMul) (s := fun _ => Set.univ) (t₀ := 0) hv
    (fun t => ⟨by simpa [rightMul] using hf t, Set.mem_univ _⟩)
    (fun t => ⟨by simpa [rightMul] using hg t, Set.mem_univ _⟩) (by simp [f, g])
  apply ContinuousMonoidHom.ext
  intro t
  rw [← ofAdd_toAdd t, expUnitHom_apply]
  apply Units.ext
  rw [expUnit_coe]
  exact congrFun hfg (Multiplicative.toAdd t)

/-- Distinct velocities generate distinct one-parameter subgroups: the generator is recovered from
`expUnitHom x` as the initial velocity of its underlying curve. -/
@[grind inj]
theorem expUnitHom_injective :
    Function.Injective (expUnitHom : R → ContinuousMonoidHom (Multiplicative ℝ) Rˣ) := by
  intro x y hxy
  have hx := hasDerivAt_expUnitHom_val_zero x
  rw [hxy] at hx
  exact hx.unique (hasDerivAt_expUnitHom_val_zero y)

/-- Two exponential one-parameter subgroups agree exactly when their velocities do. -/
@[simp]
theorem expUnitHom_inj {x y : R} : expUnitHom x = expUnitHom y ↔ x = y :=
  expUnitHom_injective.eq_iff

/-- **The differentiable one-parameter subgroups of `Rˣ` are exactly the exponentials.** A
continuous one-parameter subgroup whose underlying curve is differentiable at `0` is
`expUnitHom x` for a unique `x : R`. Together with `expUnitHom_injective` this identifies the
one-parameter subgroups satisfying that differentiability hypothesis with `R`, the Lie algebra of
`Rˣ`. The unrestricted bijection between all of `ContinuousMonoidHom (Multiplicative ℝ) Rˣ` and
`R` needs the automatic-smoothness theorem that a merely continuous one-parameter subgroup is
already differentiable, which is not proved here. The differentiability hypothesis is stated for
the `R`-valued curve, since that is where the Banach-space derivative lives. -/
theorem existsUnique_eq_expUnitHom (φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ)
    (hφ : DifferentiableAt ℝ (fun t : ℝ => (φ (Multiplicative.ofAdd t) : R)) 0) :
    ∃! x : R, φ = expUnitHom x := by
  refine ⟨deriv (fun t : ℝ => (φ (Multiplicative.ofAdd t) : R)) 0,
    continuousMonoidHom_eq_expUnitHom_of_hasDerivAt φ _ hφ.hasDerivAt, fun y hy => ?_⟩
  exact expUnitHom_injective (hy.symm.trans
    (continuousMonoidHom_eq_expUnitHom_of_hasDerivAt φ _ hφ.hasDerivAt))

end TauCeti
