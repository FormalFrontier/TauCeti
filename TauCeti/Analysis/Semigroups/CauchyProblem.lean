/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative

/-!
# The abstract Cauchy problem for a semigroup generator

This file introduces classical and mild solutions of the autonomous abstract Cauchy problem
`u' = A u`, `u(0) = x` on the nonnegative half-line.  The classical formulation uses the
derivative within the whole nonnegative half-line, which is two-sided at positive times and
right-sided at zero.  A mild solution instead asks for continuity and the integrated
identity

`A (integral u on (0, t]) = u t - x`.

The orbit `t ↦ S(t)x` of a strongly continuous semigroup is a mild solution for every initial
vector.  When the initial vector lies in the generator domain, domain invariance and the orbit
derivative formula upgrade it to a classical solution.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part A, the abstract Cauchy
problem milestone.  The definitions and proofs follow Engel--Nagel, *One-Parameter Semigroups
for Linear Evolution Equations*, Section II.6.

## Main declarations

* `IsClassicalSolution`: classical solutions on `[0, ∞)`.
* `IsMildSolution`: mild solutions in integrated form.
* `StronglyContinuousSemigroup.isClassicalSolution_realOperator`: generator-domain orbits are
  classical solutions.
* `StronglyContinuousSemigroup.isMildSolution_realOperator`: all orbits are mild solutions.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A classical solution of `u' = A u`, `u(0) = x`, on `[0, ∞)`. Its values belong to the
domain of `A`, and it has a continuous derivative within `[0, ∞)` equal to `A (u t)`. -/
def IsClassicalSolution (A : X →ₗ.[ℝ] X) (x : X) (u : ℝ → X) : Prop :=
  u 0 = x ∧ ∃ u' : ℝ → X, ContinuousOn u' (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t → ∃ hut : u t ∈ A.domain,
      HasDerivWithinAt u (u' t) (Set.Ici 0) t ∧ u' t = A ⟨u t, hut⟩

/-- A classical solution takes its prescribed initial value at time zero. -/
theorem IsClassicalSolution.apply_zero {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsClassicalSolution A x u) : u 0 = x :=
  hu.1

/-- Characterization of a classical solution by its initial value and continuously
differentiable equation. -/
theorem isClassicalSolution_iff {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X} :
    IsClassicalSolution A x u ↔
      u 0 = x ∧ ∃ u' : ℝ → X, ContinuousOn u' (Set.Ici 0) ∧
        ∀ t : ℝ, 0 ≤ t → ∃ hut : u t ∈ A.domain,
          HasDerivWithinAt u (u' t) (Set.Ici 0) t ∧ u' t = A ⟨u t, hut⟩ :=
  Iff.rfl

/-- Every value of a classical solution at nonnegative time belongs to the operator domain. -/
theorem IsClassicalSolution.mem_domain {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsClassicalSolution A x u) {t : ℝ} (ht : 0 ≤ t) : u t ∈ A.domain :=
  (hu.2.choose_spec.2 t ht).choose

/-- The derivative within the nonnegative half-line of a classical solution is the operator
applied to its value. -/
theorem IsClassicalSolution.hasDerivWithinAt {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsClassicalSolution A x u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt u (A ⟨u t, hu.mem_domain ht⟩) (Set.Ici 0) t := by
  obtain ⟨hut, hderiv, heq⟩ := hu.2.choose_spec.2 t ht
  rw [← heq]
  simpa only using hderiv

/-- A classical solution is continuous on the nonnegative half-line. -/
theorem IsClassicalSolution.continuousOn {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsClassicalSolution A x u) : ContinuousOn u (Set.Ici 0) := by
  intro t ht
  exact (hu.hasDerivWithinAt ht).continuousWithinAt

/-- A mild solution of `u' = A u`, `u(0) = x`, on `[0, ∞)`.  The integral is pointwise
Bochner integration in `X`.  Requiring the integral to lie in the domain makes the expression
`A (∫ s in (0, t], u s)` meaningful for an unbounded operator. -/
def IsMildSolution [CompleteSpace X] (A : X →ₗ.[ℝ] X) (x : X) (u : ℝ → X) : Prop :=
  ContinuousOn u (Set.Ici 0) ∧ u 0 = x ∧
    ∀ t : ℝ, 0 ≤ t → ∃ hut : (∫ s in Set.Ioc 0 t, u s) ∈ A.domain,
      A ⟨∫ s in Set.Ioc 0 t, u s, hut⟩ = u t - x

/-- A mild solution is continuous on the nonnegative half-line. -/
theorem IsMildSolution.continuousOn [CompleteSpace X] {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsMildSolution A x u) : ContinuousOn u (Set.Ici 0) :=
  hu.1

/-- A mild solution takes its prescribed initial value at time zero. -/
theorem IsMildSolution.apply_zero [CompleteSpace X] {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsMildSolution A x u) : u 0 = x :=
  hu.2.1

/-- Characterization of a mild solution by continuity and its integrated Cauchy equation. -/
theorem isMildSolution_iff [CompleteSpace X] {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X} :
    IsMildSolution A x u ↔ ContinuousOn u (Set.Ici 0) ∧ u 0 = x ∧
      ∀ t : ℝ, 0 ≤ t → ∃ hut : (∫ s in Set.Ioc 0 t, u s) ∈ A.domain,
        A ⟨∫ s in Set.Ioc 0 t, u s, hut⟩ = u t - x :=
  Iff.rfl

/-- The time integral of a mild solution belongs to the operator domain. -/
theorem IsMildSolution.integral_mem_domain [CompleteSpace X]
    {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsMildSolution A x u) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in Set.Ioc 0 t, u s) ∈ A.domain :=
  (hu.2.2 t ht).choose

/-- The integrated Cauchy equation satisfied by a mild solution. -/
theorem IsMildSolution.map_integral_eq_sub [CompleteSpace X]
    {A : X →ₗ.[ℝ] X} {x : X} {u : ℝ → X}
    (hu : IsMildSolution A x u) {t : ℝ} (ht : 0 ≤ t) :
    A ⟨∫ s in Set.Ioc 0 t, u s, hu.integral_mem_domain ht⟩ = u t - x := by
  obtain ⟨hut, hmap⟩ := hu.2.2 t ht
  simpa only [Submodule.coe_mk] using hmap

namespace StronglyContinuousSemigroup

variable [CompleteSpace X]

/-- The orbit of a generator-domain vector is a classical solution of the abstract Cauchy
problem for the generator. -/
theorem isClassicalSolution_realOperator (S : StronglyContinuousSemigroup X) (x : S.domain) :
    IsClassicalSolution S.generator (x : X) (fun t => S.realOperator t x) := by
  rw [isClassicalSolution_iff]
  let z : X := S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩
  refine ⟨S.realOperator_zero_apply x, fun t => S.realOperator t z,
    S.realOperator_continuousOn_Ici z, fun t ht => ?_⟩
  let hut : S.realOperator t (x : X) ∈ S.generator.domain := by
    rw [S.generator_domain]
    exact S.realOperator_mem_domain ht x.property
  refine ⟨hut, ?_⟩
  refine ⟨?_, ?_⟩
  · dsimp only [z]
    rw [← S.realOperator_generator_map ht x]
    simpa only [Submodule.coe_mk] using S.realOperator_hasDerivWithinAt_Ici x ht
  · simpa only [z, hut] using (S.realOperator_generator_map ht x).symm

/-- Every orbit is a mild solution of the abstract Cauchy problem for the generator. -/
theorem isMildSolution_realOperator (S : StronglyContinuousSemigroup X) (x : X) :
    IsMildSolution S.generator x (fun t => S.realOperator t x) := by
  rw [isMildSolution_iff]
  refine ⟨S.realOperator_continuousOn_Ici x, S.realOperator_zero_apply x, fun t ht => ?_⟩
  rcases ht.eq_or_lt with rfl | ht
  · refine ⟨?_, ?_⟩
    · simp
    · have harg : (⟨∫ s in Set.Ioc 0 0, S.realOperator s x, by simp⟩ :
          S.generator.domain) = 0 := by
        ext
        simp
      rw [harg, LinearPMap.map_zero]
      simp
  · let hut : (∫ s in Set.Ioc 0 t, S.realOperator s x) ∈ S.generator.domain := by
      rw [S.generator_domain]
      exact S.integral_orbit_mem_domain x ht
    refine ⟨hut, ?_⟩
    simpa only [Submodule.coe_mk] using S.generator_integral_orbit x ht

end StronglyContinuousSemigroup

end TauCeti.Semigroups
