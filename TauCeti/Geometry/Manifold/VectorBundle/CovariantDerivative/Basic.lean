/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Covariant derivatives of finite sums of sections

Mathlib's `IsCovariantDerivativeOn` is additive on pairs of sections differentiable at a point of
the set it is a covariant derivative on. This file iterates that additivity to finite sums of
sections.

## Main results

* `TauCeti.Manifold.covariantDerivative_sum`: a covariant derivative over `u` commutes with finite
  sums of sections differentiable at a point of `u`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {x : M}
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}

/-- A covariant derivative over `u` commutes with finite sums of sections differentiable at a
point of `u`. -/
theorem covariantDerivative_sum {κ : Type*} {u : Set M} {s : Finset κ} {τ : κ → Π x : M, V x}
    (hcov : IsCovariantDerivativeOn F cov u) (hx : x ∈ u)
    (hτ : ∀ i ∈ s, MDiffAt (T% (τ i)) x) :
    cov (∑ i ∈ s, τ i) x = ∑ i ∈ s, cov (τ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hcov.zero hx
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hτ
    have hsum : MDiffAt (T% (∑ j ∈ s, τ j)) x := by
      simpa [Finset.sum_apply] using
        MDifferentiableAt.sum_section (t := fun j (y : M) ↦ τ j y) (s := s) hτ.2
    rw [Finset.sum_insert hi, hcov.add hτ.1 hsum hx, ih hτ.2, Finset.sum_insert hi]

end TauCeti.Manifold
