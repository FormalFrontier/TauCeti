/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# A local frame is dual to its coefficient functionals

Let `V → M` be a smooth vector bundle, let `e` be a trivialization of `V` and let `b` be a basis
of the model fibre, so that `e.localFrame b` is a local frame of `V` over `e.baseSet` with
coefficient functionals `e.localFrameCoeff I b`. This file records that over `e.baseSet` the frame
and its coefficient functionals are dual to each other: the `i`-th functional takes the value `1`
on the `i`-th frame vector and `0` on the others.

## Main results

* `TauCeti.Manifold.localFrameCoeff_basisAt`: the coefficient functionals are dual to the basis
  `e.basisAt b hx` of the fibre at a point of `e.baseSet`.
* `TauCeti.Manifold.localFrameCoeff_localFrame`: the same duality, stated for the frame sections
  themselves.
-/

public section

open Bundle Module Set
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
  [FiberBundle F V] [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
  {x : M} {ι : Type*} (b : Basis ι 𝕜 F)
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]

/-- A local frame is dual to its own coefficient functionals on the basis sections at `x`. -/
@[simp]
theorem localFrameCoeff_basisAt [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.basisAt b hx j) = if i = j then 1 else 0 := by
  rw [← e.localFrame_apply_of_mem_baseSet b hx,
    e.localFrameCoeff_apply_of_mem_baseSet b hx (e.localFrame b j) i,
    e.localFrame_apply_of_mem_baseSet b hx, Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

/-- A local frame is dual to its own coefficient functionals. -/
theorem localFrameCoeff_localFrame [DecidableEq ι] (hx : x ∈ e.baseSet) (i j : ι) :
    e.localFrameCoeff I b i x (e.localFrame b j x) = if i = j then 1 else 0 := by
  rw [e.localFrame_apply_of_mem_baseSet b hx, localFrameCoeff_basisAt b hx]

end TauCeti.Manifold
