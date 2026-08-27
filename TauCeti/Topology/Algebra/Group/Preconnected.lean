/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Homomorphisms from preconnected topological groups

This file records a local-to-global principle for monoid homomorphisms from a preconnected
topological group: two such homomorphisms that agree near the identity agree everywhere.
-/

public section

open Filter
open scoped Topology

/-- Two monoid homomorphisms from a preconnected topological group that agree near the identity
agree everywhere. -/
theorem MonoidHom.eq_of_eventuallyEq_one
    {G M : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    [PreconnectedSpace G] [Monoid M]
    {φ ψ : G →* M} (h : φ =ᶠ[𝓝 (1 : G)] ψ) : φ = ψ := by
  let S := φ.eqLocus ψ
  have hS : (S : Set G) ∈ 𝓝 (1 : G) := by
    -- Expose equality-locus membership as the pointwise equality used by the filter statement.
    change φ =ᶠ[𝓝 (1 : G)] ψ
    exact h
  have hopen : IsOpen (S : Set G) := S.isOpen_of_mem_nhds hS
  have hclosed : IsClosed (S : Set G) := S.isClosed_of_isOpen hopen
  have huniv : (S : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨1, S.one_mem⟩
  apply MonoidHom.ext
  intro g
  -- Expose equality-locus membership as the pointwise equality required by extensionality.
  change g ∈ S
  have hg : g ∈ (S : Set G) := by
    rw [huniv]
    trivial
  exact hg
