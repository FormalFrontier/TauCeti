/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Products of nonarchimedean groups and rings

An arbitrary product of nonarchimedean groups is nonarchimedean, and likewise for rings.
Mathlib has only the binary case, `Prod.instNonarchimedeanGroup`; these are the `Pi` analogues,
stated over an unrestricted index type.

No finiteness hypothesis is needed. A neighbourhood of the identity in the product topology
contains a box that constrains only finitely many coordinates, so shrinking those finitely many
factors to open subgroups and leaving the rest unconstrained produces an open subgroup inside it.

These live in the `Pi` namespace of the construction they describe rather than in a `TauCeti`
one, following `TauCeti/Topology/Algebra/Nonarchimedean/Completion.lean`.

## Main results

* `Pi.instNonarchimedeanGroup`: a product of nonarchimedean groups is nonarchimedean, together
  with its additive version `Pi.instNonarchimedeanAddGroup`.
* `Pi.instNonarchimedeanRing`: a product of nonarchimedean rings is nonarchimedean.

## Implementation notes

Mathlib's `library_note «non-Archimedean non-instances»` explains why the *subgroup basis*
lemmas cannot be instances: they would send typeclass search after an
`@IsTopologicalAddGroup β ?m1 ?m2` whose topology and group structure are both unknown. That
obstruction does not arise here, since every structure on `∀ i, G i` is fixed by the
corresponding `Pi` instance, which is also why Mathlib states the binary case as an instance.

## References

* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean`, whose
  `Prod.instNonarchimedeanGroup` these generalise.
-/

public section

open Filter

/-- A product of nonarchimedean groups is nonarchimedean. -/
@[to_additive /-- A product of nonarchimedean additive groups is nonarchimedean. -/]
instance Pi.instNonarchimedeanGroup {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, NonarchimedeanGroup (G i)] :
    NonarchimedeanGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi] at hU
    obtain ⟨I, hI, V, hV, hVU⟩ := Filter.mem_pi.mp hU
    choose W hW using fun i ↦ NonarchimedeanGroup.is_nonarchimedean (V i) (hV i)
    refine ⟨⟨Subgroup.pi I fun i ↦ (W i).toSubgroup, ?_⟩, ?_⟩
    · exact isOpen_set_pi hI fun i _ ↦ (W i).isOpen
    · exact (Set.pi_mono fun i _ ↦ hW i).trans hVU

/-- A product of nonarchimedean rings is nonarchimedean. -/
instance Pi.instNonarchimedeanRing {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)]
    [∀ i, TopologicalSpace (R i)] [∀ i, NonarchimedeanRing (R i)] :
    NonarchimedeanRing (∀ i, R i) where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean
