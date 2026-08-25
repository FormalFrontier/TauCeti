/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.DenseSubmodule
public import TauCeti.Topology.Algebra.IsUniformGroup.Submodule

/-!
# Submodules with a module-finite closure are closed

A submodule of a complete, metrisable module over a complete Tate ring whose topological closure
is module-finite is itself closed. This is Bosch–Güntzer–Remmert §3.7.2/1 in its closure form, and
it is the closedness prerequisite on the route to Wedhorn 6.17/6.18.

The proof is one application of `TauCeti.Huber.eq_top_of_dense_of_module_finite`, made inside the
closure `N.topologicalClosure` rather than inside the ambient module. That closure is closed in a
complete space, so it is complete — the one instance that has to be supplied by hand; it is a
uniform additive group with a countably generated uniformity by `Submodule.isUniformAddGroup` and
`Submodule.isCountablyGenerated_uniformity`; and it is module-finite by hypothesis. Inside that
closure the submodule `N` is dense, by the very definition of the closure. So `N` is everything in
the closure, that is `N.topologicalClosure = N`, and `N` is closed because its closure is.

## Main results

* `TauCeti.Huber.isClosed_of_module_finite_topologicalClosure`: a submodule whose topological
  closure is module-finite is closed.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch_guntzer_remmert], §3.7.2/1.
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Propositions 6.17–6.18.

## Provenance

Adapted from the AINTLIB development (`github.com/CBirkbeck/AINTLIB`, Apache-2.0), branch
`dev/adic-spaces` at commit `37bbdaeb9ad9`, file
`projects/AdicSpaces/Adic spaces/WedhornBanachTheorem.lean`, where the same statement is
`fg_topologicalClosure_isClosed`. The argument is AINTLIB's, and the density step follows its
proof closely. Three things differ. AINTLIB establishes the uniform-group, countable-generation,
separation and `ContinuousSMul` instances on the closure by hand; here all four are found by
instance search — the first two from `Submodule.isUniformAddGroup` and
`Submodule.isCountablyGenerated_uniformity`, the last from this repository's `ContinuousSMul`
instance on a submodule — so only completeness is supplied. The engine is this repository's
`TauCeti.Huber.eq_top_of_dense_of_module_finite`, stated with `T0Space`, rather than AINTLIB's
`T2Space`-based `eq_top_of_dense_of_finite`. And the passage from `N' = ⊤` back to
`N.topologicalClosure ≤ N` is `Submodule.comap_subtype_eq_top` rather than AINTLIB's element-level
unfolding.
-/

open Filter Topology
open scoped Uniformity

public section

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T2Space A] [IsTopologicalRing A] [IsTateRing A]
  {V : Type*} [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V] [CompleteSpace V]
  [(𝓤 V).IsCountablyGenerated] [T0Space V] [Module A V] [ContinuousSMul A V]

/-- **A submodule whose topological closure is module-finite is closed**
(Bosch–Güntzer–Remmert §3.7.2/1).

Working inside `N.topologicalClosure`, which is complete because it is closed in a complete space,
the submodule `N` is dense and that closure is module-finite, so
`eq_top_of_dense_of_module_finite` gives `N = N.topologicalClosure`. -/
theorem isClosed_of_module_finite_topologicalClosure (N : Submodule A V)
    (hfin : Module.Finite A N.topologicalClosure) : IsClosed (N : Set V) := by
  have hclosed : IsClosed (N.topologicalClosure : Set V) := N.isClosed_topologicalClosure
  have : CompleteSpace N.topologicalClosure := hclosed.completeSpace_coe
  -- `N` seen inside its own closure, where it is dense.
  set N' : Submodule A N.topologicalClosure := N.comap N.topologicalClosure.subtype
  have himg : Subtype.val '' (N' : Set N.topologicalClosure) = (N : Set V) := by
    ext z
    exact ⟨fun ⟨⟨_, _⟩, hw, hwz⟩ ↦ hwz ▸ hw, fun hz ↦ ⟨⟨z, N.le_topologicalClosure hz⟩, hz, rfl⟩⟩
  have hdense : Dense (N' : Set N.topologicalClosure) := fun x ↦ by
    rw [closure_subtype, himg, ← N.topologicalClosure_coe]
    exact x.2
  -- `N' = ⊤` inside the closure says exactly that the closure is contained in `N`.
  have hle : N.topologicalClosure ≤ N :=
    Submodule.comap_subtype_eq_top.mp (eq_top_of_dense_of_module_finite N' hdense)
  exact le_antisymm hle N.le_topologicalClosure ▸ hclosed

end TauCeti.Huber
