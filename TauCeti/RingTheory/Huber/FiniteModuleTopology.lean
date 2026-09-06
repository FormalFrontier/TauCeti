/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ClosedSubmodule
public import TauCeti.Topology.Algebra.Module.Finite

/-!
# The canonical topology on a finite module over a Tate ring

Let `A` be a complete Hausdorff noetherian Tate ring and let `M` be a finite `A`-module. This
file proves that Mathlib's `moduleTopology A M` is Hausdorff, the separatedness clause of
[Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(1).

Choose a finite spanning family of `M`. Its linear-combination map `Aⁿ → M` is an open quotient
for the module topologies, and its kernel is closed by
`TauCeti.Huber.isClosed_of_isNoetherian`, so the closed-equivalence-relation criterion applies.

Separatedness is the one clause of Proposition 6.18(1) that uses `A` being a noetherian Tate
ring. The other three — first countability, nonarchimedeanness, and completeness of the canonical
right uniformity — need nothing of `A` beyond those same properties, and are proved in that
generality in `TauCeti.Topology.Algebra.Module.Finite`; a Huber ring supplies the hypotheses they
do need through `TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero` and
`TauCeti.Huber.IsHuberRing.toNonarchimedeanRing`. That file is re-exported here, so that this
module is the single entry point for the whole existence half of Proposition 6.18(1).

Together with `TauCeti.Huber.IsTateRing.isModuleTopology`, these results give the existence and
uniqueness asserted by Proposition 6.18(1), among the complete Hausdorff first-countable
nonarchimedean topological module structures occurring in the open-mapping theorem. The topology
is kept as the explicit expression `moduleTopology A M` in the statement: this is a theorem
constructor for a local instance, rather than a global instance whose head would hide the
topology on `M` from typeclass search.

## Main results

* `TauCeti.Huber.IsTateRing.t2Space_moduleTopology`: the canonical topology is Hausdorff.

The remaining three clauses are re-exported from `TauCeti.Topology.Algebra.Module.Finite`:
`TauCeti.firstCountableTopology_moduleTopology`, `TauCeti.nonarchimedeanAddGroup_moduleTopology`
and `TauCeti.completeSpace_moduleTopology`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(1).
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The module topology on a finite module over a complete noetherian Tate ring is
Hausdorff.** This supplies the separatedness clause of Wedhorn Proposition 6.18(1). -/
theorem IsTateRing.t2Space_moduleTopology [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [IsTateRing A] [IsNoetherianRing A] :
    @T2Space M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  have _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  rw [t2Space_iff_of_isOpenQuotientMap hquot]
  have hker : IsClosed ((LinearMap.ker f : Submodule A (Fin n → A)) : Set (Fin n → A)) :=
    isClosed_of_isNoetherian (LinearMap.ker f)
  have hsub : Continuous (fun q : (Fin n → A) × (Fin n → A) ↦ q.1 - q.2) :=
    continuous_fst.sub continuous_snd
  convert hker.preimage hsub using 1
  ext q
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, map_sub,
    sub_eq_zero]

end TauCeti.Huber

end
