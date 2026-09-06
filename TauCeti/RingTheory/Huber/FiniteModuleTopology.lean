/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ClosedSubmodule
import TauCeti.Topology.Algebra.Nonarchimedean.Basic
import TauCeti.Topology.Algebra.Nonarchimedean.Pi

/-!
# The canonical topology on a finite module over a Tate ring

Let `A` be a complete Hausdorff noetherian Tate ring and let `M` be a finite `A`-module. This
file proves the existence half of [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(1):
Mathlib's `moduleTopology A M` is Hausdorff, first countable, nonarchimedean, and complete for its
canonical right uniformity.

Choose a finite spanning family of `M`. Its linear-combination map `Aⁿ → M` is an open quotient
for the module topologies. First countability descends immediately along this open quotient. Its
kernel is closed by `TauCeti.Huber.isClosed_of_isNoetherian`, so the closed-equivalence-relation
criterion gives Hausdorffness. Completeness follows from Mathlib's theorem that a quotient of a
complete first-countable additive group is complete, transported across the first-isomorphism
homeomorphism. Nonarchimedeanness descends along the same open quotient.

Only the Hausdorff clause needs `A` to be a noetherian Tate ring. The other three ask of `A`
exactly what their proofs consume — first countability, nonarchimedeanness, and completeness — so
they are stated under those hypotheses instead. A Huber ring supplies the first two through
`TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero` and
`TauCeti.Huber.IsHuberRing.toNonarchimedeanRing`, which is why they still belong beside the
Hausdorff clause: Proposition 6.18(1) is the statement they are assembled for.

Together with `TauCeti.Huber.IsTateRing.isModuleTopology`, these results give the existence and
uniqueness asserted by Proposition 6.18(1), among the complete Hausdorff first-countable
nonarchimedean topological module structures occurring in the open-mapping theorem. The topology
is kept as the explicit expression `moduleTopology A M` in the statements: these are theorem
constructors for local instances, rather than global instances whose heads would hide the
topology on `M` from typeclass search.

## Main results

* `TauCeti.Huber.IsTateRing.t2Space_moduleTopology`: the canonical topology is Hausdorff.
* `TauCeti.Huber.firstCountableTopology_moduleTopology`: the canonical topology is first
  countable.
* `TauCeti.Huber.nonarchimedeanAddGroup_moduleTopology`: the canonical additive group is
  nonarchimedean.
* `TauCeti.Huber.completeSpace_moduleTopology`: its canonical right uniformity is complete.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(1).
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The module topology on a finite module over a first-countable topological ring is first
countable.** This supplies the first-countability clause of Wedhorn Proposition 6.18(1), a Huber
ring being first countable by `TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`. -/
theorem firstCountableTopology_moduleTopology [TopologicalSpace A]
    [IsTopologicalRing A] [FirstCountableTopology A] :
    @FirstCountableTopology M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← hquot.map_nhds_eq x]
  infer_instance

/-- **The module topology on a finite module over a complete noetherian Tate ring is
Hausdorff.** This supplies the separatedness clause of Wedhorn Proposition 6.18(1). -/
theorem IsTateRing.t2Space_moduleTopology [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] [IsTateRing A] [IsNoetherianRing A] :
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

/-- **The additive group of a finite module over a nonarchimedean topological ring, with its
module topology, is nonarchimedean.** This is the nonarchimedean clause of Wedhorn Proposition
6.18(1), a Huber ring being nonarchimedean by
`TauCeti.Huber.IsHuberRing.toNonarchimedeanRing`. -/
theorem nonarchimedeanAddGroup_moduleTopology [TopologicalSpace A]
    [IsTopologicalRing A] [NonarchimedeanAddGroup A] :
    @NonarchimedeanAddGroup M _ (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  exact NonarchimedeanAddGroup.nonarchimedean_of_isOpenMap f.toAddMonoidHom
    (IsModuleTopology.continuous_of_linearMap f).continuousAt
    (IsModuleTopology.isOpenQuotientMap_of_surjective hf).isOpenMap

/-- **The canonical right uniformity of the module topology on a finite module over a complete
first-countable ring is complete.** This supplies the completeness clause of Wedhorn Proposition
6.18(1), a Huber ring being first countable by
`TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`. -/
theorem completeSpace_moduleTopology [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [FirstCountableTopology A] :
    letI : TopologicalSpace M := moduleTopology A M
    letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    CompleteSpace M := by
  let _ : TopologicalSpace M := moduleTopology A M
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have _ : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  let Q := (Fin n → A) ⧸ LinearMap.ker f
  let _ : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have _ : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have _ : CompleteSpace Q :=
    QuotientAddGroup.completeSpace_right (Fin n → A) (LinearMap.ker f).toAddSubgroup
  let eLinear : Q ≃ₗ[A] M := f.quotKerEquivOfSurjective hf
  let e : Q ≃L[A] M :=
    { eLinear with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap eLinear.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap eLinear.symm.toLinearMap }
  have he : IsUniformEmbedding (e : Q → M) :=
    AddMonoidHom.isUniformEmbedding_of_isEmbedding e.toHomeomorph.isEmbedding
  exact (completeSpace_congr (e := e.toLinearEquiv.toEquiv) he).mp inferInstance

end TauCeti.Huber

end
