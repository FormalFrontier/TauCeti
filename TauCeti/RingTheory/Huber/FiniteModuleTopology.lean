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

Together with `TauCeti.Huber.IsTateRing.isModuleTopology`, these results give the existence and
uniqueness asserted by Proposition 6.18(1), among the complete Hausdorff first-countable
nonarchimedean topological module structures occurring in the open-mapping theorem. The topology
is kept as the explicit expression `moduleTopology A M` in the statements: these are theorem
constructors for local instances, rather than global instances whose heads would hide the
topology on `M` from typeclass search.

## Main results

* `TauCeti.Huber.IsTateRing.t2Space_moduleTopology`: the canonical topology is Hausdorff.
* `TauCeti.Huber.IsHuberRing.firstCountableTopology_moduleTopology`: the canonical topology is
  first countable.
* `TauCeti.Huber.IsHuberRing.nonarchimedeanAddGroup_moduleTopology`: the canonical additive group
  is nonarchimedean.
* `TauCeti.Huber.IsHuberRing.completeSpace_moduleTopology`: its canonical right uniformity is
  complete.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 6.18(1).
-/

public section

open Filter Topology
open scoped Uniformity

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsTopologicalRing A]
  {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The module topology on a finite module over a Huber ring is first countable**, when the ring
has its compatible uniform additive-group structure. A finite spanning family gives an open
quotient `Aⁿ → M`; the image of a countably generated neighbourhood filter is countably
generated. -/
theorem IsHuberRing.firstCountableTopology_moduleTopology [IsUniformAddGroup A] [IsHuberRing A] :
    @FirstCountableTopology M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  have _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let f : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A g
  have hf : Function.Surjective f :=
    span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := hf y
  rw [← hquot.map_nhds_eq x]
  infer_instance

/-- **The module topology on a finite module over a complete noetherian Tate ring is
Hausdorff.** For a finite free presentation `f : Aⁿ → M`, equality of two images is equivalent to
their difference lying in `ker f`. This kernel is closed by noetherianity, so the equivalence
relation of the open quotient is closed. -/
theorem IsTateRing.t2Space_moduleTopology [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
    [IsTateRing A] [IsNoetherianRing A] : @T2Space M (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  have _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let f : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A g
  have hf : Function.Surjective f :=
    span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan
  have hquot : IsOpenQuotientMap f := IsModuleTopology.isOpenQuotientMap_of_surjective hf
  rw [t2Space_iff_of_isOpenQuotientMap hquot]
  have hker : IsClosed ((LinearMap.ker f : Submodule A (Fin n → A)) : Set (Fin n → A)) :=
    isClosed_of_isNoetherian (LinearMap.ker f)
  have hsub : Continuous (fun q : (Fin n → A) × (Fin n → A) ↦ q.1 - q.2) :=
    continuous_fst.sub continuous_snd
  convert hker.preimage hsub using 1
  ext q
  change f q.1 = f q.2 ↔ f (q.1 - q.2) = 0
  rw [map_sub, sub_eq_zero]

/-- **The additive group of a finite module with its module topology is nonarchimedean.** It is
the open image of a finite power of the nonarchimedean additive group of the Huber ring. -/
theorem IsHuberRing.nonarchimedeanAddGroup_moduleTopology [IsHuberRing A] :
    @NonarchimedeanAddGroup M _ (moduleTopology A M) := by
  let _ : TopologicalSpace M := moduleTopology A M
  have _ : IsModuleTopology A M := inferInstance
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let f : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A g
  have hf : Function.Surjective f :=
    span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan
  exact NonarchimedeanAddGroup.nonarchimedean_of_isOpenMap f.toAddMonoidHom
    (IsModuleTopology.continuous_of_linearMap f).continuousAt
    (IsModuleTopology.isOpenQuotientMap_of_surjective hf).isOpenMap

/-- **The canonical right uniformity of the module topology on a finite module over a complete
Huber ring is complete.** A finite free presentation identifies `M` homeomorphically with the
quotient of `Aⁿ` by its kernel. Mathlib's additive quotient-completeness theorem makes that
quotient complete; the additive homeomorphism is automatically a uniform equivalence for the
canonical group uniformities. -/
theorem IsHuberRing.completeSpace_moduleTopology [IsUniformAddGroup A] [CompleteSpace A]
    [IsHuberRing A] :
    letI : TopologicalSpace M := moduleTopology A M
    letI : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
    letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    CompleteSpace M := by
  let _ : TopologicalSpace M := moduleTopology A M
  let _ : IsTopologicalAddGroup M := IsModuleTopology.isTopologicalAddGroup A M
  let _ : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have _ : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have _ : (𝓤 A).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨n, g, hspan⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let f : (Fin n → A) →ₗ[A] M := Fintype.linearCombination A g
  have hf : Function.Surjective f :=
    span_range_eq_top_iff_surjective_fintypeLinearCombination A g |>.mp hspan
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
