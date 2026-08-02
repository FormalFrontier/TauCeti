/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Montel's theorem: local boundedness is relative compactness

Layer **L1 (normal families / Montel)** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`) states its milestone as

> locally bounded ⇒ precompact for `TendstoLocallyUniformlyOn`,

and `Conformal/Montel/Basic.lean` records the *selection* consequence: every sequence drawn from a
locally bounded family of holomorphic functions has a locally uniformly convergent subsequence.
This file isolates the compactness statement that selection consequence rests on, in the space
where "precompact" literally means precompact — the space `C(↥Ω, ℂ)` of continuous maps on the
domain with its compact-open topology, whose convergence *is* locally uniform convergence — and
shows that local boundedness is not merely sufficient for it but equivalent to it.

## The two directions

A family `F : ι → ℂ → ℂ` of functions holomorphic on an open `Ω` restricts to a family
`f : ι → C(↥Ω, ℂ)`; the theorems below take that restriction as a hypothesis
`⇑(f i) = Ω.domRestrict (F i)` rather than fixing one bundling, so that a caller which already
carries such an `f` may use them directly. The hypothesis constrains nothing: a caller holding
`hF : ∀ i, ContinuousOn (F i) Ω` and no `f` of its own takes
`fun i => ⟨Ω.domRestrict (F i), (hF i).domRestrict⟩`, for which it holds by `rfl`.

*Locally bounded ⇒ relatively compact* is Mathlib's compact-open Arzelà–Ascoli framework. The
family sits inside the uniform-on-compacts function space as a closed subspace
(`ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact` together with
`UniformOnFun.isClosed_setOfPred_continuous`), so
`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` applies: equicontinuity on each compact is
`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, which is Cauchy's estimate, and pointwise relative
compactness is local boundedness at a single point. This is the direction with analytic content —
holomorphy enters only through the Cauchy estimate behind the equicontinuity.

*Relatively compact ⇒ locally bounded* is a soft argument and needs no holomorphy at all, nor even
openness of `Ω`: local compactness of the subtype `↥Ω` is all it uses. On a compact `K ⊆ Ω` the
product `closure (range f) ×ˢ (Subtype.val ⁻¹' K)` is compact, local compactness of `↥Ω` makes
evaluation `C(↥Ω, ℂ) × ↥Ω → ℂ` continuous in both variables at once, and a continuous real function
on a compact set is bounded. The bound obtained is uniform in the index, which is exactly
`TauCeti.IsLocallyBoundedOn`.

Together they give `TauCeti.isCompact_closure_range_iff_isLocallyBoundedOn`: for a family of
holomorphic functions on an open set, relative compactness in `C(↥Ω, ℂ)` and local boundedness are
the same condition.

## Main results

* `TauCeti.isCompact_closure_range_of_isLocallyBoundedOn` — a locally bounded family of
  holomorphic functions on an open set is relatively compact in `C(↥Ω, ℂ)`.
* `TauCeti.isLocallyBoundedOn_of_isCompact_closure_range` — the converse, for any family of
  maps on a set whose subtype is locally compact.
* `TauCeti.isCompact_closure_range_iff_isLocallyBoundedOn` — the two are equivalent.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
the in-progress human-curated Riemann-mapping-theorem effort, which proves a Montel
equicontinuity statement internally as a private lemma. **Like `Conformal/Montel/Basic.lean`, this
file is therefore a temporary shim**: once the corresponding Mathlib results land, these statements
should be backed by them — or deleted and their consumers refactored — rather than maintained as an
independent re-proof. What Tau Ceti adds at L1 is named, discoverable API, not first proof.

This is the **analytic** normal-families theorem; it is deliberately not routed through Mathlib's
`Analysis/LocallyConvex/Montel.lean` (`MontelSpace`), which is an unrelated notion.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Metric Filter Topology Set

namespace TauCeti

variable {ι : Type*} {Ω : Set ℂ} {F : ι → ℂ → ℂ} {f : ι → C(Ω, ℂ)}

-- `C(X, Y)` sits inside the uniform-on-compacts function space as a closed subspace: the
-- coercion is a uniform embedding, and its range is the continuous maps, which is closed when
-- the topology of `X` is coherent with its compacts. This is the shape Arzelà–Ascoli asks for.
private theorem isClosedEmbedding_ofFun_comp_coe {X Y : Type*} [TopologicalSpace X]
    [CompactlyCoherentSpace X] [UniformSpace Y] :
    IsClosedEmbedding (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) := by
  refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
  -- The `rfl` below is just `ContinuousMap.toUniformOnFunIsCompact` unfolded (Mathlib
  -- `Topology/UniformSpace/CompactConvergence.lean`): Arzelà–Ascoli asks for the map in the
  -- `UniformOnFun.ofFun 𝔖 ∘ F` form, while `range_toUniformOnFunIsCompact` is stated for the
  -- packaged name, so this bridges the two.
  rw [show (⇑(UniformOnFun.ofFun {K : Set X | IsCompact K}) ∘
      (DFunLike.coe : C(X, Y) → (X → Y))) = ContinuousMap.toUniformOnFunIsCompact from rfl,
    ContinuousMap.range_toUniformOnFunIsCompact]
  exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith

-- Equicontinuity of a family transfers to its range viewed as a subtype: every element of the
-- range is some member of the family, and equicontinuity is stable under reindexing.
private theorem equicontinuous_subtype_val_range {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {g : ι → C(X, Y)} (h : Equicontinuous fun i => (g i : X → Y)) :
    Equicontinuous ((DFunLike.coe : C(X, Y) → (X → Y)) ∘
      (Subtype.val : ↥(Set.range g) → C(X, Y))) := by
  classical
  choose σ hσ using fun x : ↥(Set.range g) => x.2
  have heq : ((DFunLike.coe : C(X, Y) → (X → Y)) ∘ (Subtype.val : ↥(Set.range g) → C(X, Y)))
      = (fun i => (g i : X → Y)) ∘ σ := funext fun x => by
    rw [Function.comp_apply, Function.comp_apply, hσ x]
  rw [heq]
  exact h.comp σ

/-- **Montel's theorem, relative-compactness form.** A locally bounded family of holomorphic
functions on an open set `Ω ⊆ ℂ` restricts to a relatively compact family in the space
`C(↥Ω, ℂ)` of continuous maps with the compact-open topology.

This is the precompactness the roadmap's L1 milestone asks for; `TauCeti.montel` is the sequential
selection statement extracted from it. The local boundedness hypothesis cannot be dropped: on a
nonempty open `Ω` the holomorphic family `F n z = n` restricts to a closed discrete — hence
non-relatively-compact — family. -/
theorem isCompact_closure_range_of_isLocallyBoundedOn (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hb : IsLocallyBoundedOn F Ω)
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) :
    IsCompact (closure (Set.range f)) := by
  haveI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have heq : Equicontinuous fun i => (f i : Ω → ℂ) := by
    rw [funext hf]
    exact (equicontinuous_restrict_iff F).mpr (hb.equicontinuousOn hΩ hF)
  -- Arzelà–Ascoli in the compact-open topology: equicontinuity comes from Cauchy's estimate and
  -- pointwise relative compactness from local boundedness.
  refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK)
    isClosedEmbedding_ofFun_comp_coe
    (fun K _ => (equicontinuous_subtype_val_range heq).equicontinuousOn K) ?_
  intro K _ x _
  obtain ⟨C, hC⟩ := hb.exists_forall_norm_le x.2
  refine ⟨closedBall 0 C, isCompact_closedBall _ _, fun g hg => ?_⟩
  obtain ⟨i, rfl⟩ := hg
  simpa [hf i, mem_closedBall, dist_zero_right] using hC i

/-- **The converse of Montel's theorem.** A family of functions on a set `Ω ⊆ ℂ` with locally
compact subtype whose restrictions are relatively compact in `C(↥Ω, ℂ)` is locally bounded on `Ω`.

No holomorphy is needed, nor even continuity beyond what the restrictions already carry:
evaluation is continuous in the map and the point together as soon as `↥Ω` is locally compact
(for an open `Ω` the instance is `IsOpen.locallyCompactSpace`), so a continuous real function on
the compact product `closure (Set.range f) ×ˢ (Subtype.val ⁻¹' K)` is bounded — and its bound is
uniform in the index, which is what local boundedness asserts. -/
theorem isLocallyBoundedOn_of_isCompact_closure_range [LocallyCompactSpace Ω]
    (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) (hcpt : IsCompact (closure (Set.range f))) :
    IsLocallyBoundedOn F Ω := by
  refine isLocallyBoundedOn_def.mpr fun K hKΩ hK => ?_
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set Ω) := by
    refine Topology.IsEmbedding.subtypeVal.isCompact_iff.2 ?_
    rwa [Subtype.image_preimage_val, inter_eq_self_of_subset_right hKΩ]
  have hcont : Continuous fun p : C(Ω, ℂ) × Ω => ‖p.1 p.2‖ := continuous_eval.norm
  obtain ⟨C, hC⟩ := ((hcpt.prod hK').image hcont).bddAbove
  refine ⟨C, fun i z hz => ?_⟩
  have hmem : ((f i, (⟨z, hKΩ hz⟩ : Ω)) : C(Ω, ℂ) × Ω) ∈
      closure (Set.range f) ×ˢ (Subtype.val ⁻¹' K : Set Ω) :=
    ⟨subset_closure ⟨i, rfl⟩, hz⟩
  have hle : ‖(f i) (⟨z, hKΩ hz⟩ : Ω)‖ ≤ C := hC (mem_image_of_mem _ hmem)
  rwa [hf i] at hle

/-- **Montel's theorem as an equivalence.** For a family of holomorphic functions on an open set
`Ω ⊆ ℂ`, being locally bounded on `Ω` and being relatively compact in `C(↥Ω, ℂ)` are the same
condition. -/
theorem isCompact_closure_range_iff_isLocallyBoundedOn (hΩ : IsOpen Ω)
    (hF : ∀ i, DifferentiableOn ℂ (F i) Ω) (hf : ∀ i, ⇑(f i) = Ω.domRestrict (F i)) :
    IsCompact (closure (Set.range f)) ↔ IsLocallyBoundedOn F Ω :=
  haveI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  ⟨isLocallyBoundedOn_of_isCompact_closure_range hf,
    fun hb => isCompact_closure_range_of_isLocallyBoundedOn hΩ hF hb hf⟩

end TauCeti
