/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.NormalFamilies
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Montel's selection theorem

A locally bounded family of holomorphic functions on an open set `Ω ⊆ ℂ` is a normal family: every
sequence drawn from it has a subsequence converging locally uniformly on `Ω`, and the limit is
again holomorphic. This completes layer **L1 (normal families / Montel)** of the conformal-mapping
roadmap, and is the compactness engine the Riemann mapping theorem runs on.

The equicontinuity half is already available in `Conformal/NormalFamilies.lean`
(`TauCeti.IsLocallyBoundedOn.equicontinuousOn`, from Cauchy's estimate); what is added here is the
selection argument that turns it into a convergent subsequence.

The proof is Mathlib's compact-open Arzelà–Ascoli framework, applied in `C(Ω, ℂ)`. The family
restricts to a set of continuous maps there;
`ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact` together with
`UniformOnFun.isClosed_setOf_continuous` exhibits `C(Ω, ℂ)` as a closed subspace of the
uniform-on-compacts function space, so
`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` applies: equicontinuity on each compact comes
from `IsLocallyBoundedOn.equicontinuousOn`, and pointwise relative compactness from local
boundedness. The closure of the family is then compact, `Ω` being locally compact makes `C(Ω, ℂ)`
first countable, and `IsCompact.tendsto_subseq` extracts a convergent subsequence. Finally
`ContinuousMap.tendsto_iff_tendstoLocallyUniformly` turns compact-open convergence into locally
uniform convergence, and `TendstoLocallyUniformlyOn.differentiableOn` gives holomorphy of the limit.

No compact exhaustion or diagonal argument is needed: Mathlib's framework subsumes both.

## Main results

* `TauCeti.montel` — a locally bounded family of holomorphic functions on an open set has a
  locally uniformly convergent subsequence, with holomorphic limit.

## Coordination with upstream Mathlib

Per the *Coordination with upstream Mathlib* section of `ConformalMapping/README.md`, L0–L3
material overlaps [mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505),
which proves a Montel equicontinuity statement internally as a private lemma. **This file is
therefore a temporary shim**: once the corresponding Mathlib results land, this statement should be
backed by them — or deleted and its consumers refactored — rather than maintained as an independent
re-proof. What Tau Ceti adds at L1 is named, discoverable API, not first proof.

Note this is the **analytic** normal-families theorem; it is deliberately not routed through
Mathlib's `Analysis/LocallyConvex/Montel.lean` (`MontelSpace`), which is an unrelated notion.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 5 §5.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. VII §2.
-/

public section

open Complex Metric Filter Topology Set BoundedContinuousFunction

namespace TauCeti

variable {Ω : Set ℂ} {F : ℕ → ℂ → ℂ}

/-- **Montel's selection theorem.** A locally bounded family of holomorphic functions on an open
set `Ω ⊆ ℂ` is normal: every sequence from it has a subsequence converging locally uniformly on
`Ω`, and the limit is holomorphic.

The local boundedness hypothesis cannot be dropped: on any *nonempty* open `Ω`, the holomorphic
family `F n z = n` has no locally uniformly convergent subsequence. (On `Ω = ∅` the conclusion is
vacuous, so nonemptiness is needed for the counterexample.) -/
theorem montel (hΩ : IsOpen Ω) (hF : ∀ n, DifferentiableOn ℂ (F n) Ω)
    (hb : IsLocallyBoundedOn F Ω) :
    ∃ (φ : ℕ → ℕ) (g : ℂ → ℂ), StrictMono φ ∧ DifferentiableOn ℂ g Ω ∧
      TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop Ω := by
  classical
  haveI : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  set f : ℕ → C(Ω, ℂ) := fun n => ⟨Ω.restrict (F n), ((hF n).continuousOn).restrict⟩ with hfdef
  -- `C(Ω, ℂ)` sits as a closed subspace of the uniform-on-compacts function space
  have hclemb : IsClosedEmbedding (⇑(UniformOnFun.ofFun {K : Set Ω | IsCompact K}) ∘
      (DFunLike.coe : C(Ω, ℂ) → (Ω → ℂ))) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [show (⇑(UniformOnFun.ofFun {K : Set Ω | IsCompact K}) ∘
        (DFunLike.coe : C(Ω, ℂ) → (Ω → ℂ))) = ContinuousMap.toUniformOnFunIsCompact from rfl,
      ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith
  -- Arzelà–Ascoli in the compact-open topology
  have hcpt : IsCompact (closure (Set.range f)) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) hclemb ?_ ?_
    · intro K _
      have hbase : Equicontinuous (fun n => (f n : Ω → ℂ)) :=
        (equicontinuous_restrict_iff F).mpr (hb.equicontinuousOn hΩ hF)
      have hchoice : ∀ x : ↥(Set.range f), ∃ n, f n = (x : C(Ω, ℂ)) := fun x => x.2
      choose σ hσ using hchoice
      have heq : ((DFunLike.coe : C(Ω, ℂ) → (Ω → ℂ)) ∘ (Subtype.val : ↥(Set.range f) → C(Ω, ℂ)))
          = (fun n => (f n : Ω → ℂ)) ∘ σ := by
        funext x
        rw [Function.comp_apply, Function.comp_apply, hσ x]
      rw [heq]
      exact (hbase.comp σ).equicontinuousOn K
    · intro K _ x _
      obtain ⟨C, hC⟩ := isLocallyBoundedOn_def.mp hb {(x : ℂ)}
        (by simp) isCompact_singleton
      refine ⟨closedBall 0 C, isCompact_closedBall _ _, fun i hi => ?_⟩
      obtain ⟨n, rfl⟩ := hi
      simpa [hfdef, mem_closedBall, dist_zero_right] using hC n x.1 rfl
  obtain ⟨a, -, φ, hφ, hconv⟩ := hcpt.tendsto_subseq (x := f) fun n => subset_closure ⟨n, rfl⟩
  -- compact-open convergence is locally uniform convergence
  have hlu : TendstoLocallyUniformly (fun n (x : Ω) => F (φ n) x) (fun x : Ω => a x) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv
  have hlim : ((fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) ∘ (Subtype.val : Ω → ℂ))
      = fun x : Ω => a x := by
    funext x
    simp [x.2]
  have hconvOn : TendstoLocallyUniformlyOn (fun n => F (φ n))
      (fun z => if hz : z ∈ Ω then a ⟨z, hz⟩ else 0) atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe, hlim]
    exact hlu
  exact ⟨φ, _, hφ, hconvOn.differentiableOn (Eventually.of_forall fun n => hF (φ n)) hΩ, hconvOn⟩

end TauCeti
