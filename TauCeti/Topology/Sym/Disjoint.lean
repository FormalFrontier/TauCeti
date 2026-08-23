/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Data.Sym.Disjoint
public import TauCeti.Topology.Sym.Basic

/-!
# Disjoint open embeddings into a symmetric power

Given open embeddings with pairwise disjoint ranges, ordered tuples mapped pointwise through those
embeddings embed openly as unordered tuples. In particular, given pairwise disjoint open
neighbourhoods `U i` of `n` distinct points, their product is an open subspace of `Sym α n`;
obtaining such neighbourhoods in a Hausdorff space is a separate step. The proof comes from
`TauCeti.Sym.ofFn` being continuous and open together with `IsOpenEmbedding.piMap`.

Splitting over the distinct points of a tuple, with the multiplicities as the degrees, is how the
symmetric power of a surface is charted: a neighbourhood of a tuple with
distinct points `z₁, …, z_k` of multiplicities `n₁, …, n_k` is a product of the symmetric powers
`Sym^{n_j}` of disjoint coordinate discs, each of which is an open subspace of affine space by
`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`. Lane F4.1 of the analytic Heegaard Floer
roadmap needs exactly this to give `Sym^g(Σ)` its complex structure, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1). The coefficient homeomorphism
is in `TauCeti/Analysis/Polynomial/SymmetricPower.lean`, while the charts and charted structure are
in `TauCeti/Geometry/Manifold/SymmetricPower.lean`. Family-level concatenation along disjoint open
sets, and the Hausdorff separation producing the family that a given tuple needs, are in
`TauCeti/Topology/Sym/Family.lean`.

## Main declaration

* `TauCeti.Sym.isOpenEmbedding_ofFn_map`: open embeddings with pairwise disjoint ranges induce an
  open embedding from their product into the symmetric power.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {n : ℕ}

/-! ### Tuples mapped into pairwise disjoint open ranges -/

/-- **Away from the diagonal the symmetric power is a product.** Open embeddings with pairwise
disjoint ranges induce an open embedding from their product into the symmetric power. Applied to
subtype inclusions, this says conditionally that given pairwise disjoint open neighbourhoods `U i`
of `n` distinct points, their product is an open subspace of `Sym α n`; constructing such a family
in a Hausdorff space is a separate step. -/
theorem isOpenEmbedding_ofFn_map {X : Fin n → Type*} [∀ i, TopologicalSpace (X i)]
    (f : ∀ i, X i → α) (hf : ∀ i, IsOpenEmbedding (f i))
    (h : Pairwise (Function.onFun Disjoint fun i => Set.range (f i))) :
    IsOpenEmbedding fun x : ∀ i, X i => ofFn fun i => f i (x i) := by
  refine .of_continuous_injective_isOpenMap ?_
    (ofFn_map_injective f (fun i => (hf i).injective) h) ?_
  · exact continuous_ofFn.comp (Continuous.piMap fun i => (hf i).continuous)
  · exact isOpenMap_ofFn.comp (IsOpenEmbedding.piMap hf).isOpenMap

end Sym

end TauCeti
