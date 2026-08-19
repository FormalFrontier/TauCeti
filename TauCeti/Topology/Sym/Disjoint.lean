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
# The symmetric power is locally a product

The `n`-th symmetric power of a space is not a product, but it becomes one over a decomposition of
the points into disjoint open pieces. Two statements say this:

* concatenation `TauCeti.Sym.appendSubtype` of an unordered `n`-tuple of points of an open set `U`
  and an unordered `m`-tuple of points of a disjoint open set `V` is an **open embedding**
  `Sym U n × Sym V m ↪ Sym α (n + m)`, whose range is described in
  `TauCeti.Sym.mem_range_appendSubtype`;
* given open embeddings with pairwise disjoint ranges, ordered tuples mapped pointwise through
  those embeddings embed openly as unordered tuples. In particular, given pairwise disjoint open
  neighbourhoods `U i` of `n` distinct points, their product is an open subspace of `Sym α n`;
  obtaining such neighbourhoods in a Hausdorff space is a separate step.

The first statement combines the continuous and open concatenation map on symmetric powers with
functoriality for open embeddings; those general facts come from the open quotient map
`TauCeti.Sym.ofFn` and `Fin.appendHomeomorph`. The second comes from `ofFn` being continuous and
open together with `IsOpenEmbedding.piMap`.

Iterating the first statement over the distinct points of a tuple, with the multiplicities as the
degrees, is how the symmetric power of a surface is charted: a neighbourhood of a tuple with
distinct points `z₁, …, z_k` of multiplicities `n₁, …, n_k` is a product of the symmetric powers
`Sym^{n_j}` of disjoint coordinate discs, each of which is an open subspace of affine space by
`TauCeti.Sym.isOpenEmbedding_coeffEquiv_comp_map`. Lane F4.1 of the analytic Heegaard Floer
roadmap needs exactly this to give `Sym^g(Σ)` its complex structure, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1); the charts themselves are in
`TauCeti/Analysis/Polynomial/SymmetricPower.lean`.

## Main declarations

* `TauCeti.Sym.isOpenEmbedding_appendSubtype`: concatenation along a disjoint pair of open sets is
  an open embedding of the product of the two symmetric powers.
* `TauCeti.Sym.isOpenEmbedding_ofFn_map`: open embeddings with pairwise disjoint ranges induce an
  open embedding from their product into the symmetric power.
-/

public section

open Topology

namespace TauCeti

namespace Sym

variable {α : Type*} [TopologicalSpace α] {m n : ℕ} {U V : Set α}

/-! ### Concatenation along a disjoint pair of open sets -/

/-- Concatenating an unordered tuple of points of `U` and one of points of `V` is continuous. -/
@[continuity, fun_prop]
theorem continuous_appendSubtype : Continuous (appendSubtype U V n m) := by
  rw [appendSubtype_eq_append_map]
  exact continuous_append.comp
    ((continuous_map continuous_subtype_val).prodMap (continuous_map continuous_subtype_val))

/-- For open sets `U` and `V`, concatenating their symmetric-power points is an open map. -/
theorem isOpenMap_appendSubtype (hU : IsOpen U) (hV : IsOpen V) :
    IsOpenMap (appendSubtype U V n m) := by
  rw [appendSubtype_eq_append_map]
  exact isOpenMap_append.comp
    ((isOpenMap_map hU.isOpenMap_subtype_val).prodMap (isOpenMap_map hV.isOpenMap_subtype_val))

/-- **The symmetric power is locally a product.** For disjoint open sets `U` and `V`, concatenation
identifies `Sym U n × Sym V m` with an open subspace of `Sym α (n + m)`, namely the unordered
tuples supported in `U ∪ V` with exactly `n` of their points in `U`
(`TauCeti.Sym.mem_range_appendSubtype`). -/
theorem isOpenEmbedding_appendSubtype (hU : IsOpen U) (hV : IsOpen V) (h : Disjoint U V) :
    IsOpenEmbedding (appendSubtype U V n m) :=
  .of_continuous_injective_isOpenMap continuous_appendSubtype (appendSubtype_injective h)
    (isOpenMap_appendSubtype hU hV)

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
