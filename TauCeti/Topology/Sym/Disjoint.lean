/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Data.Sym.Disjoint
public import TauCeti.Topology.Sym

/-!
# The symmetric power is locally a product

The `n`-th symmetric power of a space is not a product, but it becomes one over a decomposition of
the points into disjoint open pieces. Two statements say this:

* concatenation `TauCeti.Sym.appendSubtype` of an unordered `n`-tuple of points of an open set `U`
  and an unordered `m`-tuple of points of a disjoint open set `V` is an **open embedding**
  `Sym U n × Sym V m ↪ Sym α (n + m)`, whose range is described in
  `TauCeti.Sym.mem_range_appendSubtype`;
* the ordered tuples with `i`-th point in `U i`, for a pairwise disjoint family of open sets, embed
  openly as unordered tuples: near a tuple of `n` *distinct* points the symmetric power is the
  product `U 1 × ⋯ × U n`.

Both come from the same two facts about `TauCeti.Sym.ofFn`: it is an open quotient map, so a map
out of a symmetric power is continuous, or open, exactly when its composite with `ofFn` is; and
`Fin.appendHomeomorph` identifies pairs of ordered tuples with ordered tuples.

Iterating the first statement over the distinct points of a tuple, with the multiplicities as the
degrees, is how the symmetric power of a surface is charted: a neighbourhood of a tuple with
distinct points `z₁, …, z_k` of multiplicities `n₁, …, n_k` is a product of the symmetric powers
`Sym^{n_j}` of disjoint coordinate discs, each of which is affine space by the elementary
symmetric chart `TauCeti.Sym.coeffHomeomorph`. Lane F4.1 of the analytic Heegaard Floer roadmap
needs exactly this to give `Sym^g(Σ)` its complex structure, after Ozsváth--Szabó
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206), §2.1); the charts themselves are in
`TauCeti/Analysis/Polynomial/SymmetricPower.lean`.

## Main declarations

* `TauCeti.Sym.isOpenEmbedding_appendSubtype`: concatenation along a disjoint pair of open sets is
  an open embedding of the product of the two symmetric powers.
* `TauCeti.Sym.isOpenEmbedding_ofFn_val`: for a pairwise disjoint family of open sets, an ordered
  tuple with one point in each embeds openly as an unordered tuple.
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
  rw [← (isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).continuous_comp_iff,
    appendSubtype_comp_ofFn]
  exact continuous_ofFn.comp ((Fin.continuous_append n m).comp (by fun_prop))

/-- Concatenating an unordered tuple of points of an open set `U` and one of points of an open set
`V` is an open map: `Fin.append` is a homeomorphism on ordered tuples, and the quotient map onto a
symmetric power is open. -/
theorem isOpenMap_appendSubtype (hU : IsOpen U) (hV : IsOpen V) :
    IsOpenMap (appendSubtype U V n m) := by
  have hcoe : ⇑(Fin.appendHomeomorph (X := α) n m) =
      fun q : (Fin n → α) × (Fin m → α) => Fin.append q.1 q.2 := by
    funext q i
    simp
  rw [(isOpenQuotientMap_ofFn.prodMap isOpenQuotientMap_ofFn).isOpenMap_iff,
    appendSubtype_comp_ofFn, ← hcoe]
  refine isOpenMap_ofFn.comp ((Fin.appendHomeomorph n m).isOpenMap.comp (IsOpenMap.prodMap ?_ ?_))
  · exact (IsOpenEmbedding.piMap fun _ => hU.isOpenEmbedding_subtypeVal).isOpenMap
  · exact (IsOpenEmbedding.piMap fun _ => hV.isOpenEmbedding_subtypeVal).isOpenMap

/-- **The symmetric power is locally a product.** For disjoint open sets `U` and `V`, concatenation
identifies `Sym U n × Sym V m` with an open subspace of `Sym α (n + m)`, namely the unordered
tuples supported in `U ∪ V` with exactly `n` of their points in `U`
(`TauCeti.Sym.mem_range_appendSubtype`). -/
theorem isOpenEmbedding_appendSubtype (hU : IsOpen U) (hV : IsOpen V) (h : Disjoint U V) :
    IsOpenEmbedding (appendSubtype U V n m) :=
  .of_continuous_injective_isOpenMap continuous_appendSubtype (appendSubtype_injective h)
    (isOpenMap_appendSubtype hU hV)

/-! ### Tuples with one point in each of pairwise disjoint open sets -/

/-- **Away from the diagonal the symmetric power is a product.** For a pairwise disjoint family of
open sets `U i`, an ordered tuple with `i`-th point in `U i` embeds openly, as an unordered tuple,
into `Sym α n`: a neighbourhood of an unordered tuple of `n` distinct points is the product of `n`
neighbourhoods of those points. -/
theorem isOpenEmbedding_ofFn_val {U : Fin n → Set α} (hU : ∀ i, IsOpen (U i))
    (h : Pairwise (Function.onFun Disjoint U)) :
    IsOpenEmbedding fun f : (i : Fin n) → U i => ofFn fun i => (f i : α) := by
  refine .of_continuous_injective_isOpenMap ?_ (ofFn_val_injective h) ?_
  · exact continuous_ofFn.comp (continuous_pi fun i => (continuous_apply i).subtype_val)
  · exact isOpenMap_ofFn.comp
      (IsOpenEmbedding.piMap fun i => (hU i).isOpenEmbedding_subtypeVal).isOpenMap

end Sym

end TauCeti
