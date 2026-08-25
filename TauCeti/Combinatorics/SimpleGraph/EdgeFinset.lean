/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Edges of a graph under an isomorphism and under a disjoint sum

Two ways of moving a finite product indexed by the edges of a graph, both stated so that the
statement itself carries no decidability side conditions:

* along a graph isomorphism `φ : G ≃g H`, where `Sym2.map φ` matches the edges of `G` with those
  of `H`;
* across the disjoint sum `G ⊕g H`, whose edges are the edges of `G` and the edges of `H`, tagged
  by `Sum.inl` and `Sum.inr`.

`SimpleGraph.sum` has no `DecidableRel` instance in Mathlib, so `(G ⊕g H).edgeFinset` is not even
expressible without one; `TauCeti.instDecidableRelSumAdj` supplies it by the four-way case split its
definition makes.  Mathlib's `SimpleGraph.edgeSetSumEquiv` matches the edges of a disjoint sum with
a sum of edge sets, but reindexing a `Finset` product needs the edges of `G` and of `H` *tagged
inside* `Sym2 (V ⊕ W)`, which is what `TauCeti.edgeSet_sum` records.

## Main results

* `TauCeti.instDecidableRelSumAdj` — adjacency in a disjoint sum is decidable;
* `TauCeti.edgeFinset_iso` and `TauCeti.prod_edgeFinset_iso` — the edges of `H` are the edges of `G`
  read through `Sym2.map φ`, and a product over them reindexes;
* `TauCeti.edgeSet_sum`, `TauCeti.edgeFinset_sum` and `TauCeti.card_edgeFinset_sum` — the edges of a
  disjoint sum split into two tagged copies;
* `TauCeti.prod_edgeFinset_sum` — a product over the edges of a disjoint sum factors.
-/

public section

namespace TauCeti

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Adjacency in a disjoint sum of graphs is decidable: `SimpleGraph.sum` splits on which sides its
two arguments lie, and vertices on opposite sides are never adjacent. -/
instance instDecidableRelSumAdj (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl u, .inl v => ‹DecidableRel G.Adj› u v
  | .inr u, .inr v => ‹DecidableRel H.Adj› u v
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

/-- The disjoint sum of two graphs is the join of their images under the two inclusions of a sum
type. -/
theorem sum_eq_sup_map (G : SimpleGraph V) (H : SimpleGraph W) :
    G ⊕g H = G.map Function.Embedding.inl ⊔ H.map Function.Embedding.inr := by
  ext a b
  cases a <;> cases b <;> simp

/-- The edges of a disjoint sum are the edges of the two summands, tagged by the inclusions. -/
theorem edgeSet_sum (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).edgeSet = Sym2.map Sum.inl '' G.edgeSet ∪ Sym2.map Sum.inr '' H.edgeSet := by
  rw [sum_eq_sup_map, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map, SimpleGraph.edgeSet_map]
  rfl

variable [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- An edge of `G` tagged by `Sum.inl` is never an edge of `H` tagged by `Sum.inr`. -/
theorem disjoint_edgeFinset_sum :
    Disjoint (G.edgeFinset.map (Function.Embedding.inl (β := W)).sym2Map)
      (H.edgeFinset.map (Function.Embedding.inr (α := V)).sym2Map) := by
  classical
  rw [Finset.disjoint_left]
  rintro d hd₁ hd₂
  simp only [Finset.mem_map, Function.Embedding.sym2Map] at hd₁ hd₂
  obtain ⟨c₁, -, h₁⟩ := hd₁
  obtain ⟨c₂, -, h₂⟩ := hd₂
  induction c₁ using Sym2.ind with
  | _ a b =>
    induction c₂ using Sym2.ind with
    | _ a' b' =>
      rw [← h₂] at h₁
      simp at h₁

/-- The `Finset` form of `TauCeti.edgeSet_sum`. -/
theorem edgeFinset_sum [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G ⊕g H).edgeFinset = G.edgeFinset.map (Function.Embedding.inl).sym2Map
      ∪ H.edgeFinset.map (Function.Embedding.inr).sym2Map := by
  rw [← Finset.coe_inj]
  push_cast
  exact edgeSet_sum G H

/-- A disjoint sum has as many edges as its two summands together. -/
theorem card_edgeFinset_sum :
    (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  classical
  rw [edgeFinset_sum, Finset.card_union_of_disjoint disjoint_edgeFinset_sum, Finset.card_map,
    Finset.card_map]

/-- A finite product indexed by the edges of a disjoint sum factors as the product over the edges
of the left summand times the product over the edges of the right one. -/
theorem prod_edgeFinset_sum {M : Type*} [CommMonoid M] (g : Sym2 (V ⊕ W) → M) :
    ∏ d ∈ (G ⊕g H).edgeFinset, g d
      = (∏ c ∈ G.edgeFinset, g (Sym2.map Sum.inl c))
        * ∏ c ∈ H.edgeFinset, g (Sym2.map Sum.inr c) := by
  classical
  rw [edgeFinset_sum, Finset.prod_union disjoint_edgeFinset_sum, Finset.prod_map, Finset.prod_map]
  rfl

/-- The edges of `H` are exactly the edges of `G` read through an isomorphism `φ : G ≃g H`.

The two graphs have equally many edges (`SimpleGraph.Iso.card_edgeFinset_eq`), so the inclusion
of one side into the other already forces equality. -/
theorem edgeFinset_iso (φ : G ≃g H) :
    H.edgeFinset = G.edgeFinset.map ⟨Sym2.map φ, Sym2.map.injective φ.injective⟩ := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro d hd
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    induction c using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset] at hc ⊢
      simpa using φ.map_adj_iff.2 hc
  · rw [Finset.card_map, φ.card_edgeFinset_eq]

/-- A finite product indexed by the edges of `H` is the product, over the edges of `G`, of the same
function read through an isomorphism `φ : G ≃g H`. -/
theorem prod_edgeFinset_iso {M : Type*} [CommMonoid M] (φ : G ≃g H) (g : Sym2 W → M) :
    ∏ d ∈ H.edgeFinset, g d = ∏ c ∈ G.edgeFinset, g (Sym2.map φ c) := by
  rw [edgeFinset_iso φ, Finset.prod_map]
  rfl

end TauCeti
