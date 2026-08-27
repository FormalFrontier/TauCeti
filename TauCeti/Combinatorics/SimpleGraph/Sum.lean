/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Decidable adjacency for a disjoint sum of graphs

`SimpleGraph.sum` has no `DecidableRel` instance in Mathlib. Consequently, even when adjacency in
both summands is decidable, `(G ⊕g H).edgeFinset` is not expressible without supplying an
instance. `TauCeti.instDecidableRelSumAdj` supplies it by the four-way case split in the definition
of `SimpleGraph.sum`.

## Main results

* `TauCeti.instDecidableRelSumAdj` — adjacency in a disjoint sum is decidable;
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

end TauCeti
