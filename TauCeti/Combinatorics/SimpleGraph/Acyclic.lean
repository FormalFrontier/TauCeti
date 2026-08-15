/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

/-!
# Paths in acyclic simple graphs

This file records reusable consequences of acyclicity for paths in simple graphs.

## Main results

* `SimpleGraph.IsAcyclic.not_adj_getVert_of_add_one_lt`: nonconsecutive vertices of a path
  in an acyclic graph are not adjacent.
* `SimpleGraph.IsAcyclic.ne_of_adj_start_of_adj_end`: an off-path neighbour of a path's start
  differs from every neighbour of its end.
* `SimpleGraph.IsAcyclic.not_adj_of_adj_start_of_adj_end`: when both lie off the path, such a
  neighbour of the start and a neighbour of the end are not adjacent.
-/

namespace TauCeti

/-- A path in an acyclic graph has no chord: vertices separated by at least one intermediate
vertex cannot be adjacent. -/
theorem _root_.SimpleGraph.IsAcyclic.not_adj_getVert_of_add_one_lt {V : Type*}
    {G : SimpleGraph V} {u v : V}
    (hG : G.IsAcyclic) {p : G.Walk u v} (hp : p.IsPath) {i j : ℕ} (hij : i + 1 < j)
    (hj : j ≤ p.length) : ¬G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hij' : i ≤ j := by omega
  have hmem : p.getVert j ∈ (p.drop i).support := by
    simpa [Nat.add_sub_of_le hij'] using (p.drop i).getVert_mem_support (j - i)
  have heq := hG.eq_snd_of_adj_start (hp.drop i) hadj hmem
  have hsnd : (p.drop i).snd = p.getVert (i + 1) := by simp [SimpleGraph.Walk.snd]
  rw [hsnd] at heq
  have := hp.getVert_injOn (by omega : i + 1 ≤ p.length) hj heq.symm
  omega

/-- **An off-path neighbour of a path's start differs from every neighbour of its end.** In an
acyclic graph, for a path with distinct endpoints. Only the start-side vertex is required to lie
off the path; the end-side one is unconstrained. -/
theorem _root_.SimpleGraph.IsAcyclic.ne_of_adj_start_of_adj_end {V : Type*} {G : SimpleGraph V}
    {u v : V} (hG : G.IsAcyclic) (huv : u ≠ v) {q : G.Walk u v} (hq : q.IsPath)
    {a b : V} (ha : G.Adj u a) (ha' : a ∉ q.support) (hb : G.Adj v b) : a ≠ b := fun hab ↦
  -- `a = b` makes `a` adjacent to the far end `v` of the path `a — u — … — v`, so acyclicity
  -- forces `v` to be that path's second vertex, which is `u`.
  huv <| (SimpleGraph.Walk.snd_cons q ha.symm).symm.trans
    (hG.eq_snd_of_adj_start (hq.cons ha' (h := ha.symm)) (hab ▸ hb).symm
      (SimpleGraph.Walk.end_mem_support _)).symm

/-- **Neighbours of a path's two ends, both lying off the path, are not adjacent.** In an acyclic
graph, no edge joins a vertex adjacent to the start of a path to one adjacent to its end. Here
both are required to lie off the path, unlike in `ne_of_adj_start_of_adj_end`. -/
theorem _root_.SimpleGraph.IsAcyclic.not_adj_of_adj_start_of_adj_end {V : Type*}
    {G : SimpleGraph V} {u v : V} (hG : G.IsAcyclic) {q : G.Walk u v} (hq : q.IsPath)
    {a b : V} (ha : G.Adj u a) (ha' : a ∉ q.support) (hb : G.Adj v b) (hb' : b ∉ q.support) :
    ¬G.Adj a b := by
  intro hadj
  -- The paths `a — u — … — v` and `a — b` leave `a` with adjacent far ends, and `v` misses the
  -- edge `a — b`, so acyclicity puts `b` on the first path; but `b` is neither `a` nor on `q`.
  have hmem := hG.mem_support_of_ne_mem_support_of_adj_of_isPath (hq.cons ha' (h := ha.symm))
    hadj.isPath_toWalk hb (by simp [hb.ne, ne_of_mem_of_not_mem q.end_mem_support ha'])
  simp [hadj.ne', hb'] at hmem

end TauCeti
