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

end TauCeti
