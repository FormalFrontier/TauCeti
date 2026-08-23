/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.OpenMapping.Basic

/-!
# The approximating sequence of Henkel's open mapping theorem

`TauCeti/Topology/Algebra/OpenMapping/Basic.lean` proves one step of Henkel's approximation: a
point in
`closure (f '' U)` is brought inside `closure (f '' V)` by subtracting the image of some `x ∈ U`.
Iterating that step down a sequence of sets produces a sequence of approximants whose residuals
shrink, and this file builds it.

Nothing here converges anything: the sequence exists in any topological additive group, with no
completeness and no first countability. Summing it — which is what finally removes the closure
from `f '' U` — is a separate step, and the two hypotheses enter there separately:
completeness sums the resulting null sequence, while countable generation of `𝓝 0` is what
produces the sequence of subgroups to sum along. `TauCeti.mem_image_of_mem_closure_image` takes
that sequence as an explicit `HasAntitoneBasis` hypothesis rather than synthesising it, so it
assumes completeness but no first-countability instance.

## Main results

* `TauCeti.exists_seq_mem_and_sub_sum_mem`: the approximating sequence, with its partial sums
  driving the residual into `closure (f '' V (n + 1))` at every stage.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647).
-/

public section

open Filter Topology

namespace TauCeti

variable {M N : Type*} [AddCommMonoid M] [AddGroup N] [TopologicalSpace N] [ContinuousSub N]

/-- **Henkel's approximating sequence.** If each `closure (f '' V (n + 1))` is a neighbourhood of
zero and `y` lies in `closure (f '' V 0)`, there are approximants `x n ∈ V n` whose partial sums
drive the residual down the sequence: `y - f (x 0 + ⋯ + x n)` lies in `closure (f '' V (n + 1))`.

No completeness or first countability is used: those are what let the sequence be *summed*, which
is what finally removes the closure from `f '' U`, and neither is needed to obtain the
approximants. -/
theorem exists_seq_mem_and_sub_sum_mem {F : Type*} [FunLike F M N] [AddHomClass F M N]
    (f : F) (V : ℕ → Set M) (hV : ∀ n, closure (f '' V (n + 1)) ∈ 𝓝 (0 : N)) {y : N}
    (hy : y ∈ closure (f '' V 0)) :
    ∃ x : ℕ → M, (∀ n, x n ∈ V n) ∧
      ∀ n, y - f (∑ i ∈ Finset.range (n + 1), x i) ∈ closure (f '' V (n + 1)) := by
  classical
  -- One application of choice, packaging the approximant with both of its properties.
  choose! x hxV hxres using fun (n : ℕ) (r : {z : N // z ∈ closure (f '' V n)}) ↦
    exists_mem_and_sub_mem_closure_image f r.property (hV n)
  -- The recursion carries the residual, whose type depends on the stage.
  let state : ∀ n, {z : N // z ∈ closure (f '' V n)} :=
    fun n ↦ Nat.rec (motive := fun n ↦ {z : N // z ∈ closure (f '' V n)}) ⟨y, hy⟩
      (fun m r ↦ ⟨r.1 - f (x m r), hxres m r⟩) n
  have state_succ : ∀ m, (state (m + 1)).1 = (state m).1 - f (x m (state m)) := fun _ ↦ rfl
  refine ⟨fun n ↦ x n (state n), fun n ↦ hxV n (state n), fun n ↦ ?_⟩
  -- The residual after `n + 1` steps is `y` minus the image of the `n`-th partial sum.
  have key : ∀ m, (state (m + 1)).1
      = y - f (∑ i ∈ Finset.range (m + 1), x i (state i)) := by
    intro m
    induction m with
    | zero => simp [state]
    | succ p ih =>
      -- `a - b - c = a - (b + c)` needs `b` and `c` to commute, which they do here: they are
      -- images of elements of `M`, where addition is commutative.
      have hsub : ∀ a b c : N, b + c = c + b → a - b - c = a - (b + c) := by
        intro a b c hbc
        have hneg : -b + -c = -(b + c) := by rw [← neg_add_rev, hbc]
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, add_assoc, hneg]
      rw [state_succ, ih]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [map_add, hsub _ _ _ (by rw [← map_add, ← map_add, add_comm])]
  exact key n ▸ (state (n + 1)).property

end TauCeti

end
