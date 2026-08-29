/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Negation and topological nilpotence

Mathlib closes `IsTopologicallyNilpotent` under the operations that a topology on the ring makes
available — `zero`, `add`, `mul_left`, `mul_right`, `map` — but not under negation. This file adds
that, at the hypotheses the statement needs: a `MonoidWithZero` with a distributive negation, and
continuity of negation.

No uniformity, nonarchimedean neighbourhood basis or commutativity is involved. `(-a) ^ n` is
`a ^ n` for even `n` and `-(a ^ n)` for odd `n`, and both of those sequences tend to `0` as soon as
negation is continuous, so every neighbourhood of `0` eventually contains `(-a) ^ n` whichever
parity `n` has.

## Main results

* `IsTopologicallyNilpotent.neg` : the negation of a topologically nilpotent element is
  topologically nilpotent.
* `isTopologicallyNilpotent_neg` : the same fact as a `simp` iff, mirroring `isPowerBounded_neg`.
* `eventually_mul_pow_mem_of_isTopologicallyNilpotent`, and its `.exists` form: a topologically
  nilpotent element absorbs any fixed element into any open subring.

## Provenance

The statement is AINTLIB's `IsTopologicallyNilpotent.neg`, branch `dev/adic-spaces`, commit
`37bbdaeb`, Apache-2.0, Chris Birkbeck, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
There it sits inside the geometric-series development over a complete nonarchimedean uniform
commutative ring, and the sign on the odd powers is absorbed by an open subgroup. Only the
statement is followed here: the hypotheses are weakened to the ones the result needs, and the
open-subgroup step is replaced by the two-sequence argument above, which needs no nonarchimedean
basis. The iff form has no counterpart in the source.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
-/

open Filter Topology

public section

variable {R : Type*} [MonoidWithZero R] [HasDistribNeg R] [TopologicalSpace R] [ContinuousNeg R]

/-- **The negation of a topologically nilpotent element is topologically nilpotent.** -/
theorem IsTopologicallyNilpotent.neg {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (-a) := by
  -- `ha` is restated as a `Tendsto` before any dot notation: `ha.neg` would resolve to this very
  -- lemma rather than to `Filter.Tendsto.neg`.
  have ht : Tendsto (fun n : ℕ ↦ a ^ n) atTop (𝓝 0) := ha
  have hneg : Tendsto (fun n : ℕ ↦ -(a ^ n)) atTop (𝓝 0) := by simpa using ht.neg
  unfold IsTopologicallyNilpotent
  rw [tendsto_def] at ht hneg ⊢
  intro U hU
  filter_upwards [ht U hU, hneg U hU] with n h1 h2
  rcases Nat.even_or_odd n with he | ho
  · simpa [he.neg_pow] using h1
  · simpa [ho.neg_pow] using h2

/-- Topological nilpotence is invariant under negation. -/
@[simp]
theorem isTopologicallyNilpotent_neg {a : R} :
    IsTopologicallyNilpotent (-a) ↔ IsTopologicallyNilpotent a :=
  ⟨fun h ↦ by simpa using h.neg, IsTopologicallyNilpotent.neg⟩


section Absorb

variable {A : Type*} [Ring A] [TopologicalSpace A] [ContinuousMul A]

/-- **A topologically nilpotent element absorbs any element into any open subring.** For `s`
topologically nilpotent and `B` open, `a * s ^ n` lies in `B` for all large `n`.

Multiplication by `a` is continuous, so `B` pulls back to a neighbourhood of `0`, and the powers
of `s` converge to `0`. Neither commutativity nor continuity of addition is used — only
`ContinuousMul` — and no Huber structure enters, which is why this sits here rather than beside
the ring-of-definition form it generalises,
`TauCeti.Huber.PairOfDefinition.exists_pow_idealOfDefinition_mul_mem`. -/
theorem eventually_mul_pow_mem_of_isTopologicallyNilpotent {s : A}
    (hs : IsTopologicallyNilpotent s) {B : Subring A} (hB : IsOpen (B : Set A)) (a : A) :
    ∀ᶠ n : ℕ in atTop, a * s ^ n ∈ B :=
  hs ((hB.preimage (continuous_const_mul a)).mem_nhds (by simp))

/-- The existential form of `eventually_mul_pow_mem_of_isTopologicallyNilpotent`: some power of a
topologically nilpotent element carries `a` into an open subring. -/
theorem exists_mul_pow_mem_of_isTopologicallyNilpotent {s : A}
    (hs : IsTopologicallyNilpotent s) {B : Subring A} (hB : IsOpen (B : Set A)) (a : A) :
    ∃ n : ℕ, a * s ^ n ∈ B :=
  (eventually_mul_pow_mem_of_isTopologicallyNilpotent hs hB a).exists

end Absorb

end
