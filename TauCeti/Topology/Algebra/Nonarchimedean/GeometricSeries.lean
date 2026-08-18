/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import TauCeti.Topology.Algebra.TopologicallyNilpotent

/-!
# The geometric series in a complete nonarchimedean ring

**Wedhorn, *Adic Spaces*, Proposition 5.38.** In a complete nonarchimedean topological ring,
`1 - a` is a unit for every topologically nilpotent `a`.

Nonarchimedean is what makes this cheap. In a general topological ring the geometric series need
not converge just because its terms tend to `0`, but in a complete nonarchimedean additive group
summability is *equivalent* to the terms tending to zero along the cofinite filter
(`NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`, which is where completeness is
consumed) — and for the powers of `a` that is precisely topological nilpotence. Mathlib's
`Summable.one_sub_mul_tsum_pow` and `Summable.tsum_pow_mul_one_sub` then exhibit `∑ aⁿ` as a
two-sided inverse.

What is exported is unit-hood alone; a consumer wanting the inverse should use
`ha.summable_pow.one_sub_mul_tsum_pow` directly.

Mathlib has the analytic counterpart, `isUnit_one_sub_of_norm_lt_one`, which needs a norm; the
nonarchimedean-topological statement is what the Huber theory uses, since a Huber ring carries no
canonical norm.

## Main results

* `IsTopologicallyNilpotent.summable_pow` : the geometric series `∑ aⁿ` is summable.
* `IsTopologicallyNilpotent.isUnit_one_sub` : the unit-hood half of Proposition 5.38.
* `IsTopologicallyNilpotent.isUnit_one_add` : the `1 + a` form, which is the one consumers want.

## Provenance

Ported from AINTLIB's `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`, branch
`dev/adic-spaces`, commit `37bbdaeb`, Apache-2.0, Chris Birkbeck. The proofs are AINTLIB's and rest
entirely on Mathlib primitives. Two deliberate differences from the source: the ring here is only a
`Ring`, the unit being built from both one-sided geometric identities instead of from
commutativity; and the negation-stability lemma the `1 + a` form needs lives in
`TauCeti/Topology/Algebra/TopologicallyNilpotent.lean`, stated at the hypotheses it actually
requires rather than under this file's uniform nonarchimedean block. The `omit` annotations record
which hypotheses each proof uses.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.38.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/GeometricSeries.lean`.
-/

open Filter Topology

public section

variable {A : Type*} [Ring A] [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]

omit [T2Space A] [IsTopologicalRing A] in
/-- **The geometric series of a topologically nilpotent element is summable.** In a complete
nonarchimedean additive group summability is equivalent to the terms tending to zero cofinitely,
which for powers is topological nilpotence. -/
theorem IsTopologicallyNilpotent.summable_pow {a : A} (ha : IsTopologicallyNilpotent a) :
    Summable (a ^ · : ℕ → A) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
  exact ha

/-- **Wedhorn Proposition 5.38**: in a complete nonarchimedean ring, `1 - a` is a unit for every
topologically nilpotent `a`. The inverse is `∑ aⁿ`, which the proof exhibits and
`ha.summable_pow.one_sub_mul_tsum_pow` states. -/
theorem IsTopologicallyNilpotent.isUnit_one_sub {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 - a) :=
  ⟨⟨1 - a, ∑' i : ℕ, a ^ i, ha.summable_pow.one_sub_mul_tsum_pow,
    ha.summable_pow.tsum_pow_mul_one_sub⟩, rfl⟩

/-- **`1 + a` is a unit for topologically nilpotent `a`**, by Proposition 5.38 applied to `-a`.
This is the form consumers use: the units of a complete nonarchimedean ring contain the coset
`1 + A°°`, which is what makes the unit group open. -/
theorem IsTopologicallyNilpotent.isUnit_one_add {a : A} (ha : IsTopologicallyNilpotent a) :
    IsUnit (1 + a) := by
  rw [← sub_neg_eq_add]
  exact ha.neg.isUnit_one_sub

end
