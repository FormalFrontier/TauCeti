/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm

/-!
# A four-element cyclic identity for the trace form of a Lie module

Let `M` be a representation of a Lie algebra `L` over a commutative ring `R`. Its trace form
`B = LieModule.traceForm R L M` is symmetric and invariant, `B ⁅a, b⁆ c = B a ⁅b, c⁆`. Together
with the Leibniz rule those two properties give an identity in four elements,

```text
B ⁅a, b⁆ ⁅c, d⁆ + B ⁅b, c⁆ ⁅a, d⁆ + B ⁅c, a⁆ ⁅b, d⁆ = 0,
```

which is the Jacobi identity rewritten so that each summand pairs two brackets against each other
rather than iterating them. No hypothesis at all is needed on the four elements: this is a
consequence of invariance and symmetry, and it holds in every Lie algebra.

Its purpose is downstream: when `a`, `b`, `c`, `d` are root vectors of a split semisimple Lie
algebra and `B` is the Killing form, each summand evaluates to a product of two structure
constants weighted by the Killing pairing of an opposite pair of root vectors, and the identity
becomes the four-term relation between the structure constants. Grouping the brackets in pairs is
exactly what makes that evaluation possible, since a summand with an iterated bracket would mix
root spaces of three different roots.

## Main results

* `TauCeti.traceForm_lie_lie_cyclic_eq_zero`: the identity above.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.1.
-/

public section

namespace TauCeti

open LieModule

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **The four-element cyclic identity for an invariant trace form.** Pairing the three ways of
splitting `a`, `b`, `c`, `d` into two brackets, with `d` always in the second, gives zero.

The proof moves each summand into the shape `B a _` using invariance and symmetry, and then reads
the resulting sum of three inner brackets as the Leibniz rule for `⁅b, ⁅c, d⁆⁆`. -/
theorem traceForm_lie_lie_cyclic_eq_zero (a b c d : L) :
    traceForm R L M ⁅a, b⁆ ⁅c, d⁆ + traceForm R L M ⁅b, c⁆ ⁅a, d⁆ +
      traceForm R L M ⁅c, a⁆ ⁅b, d⁆ = 0 := by
  have h₁ : traceForm R L M ⁅a, b⁆ ⁅c, d⁆ = traceForm R L M a ⁅b, ⁅c, d⁆⁆ :=
    traceForm_apply_lie_apply R L M a b ⁅c, d⁆
  have h₂ : traceForm R L M ⁅b, c⁆ ⁅a, d⁆ = traceForm R L M a ⁅d, ⁅b, c⁆⁆ := by
    rw [traceForm_comm R L M ⁅b, c⁆ ⁅a, d⁆, traceForm_apply_lie_apply]
  have h₃ : traceForm R L M ⁅c, a⁆ ⁅b, d⁆ = -traceForm R L M a ⁅c, ⁅b, d⁆⁆ := by
    rw [← lie_skew c a, map_neg, LinearMap.neg_apply, traceForm_apply_lie_apply]
  have hleib : ⁅b, ⁅c, d⁆⁆ + ⁅d, ⁅b, c⁆⁆ - ⁅c, ⁅b, d⁆⁆ = (0 : L) := by
    rw [leibniz_lie b c d, ← lie_skew d ⁅b, c⁆]
    abel
  have hmap := congrArg (traceForm R L M a) hleib
  rw [map_sub, map_add, map_zero] at hmap
  rw [h₁, h₂, h₃]
  linear_combination hmap

end TauCeti
