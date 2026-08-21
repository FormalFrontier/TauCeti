/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Self-multiplication cancellation for formal power series

A formal power series fixed by multiplication with a series of zero constant coefficient is zero:
if `f = g * f` in `R⟦X⟧` and `constantCoeff g = 0`, then `f = 0`.

This is the uniqueness engine for recursively defined power series: two solutions of the same
recurrence have a difference `f` satisfying exactly such a fixed-point equation, with the `g`
coming from the recurrence and having no constant term.

Multiplication on either side works, and neither form needs commutativity.

## Main results

* `PowerSeries.eq_zero_of_self_eq_mul_self`: `constantCoeff g = 0` and `f = g * f` give `f = 0`.
* `PowerSeries.eq_zero_of_self_eq_self_mul`: the same for `f = f * g`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/PowerSeriesHelpers.lean`, declarations `eq_zero_of_self_eq_mul_self` and
`eq_zero_of_self_eq_self_mul`. The source states the second over a `CommSemiring`, deriving it
from the first by `mul_comm`; that hypothesis is unnecessary, and both are stated here over a
`Semiring`.
-/

public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- A power series whose order is not raised by adding one is zero: in `ℕ∞` only `⊤` satisfies
`order f + 1 ≤ order f`. -/
private theorem eq_zero_of_order_add_one_le {f : R⟦X⟧} (h : f.order + 1 ≤ f.order) : f = 0 := by
  by_contra hf
  exact absurd ((ENat.add_one_le_iff <| order_eq_top.not.mpr hf).mp h) (lt_irrefl _)

/-- **Self-multiplication cancellation.** If `f = g * f` in `R⟦X⟧` and `g` has zero constant
coefficient, then `f = 0`. -/
theorem eq_zero_of_self_eq_mul_self {f g : R⟦X⟧} (hg : constantCoeff g = 0) (h : f = g * f) :
    f = 0 := by
  -- `order g ≥ 1`, so the order of `g * f` strictly exceeds that of `f` unless `f = 0`.
  refine eq_zero_of_order_add_one_le ?_
  have hgorder : (1 : ℕ∞) ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg
  calc f.order + 1 = 1 + f.order := by rw [add_comm]
    _ ≤ g.order + f.order := by gcongr
    _ ≤ (g * f).order := le_order_mul g f
    _ = f.order := (congrArg _ h).symm

/-- **Self-multiplication cancellation, other side.** If `f = f * g` in `R⟦X⟧` and `g` has zero
constant coefficient, then `f = 0`.

No commutativity is needed: `order f + order g ≤ order (f * g)` holds with the factors in either
order, so this runs the same argument as `eq_zero_of_self_eq_mul_self`. -/
theorem eq_zero_of_self_eq_self_mul {f g : R⟦X⟧} (hg : constantCoeff g = 0) (h : f = f * g) :
    f = 0 := by
  refine eq_zero_of_order_add_one_le ?_
  have hgorder : (1 : ℕ∞) ≤ g.order := one_le_order_iff_constCoeff_eq_zero.mpr hg
  calc f.order + 1 ≤ f.order + g.order := by gcongr
    _ ≤ (f * g).order := le_order_mul f g
    _ = f.order := (congrArg _ h).symm

end PowerSeries
