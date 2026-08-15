/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic
public import TauCeti.Analysis.PositiveDefinite.Kernel.Shift

/-!
# Differences of bounded positive-definite functions

On an involutive commutative additive monoid `M`, a *bounded* positive-definite function `F`
dominates each of its translates by a self-adjoint element: if `star s = s`, then

`x ↦ F x - F (x + s)`

is again positive definite. This is the function-level form of
`TauCeti.posSemidef_sub_comp_shift`; self-adjointness of `s` is exactly what makes translation by
`s` a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`.

Boundedness is essential and is not a technical artefact: `t ↦ exp t` is positive definite on the
involutive monoid `(ℝ≥0, +)` with the trivial involution, and it *increases*. The statement is
proved by a purely numerical moment-problem estimate on the finite quadratic forms; no topology,
measurability, or representing measure is assumed or produced here.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C: it is the closure property
of the generic `IsPositiveDefinite` predicate that the Berg--Christensen--Ressel representation
(Milestone 2) runs on, specialized to the time direction of `ℝ≥0 × V` in
`TauCeti/Analysis/PositiveDefinite/SemigroupGroup/Time/Difference.lean`.

## Main declarations

* `TauCeti.IsPositiveDefinite.sub_shift`: the difference of a bounded positive-definite function
  and its translate by a self-adjoint element is positive definite.
* `TauCeti.IsPositiveDefinite.sub_shift_apply_nonneg`: the resulting nonnegativity at the
  "norm points" `a + star a`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti

namespace IsPositiveDefinite

variable {M : Type*} [AddCommMonoid M] [StarAddMonoid M] {F : M → ℂ} {C : ℝ} {s : M}

/-- **A bounded positive-definite function dominates its translate by a self-adjoint element.**
Translation by `s` with `star s = s` is a symmetric shift of the kernel `(a, b) ↦ F (a + star b)`,
so the bounded-kernel estimate `TauCeti.posSemidef_sub_comp_shift` applies. Boundedness cannot be
dropped: `t ↦ exp t` is positive definite on `ℝ≥0` with the trivial involution and increases. -/
theorem sub_shift (hF : IsPositiveDefinite F) (hbdd : ∀ x, ‖F x‖ ≤ C) (hs : star s = s) :
    IsPositiveDefinite fun x => F x - F (x + s) := by
  have hkey := posSemidef_sub_comp_shift (K := fun a b : M => F (a + star b))
    (σ := fun a : M => a + s) hF.posSemidef (fun p q => ?_) (fun p q => hbdd _)
  · refine IsPositiveDefinite.of_posSemidef ?_
    have heq : (fun a b : M => F (a + star b) - F (a + s + star b)) =
        fun a b : M => F (a + star b) - F (a + star b + s) := by
      funext a b
      rw [add_right_comm]
    rw [heq] at hkey
    exact hkey
  · rw [star_add, hs, add_assoc, add_comm s (star q)]

/-- The difference of a bounded positive-definite function and its translate by a self-adjoint
element is nonnegative at every "norm point" `a + star a`. -/
theorem sub_shift_apply_nonneg (hF : IsPositiveDefinite F) (hbdd : ∀ x, ‖F x‖ ≤ C)
    (hs : star s = s) (a : M) : 0 ≤ F (a + star a) - F (a + star a + s) :=
  (hF.sub_shift hbdd hs).add_star_self_nonneg a

end IsPositiveDefinite

end TauCeti
