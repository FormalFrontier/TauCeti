/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic

/-!
# The positive-definite function ↔ positive-definite kernel correspondence

A positive-definite function `F : M → ℂ` on an involutive additive monoid and a positive-definite
kernel `K : M → M → ℂ` are two views of the same data, linked by the assignment
`K(a, b) = F(a + b⋆)`. This file records the forward and reverse correspondence, packages them
as an iff, and records the translation-invariant group specialization.

Both sides express nonnegativity of finite quadratic forms; the two-variable kernel is viewed
directly as a matrix and tested with Mathlib's `Matrix.PosSemidef` predicate.

Under the negation involution `a⋆ = -a` the kernel takes the familiar translation-invariant shape
`K(a, b) = F(a - b)`, the form in which positive definiteness is usually stated on groups such as
`ℝᵈ` or a real inner-product space. We record that specialization as a corollary parameterized by
the hypothesis `star a = -a` (Mathlib pins no such `StarAddMonoid` instance, since `star` is the
identity on a real vector space, so the negation involution is supplied as a side hypothesis rather
than an instance).

This advances the `OneParameterSemigroups` roadmap, Part C ("Positive-definite functions and
Bochner's theorem", `TauCetiRoadmap/OneParameterSemigroups/README.md`): the `API to develop` bullet
"the PD-function ↔ PD-kernel equivalence (`K(a, b) = F(a + b⋆)`; `F(a − b)` for a group)". The two
component predicates already live in TauCeti; this file is the equivalence connecting them, and the
group form. No Mathlib code is vendored.

## Main declarations

* `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteKernel`: the equivalence of the two predicates,
  packaging the two halves.
* `TauCeti.IsPositiveDefinite.isPositiveDefiniteKernel_sub` and
  `TauCeti.isPositiveDefinite_iff_isPositiveDefiniteKernel_sub`: the subtraction form
  `K(a, b) = F(a - b)` under the negation involution `star a = -a`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {M : Type*} [AddMonoid M] [StarAddMonoid M] {F : M → ℂ}

/-- A function `F` on an involutive additive monoid is positive definite if and only if the
two-variable kernel `K(a, b) = F(a + b⋆)` is positive definite. -/
theorem isPositiveDefinite_iff_isPositiveDefiniteKernel :
    IsPositiveDefinite F ↔ Matrix.PosSemidef (fun a b => F (a + star b)) :=
  ⟨IsPositiveDefinite.isPositiveDefiniteKernel, IsPositiveDefinite.of_isPositiveDefiniteKernel⟩

namespace IsPositiveDefinite

variable {G : Type*} [SubNegMonoid G] [StarAddMonoid G] {F : G → ℂ}

/-- Under the negation involution `a⋆ = -a`, a positive-definite function `F` gives the
translation-invariant positive-definite kernel `K(a, b) = F(a - b)`. This is the form in which
positive definiteness is usually stated on groups such as `ℝᵈ` or a real inner-product space. -/
theorem isPositiveDefiniteKernel_sub (hstar : ∀ a : G, star a = -a) (hF : IsPositiveDefinite F) :
    Matrix.PosSemidef (fun a b => F (a - b)) := by
  have hfun : (fun a b : G => F (a + star b)) = fun a b => F (a - b) := by
    funext a b
    rw [hstar, ← sub_eq_add_neg]
  rw [← hfun]
  exact hF.isPositiveDefiniteKernel

end IsPositiveDefinite

variable {G : Type*} [SubNegMonoid G] [StarAddMonoid G] {F : G → ℂ}

/-- Under the negation involution `a⋆ = -a`, `F` is positive definite if and only if the
translation-invariant kernel `K(a, b) = F(a - b)` is positive definite. -/
theorem isPositiveDefinite_iff_isPositiveDefiniteKernel_sub (hstar : ∀ a : G, star a = -a) :
    IsPositiveDefinite F ↔ Matrix.PosSemidef (fun a b => F (a - b)) := by
  have hfun : (fun a b : G => F (a + star b)) = fun a b => F (a - b) := by
    funext a b
    rw [hstar, ← sub_eq_add_neg]
  rw [isPositiveDefinite_iff_isPositiveDefiniteKernel, hfun]

end TauCeti
