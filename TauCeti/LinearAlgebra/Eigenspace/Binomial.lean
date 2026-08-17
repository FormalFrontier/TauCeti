/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Module.Rat

/-!
# Generalized binomial coefficients of an endomorphism at an eigenvector

An endomorphism `f` of a rational vector space is an element of the `ℚ`-algebra
`Module.End ℚ V`, which is a binomial ring, so the generalized binomial coefficients
`Ring.choose f n = f (f - 1) ⋯ (f - n + 1) / n !` are again endomorphisms. This file records that
they are computed on eigenvectors by the same expression in the eigenvalue:

```text
f v = μ • v   →   (f choose n) v = (μ choose n) • v.
```

The mechanism is Mathlib's characterization of `Ring.choose` by
`Ring.descPochhammer_eq_factorial_smul_choose`: the descending Pochhammer polynomial has integer
coefficients, so it is evaluated on an eigenvector by evaluating it at the eigenvalue, and the
factorial is then cancelled because a rational vector space is torsion-free.

Integer eigenvalues are the case of interest: the coefficient is then an ordinary natural-number
binomial coefficient, which is what makes the Cartan generators `(h choose n)` of a Kostant
integral form act integrally on weight vectors. `TauCeti.Sl2Std.ringChoose_diag_apply` is the
coordinate form of the same computation for the standard `sl₂`-modules, where the endomorphism is
diagonal in a fixed basis rather than merely applied to one eigenvector.

## Main results

* `TauCeti.ringChoose_end_apply_of_apply_eq_smul`: the binomial coefficient of an endomorphism
  scales an eigenvector by the binomial coefficient of its eigenvalue.
* `TauCeti.ringChoose_end_apply_of_apply_eq_natCast_smul`: the specialization to a natural-number
  eigenvalue, where the scalar is `Nat.choose`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti

open Polynomial

attribute [local instance] TauCeti.moduleNNRat

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

private theorem pow_apply_of_apply_eq_smul {f : Module.End ℚ V} {v : V} {μ : ℚ}
    (h : f v = μ • v) : ∀ k : ℕ, (f ^ k) v = μ ^ k • v
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, Module.End.mul_apply, h, map_smul, pow_apply_of_apply_eq_smul h k, smul_smul,
      ← pow_succ']

private theorem smeval_apply_of_apply_eq_smul {f : Module.End ℚ V} {v : V} {μ : ℚ}
    (h : f v = μ • v) (p : ℤ[X]) : (p.smeval f) v = (p.smeval μ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [smeval_add, LinearMap.add_apply, hp, hq, smeval_add, add_smul]
  | monomial k z =>
    rw [smeval_monomial, smeval_monomial, LinearMap.smul_apply, pow_apply_of_apply_eq_smul h,
      smul_assoc]

/-- **A binomial coefficient of an endomorphism acts on an eigenvector through its eigenvalue.**
If `f v = μ • v` then `(f choose n) v = (μ choose n) • v`.

Both sides are `n !`-th multiples of the descending Pochhammer expression, which is a polynomial
with integer coefficients and hence is evaluated on `v` by evaluating it at `μ`. -/
theorem ringChoose_end_apply_of_apply_eq_smul {f : Module.End ℚ V} {v : V} {μ : ℚ}
    (h : f v = μ • v) (n : ℕ) : (Ring.choose f n) v = Ring.choose μ n • v := by
  have : IsAddTorsionFree V := .of_module_rat V
  refine (nsmul_right_inj (Nat.factorial_ne_zero n)).mp ?_
  have hf : ((descPochhammer ℤ n).smeval f) v =
      n.factorial • ((Ring.choose f n : Module.End ℚ V) v) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose, LinearMap.smul_apply]
  have hμ : ((descPochhammer ℤ n).smeval μ) • v = n.factorial • (Ring.choose μ n • v) := by
    rw [Ring.descPochhammer_eq_factorial_smul_choose, smul_assoc]
  rw [← hf, ← hμ, smeval_apply_of_apply_eq_smul h]

/-- The binomial coefficients of an endomorphism act on an eigenvector with natural-number
eigenvalue `j` by the ordinary binomial coefficients `(j choose n)`; in particular they act
integrally. -/
theorem ringChoose_end_apply_of_apply_eq_natCast_smul {f : Module.End ℚ V} {v : V} {j : ℕ}
    (h : f v = (j : ℚ) • v) (n : ℕ) : (Ring.choose f n) v = (j.choose n : ℚ) • v := by
  rw [ringChoose_end_apply_of_apply_eq_smul h, Ring.choose_natCast]

end TauCeti
