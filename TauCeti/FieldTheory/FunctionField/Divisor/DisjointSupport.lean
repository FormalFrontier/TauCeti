/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Principal

/-!
# Moving a divisor within its class to avoid finitely many places

Every divisor class of an algebraic function field contains a representative whose support misses
any prescribed finite set of places:

```
∀ D, ∀ s : Finset (Place k F), ∃ D' ~ D, Disjoint D'.support s.
```

Weak approximation is what makes this true. Finitely many distinct places impose independent
conditions on `F`, so there is a function whose order at each place of `s` is exactly the negative
of the coefficient of `D` there; adding its divisor cancels `D` on `s` and changes nothing about
the class.

## Main results

* `TauCeti.Divisor.exists_linearlyEquivalent_disjoint_support`: the statement above.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 1.3.1 (weak approximation) and Definition 1.4.3 (linear equivalence).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8 — the divisor
  construction of the Weil pairing, where evaluating one function on another's divisor requires
  exactly this move.
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **Every divisor class has a representative avoiding a given finite set of places.**

Evaluating a function on a divisor requires the divisor's support to miss the function's zeros and
poles; this is what makes that arrangeable, by replacing the divisor with a linearly equivalent one
that avoids them. Weil reciprocity and the divisor construction of the Weil pairing both need the
move. -/
theorem exists_linearlyEquivalent_disjoint_support (hF : IsFunctionField k F) (D : Divisor k F)
    (s : Finset (Place k F)) :
    ∃ D' : Divisor k F, (Place.orderSystem hF).LinearlyEquivalent D D' ∧
      Disjoint D'.support s := by
  -- a function whose order on `s` is exactly minus that of `D`
  obtain ⟨g, hg0, hg⟩ := Place.exists_ne_zero_forall_mem_ord_eq s fun P ↦ -D.coeff P
  refine ⟨D + principal hF (Units.mk0 g hg0), ?_, ?_⟩
  · have h := (Place.orderSystem hF).linearlyEquivalent_add_principalDivisor D
      (Additive.ofMul (Units.mk0 g hg0))
    rw [principalDivisor_eq hF, toMul_ofMul] at h
    exact h.symm
  · rw [Finset.disjoint_left]
    intro P hP hPs
    rw [WeilDivisor.mem_support_iff, WeilDivisor.coeff_add, coeff_principal] at hP
    exact hP (by rw [Units.val_mk0, hg P hPs, add_neg_cancel])

end Divisor

end TauCeti
