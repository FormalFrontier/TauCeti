/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Uniqueness

/-!
# The large-degree Riemann–Roch regime

For a divisor `W` satisfying the Riemann–Roch identity, the correction term at `D` is
`ℓ(W - D)`.  The identities `deg W = 2g - 2` and `ℓ(E) = 0` for `deg E < 0` therefore show
that this correction vanishes as soon as `deg D ≥ 2g - 1`.

This is Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Theorem 1.5.17.
The existence of a divisor satisfying the Riemann–Roch identity is a separate theorem; the
conditional form here is useful independently and is the exact consequence consumed once such a
divisor has been constructed.

## Main result

* `TauCeti.Divisor.dim_eq_degree_add_one_sub_genus_of_degree_ge_two_genus_sub_one`: the
  Riemann–Roch dimension has its sharp large-degree value.

No Mathlib infrastructure or external formalization is vendored here.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **The large-degree Riemann–Roch formula** (Stichtenoth, Theorem 1.5.17): if `W` satisfies the
Riemann–Roch identity and `deg D ≥ 2g - 1`, then the index of specialty of `D` vanishes and
`ℓ(D) = deg D + 1 - g`.

The hypothesis `hW` is the canonical-divisor input to this consequence.  It is kept explicit so
that this theorem can be used before the existence theorem for such a divisor is imported. -/
theorem Divisor.dim_eq_degree_add_one_sub_genus_of_degree_ge_two_genus_sub_one
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {W : Divisor k F} {D : Divisor k F}
    (hW : W.IsRiemannRochDivisor (genus k F))
    (hD : 2 * (genus k F : ℤ) - 1 ≤ Divisor.degree D) :
    (Divisor.dim D : ℤ) = Divisor.degree D + 1 - genus k F := by
  have hWdeg : Divisor.degree W = 2 * (genus k F : ℤ) - 2 :=
    hW.degree_eq hF hex
  have hneg : Divisor.degree (W - D) < 0 := by
    rw [Divisor.degree_sub, hWdeg]
    omega
  have hvanish : Divisor.dim (W - D) = 0 :=
    Divisor.dim_eq_zero_of_degree_neg hF hneg
  have hRR := (Divisor.isRiemannRochDivisor_iff.mp hW) D
  rw [hvanish] at hRR
  simpa using hRR

end TauCeti
