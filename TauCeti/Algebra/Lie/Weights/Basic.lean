/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Elementary identities for Lie algebra weights

This file records general identities for weights that are used by several parts of the Lie algebra
weight-space theory.

## Main results

* `TauCeti.Weight.coe_neg_eq_add_of_coe_eq_add`: reading a vanishing sum of four weights as an
  equation between opposite pair sums.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]

/-- If four weights sum to zero and a weight `μ` names the sum of the first two, then `-μ` names
the sum of the last two. -/
theorem Weight.coe_neg_eq_add_of_coe_eq_add {μ : Weight K H L} {a b c d : H → K}
    (hsum : a + b + c + d = 0) (hμ : (μ : H → K) = a + b) :
    ((-μ : Weight K H L) : H → K) = c + d := by
  funext y
  have hy := congrFun hsum y
  simp only [Weight.coe_neg, hμ, Pi.add_apply, Pi.neg_apply, Pi.zero_apply] at hy ⊢
  linear_combination -hy

end TauCeti
