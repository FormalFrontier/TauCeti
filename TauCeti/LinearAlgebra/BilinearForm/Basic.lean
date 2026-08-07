/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Tactic.LinearCombination

/-!
# A form that is both symmetric and alternating

Away from characteristic two a bilinear form cannot be both symmetric and alternating without
being zero: symmetry and alternation give `B x y = B y x` and `B x y = -B y x`, so `2 * B x y = 0`,
and `2` is not a zero divisor.

## Main results

* `TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`: a symmetric alternating form over a ring without
  zero divisors in which `2 ≠ 0` is zero.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

namespace BilinForm

/-- **Away from characteristic two a symmetric alternating form is zero.** -/
theorem eq_zero_of_isSymm_of_isAlt {R M : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup M]
    [Module R M] (h2 : (2 : R) ≠ 0) {B : BilinForm R M} (hsymm : B.IsSymm) (halt : B.IsAlt) :
    B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  have hzero : (2 : R) * B x y = 0 := by
    linear_combination hsymm.eq x y - halt.neg_eq x y
  simpa using (mul_eq_zero.mp hzero).resolve_left h2

end BilinForm

end TauCeti
