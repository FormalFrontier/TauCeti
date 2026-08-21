/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The conjugate transpose of a special unitary matrix is its adjugate

For a special unitary matrix the conjugate transpose is the inverse, and an invertible matrix of
determinant one is its own adjugate's inverse, so the two descriptions of the inverse agree. This
turns `star` on `Matrix.specialUnitaryGroup n α` into a polynomial expression in the entries, which
is what makes the small special unitary groups computable by hand.

## Main results

* `TauCeti.Matrix.specialUnitaryGroup.star_eq_adjugate`: the conjugate transpose of a special
  unitary matrix is its adjugate.
-/

public section

namespace TauCeti

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

/-- The conjugate transpose of a special unitary matrix is its adjugate: it is the inverse, and
for determinant one the inverse is the adjugate. -/
theorem specialUnitaryGroup.star_eq_adjugate (g : Matrix.specialUnitaryGroup n α) :
    star (g : Matrix n n α) = (g : Matrix n n α).adjugate := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  have hmul : (g : Matrix n n α) * star (g : Matrix n n α) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp hmem.1
  calc star (g : Matrix n n α)
      = (g : Matrix n n α).adjugate * (g : Matrix n n α) * star (g : Matrix n n α) := by
        rw [Matrix.adjugate_mul, hmem.2, one_smul, Matrix.one_mul]
    _ = (g : Matrix n n α).adjugate := by
        rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

end Matrix

end TauCeti
