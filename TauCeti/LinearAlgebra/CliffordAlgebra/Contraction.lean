/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Contraction anticommutes with the grade involution

Mathlib's `CliffordAlgebra.contractLeft` lowers the degree of a multivector by one, so it
exchanges the two halves of the `ℤ/2`-grading and therefore anticommutes with the grade
involution `CliffordAlgebra.involute`. This file proves that single identity, which Mathlib does
not record: `involute` interacts with products (`involute` is an algebra homomorphism) and with
the grading, but never with a contraction.

The identity is what makes the grade involution usable as an odd operator alongside exterior
multiplication and contraction — for instance as the operator by which an anisotropic vector
orthogonal to a polarization acts on a spinor module.

## Main results

* `TauCeti.CliffordAlgebra.involute_contractLeft`: `involute (d ⌋ x) = -(d ⌋ involute x)`.

## References

* [D. Grinberg, *The Clifford algebra and the Chevalley map*][grinberg_clifford_2016], for the
  contraction operators themselves.
-/

public section

open CliffordAlgebra

universe u v

namespace TauCeti.CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- **The grade involution anticommutes with contraction.** Contracting against a linear
functional lowers the degree by one, hence swaps the even and odd parts of the Clifford algebra,
so it anticommutes with the operator that is `+1` on the even part and `-1` on the odd part. -/
@[simp, grind =]
theorem involute_contractLeft (d : Module.Dual R M) (x : CliffordAlgebra Q) :
    involute (contractLeft d x) = -contractLeft d (involute x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | ι_mul x a hx =>
    have hlhs : involute (contractLeft d (ι Q a * x))
        = d a • involute x - ι Q a * contractLeft d (involute x) := by
      rw [contractLeft_ι_mul, map_sub, map_smul, map_mul, involute_ι, hx, neg_mul_neg]
    have hrhs : involute (ι Q a * x) = -(ι Q a * involute x) := by
      rw [map_mul, involute_ι, neg_mul]
    rw [hlhs, hrhs, map_neg, neg_neg, contractLeft_ι_mul]

end TauCeti.CliffordAlgebra
