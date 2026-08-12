/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The grade involution against the degree-shifting operators

The two operators that shift the exterior degree by one are left multiplication by a vector, which
raises it, and `CliffordAlgebra.contractLeft`, which lowers it. Both exchange the two halves of the
`ℤ/2`-grading, so both anticommute with the grade involution `CliffordAlgebra.involute`. This file
records the two identities, which Mathlib does not: `involute` is related there to products (it is
an algebra homomorphism) and to the grading, but neither consequence is stated, and the contraction
is never mentioned alongside it.

The identities are what make the grade involution usable as an odd operator alongside exterior
multiplication and contraction — for instance as the operator by which an anisotropic vector
orthogonal to a polarization acts on a spinor module.

## Main results

* `TauCeti.CliffordAlgebra.involute_ι_mul`: `involute (ι m * x) = -(ι m * involute x)`.
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

/-- **The grade involution anticommutes with left multiplication by a vector.** A vector is odd,
so multiplying by it swaps the even and odd parts of the Clifford algebra.

Not a `simp` lemma: `simp` normalizes the left-hand side through `map_mul` and
`CliffordAlgebra.involute_ι` instead. -/
theorem involute_ι_mul (m : M) (x : CliffordAlgebra Q) :
    involute (ι Q m * x) = -(ι Q m * involute x) := by
  rw [map_mul, involute_ι, neg_mul]

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
    rw [hlhs, involute_ι_mul, map_neg, neg_neg, contractLeft_ι_mul]

end TauCeti.CliffordAlgebra
