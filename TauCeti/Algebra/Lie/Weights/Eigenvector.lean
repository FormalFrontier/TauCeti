/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing

public section

/-!
# Simultaneous eigenvectors of a subalgebra

Let `H` be a subalgebra of a Lie algebra `L` acting on a module `M`. A vector `v` on which every
element of `H` acts by a scalar is a **simultaneous eigenvector**, its eigenvalue being the
function `chi : H → R` that records those scalars. This file collects two facts about such a vector.
When `H` is nilpotent, it lies in the generalized weight space of its eigenvalue. And applying to
it an eigenvector `f` of the adjoint action shifts its eigenvalue by that of `f`, once per
application; this second fact is one element of `L` at a time, so it needs no subalgebra at all.

Both are stated over a commutative ring; the weight-space result assumes the subalgebra is
nilpotent. The Cartan subalgebra of a Lie algebra with non-degenerate Killing form, where the
eigenvalue of `f` is a root, is the case the weight theory uses, and
`TauCeti.lie_pow_toEnd_eq_smul_of_mem_rootSpace` records it.

## Main results

* `TauCeti.mem_genWeightSpace_of_forall_lie_eq_smul`: a simultaneous eigenvector of `H` lies in the
  generalized weight space of its eigenvalue, at nilpotency index one.
* `TauCeti.lie_pow_toEnd_eq_smul`: for a single `x : L`, applying an `x`-eigenvector `f` of
  eigenvalue `c` to an `x`-eigenvector of eigenvalue `a`, `k` times, gives an `x`-eigenvector of
  eigenvalue `a + k c`.
* `TauCeti.lie_pow_toEnd_eq_smul_of_mem_rootSpace`: the specialization of the shift to a vector of
  the root space of `psi`, which is an adjoint eigenvector of weight `psi` by
  `LieAlgebra.IsKilling.lie_eq_smul_of_mem_rootSpace`.

## References

This is elementary weight-space infrastructure for the highest weight modules of Layer 3 and the
"integrability relation" milestone of Layer 4 of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`: the weight shift is what makes
a lowered highest weight vector an eigenvector again.
-/

namespace TauCeti

open LieAlgebra LieModule Module

universe u v w

section CommRing

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L} {M : Type w} [AddCommGroup M] [Module R M] [LieRingModule L M]
  [LieModule R L M]

variable [LieRing.IsNilpotent ↥H] in
/-- An eigenvector for the whole subalgebra `H` lies in the generalized weight space of its
eigenvalue: an honest simultaneous eigenvector is a generalized one, at nilpotency index one. -/
theorem mem_genWeightSpace_of_forall_lie_eq_smul {chi : H → R} {v : M}
    (hv : ∀ x : H, ⁅(x : L), v⁆ = chi x • v) : v ∈ genWeightSpace M chi :=
  weightSpace_le_genWeightSpace (M := M) chi <| (mem_weightSpace chi v).mpr fun x => by
    rw [LieSubalgebra.coe_bracket_of_module]
    exact hv x

/-- **Applying an adjoint eigenvector shifts the eigenvalue.** If `x` acts on `v` by `a` and `f`
is an eigenvector of `ad x` of eigenvalue `c`, then `x` acts on `fᵏ v` by `a + k c`.

Each application of `f` costs one `c` by the Leibniz rule, and the statement is the induction on
`k` that accumulates the cost. The vector `fᵏ v` is allowed to be zero, when the statement is
vacuous. -/
theorem lie_pow_toEnd_eq_smul {x f : L} {a c : R} {v : M} (hv : ⁅x, v⁆ = a • v)
    (hf : ⁅x, f⁆ = c • f) (k : ℕ) :
    ⁅x, ((toEnd R L M f) ^ k) v⁆ = (a + k * c) • ((toEnd R L M f) ^ k) v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
      have hstep : ∀ m : M, ((toEnd R L M f) ^ (k + 1)) m = ⁅f, ((toEnd R L M f) ^ k) m⁆ := by
        intro m
        rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
      rw [hstep, leibniz_lie, hf, ih, smul_lie, lie_smul, ← add_smul]
      congr 1
      push_cast
      ring

end CommRing

section Killing

variable {K : Type u} {L : Type v} [Field K] [PerfectField K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L] {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M]

/-- **Lowering by a root vector shifts the weight.** If `H` acts on `v` through the linear form
`chi` and `f` lies in the root space of `psi`, then `H` acts on `fᵏ v` through `chi + k psi`. -/
theorem lie_pow_toEnd_eq_smul_of_mem_rootSpace {chi psi : H → K} {v : M}
    (hv : ∀ x : H, ⁅(x : L), v⁆ = chi x • v) {f : L} (hf : f ∈ rootSpace H psi) (k : ℕ) (x : H) :
    ⁅(x : L), ((toEnd K L M f) ^ k) v⁆ = (chi x + k * psi x) • ((toEnd K L M f) ^ k) v := by
  refine lie_pow_toEnd_eq_smul (hv x) ?_ k
  rw [← LieSubalgebra.coe_bracket_of_module]
  exact IsKilling.lie_eq_smul_of_mem_rootSpace hf x

end Killing

end TauCeti
