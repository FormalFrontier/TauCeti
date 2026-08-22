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
When `H` is nilpotent, it lies in the generalized weight space of its eigenvalue. Without a
nilpotence assumption, applying to it an adjoint eigenvector of weight `psi` shifts its eigenvalue
by `psi`, once per application.

Both are stated over a commutative ring; the weight-space result assumes the subalgebra is
nilpotent, while the weight-shift result applies to an arbitrary subalgebra. The Cartan subalgebra
of a Lie algebra with non-degenerate Killing form, where `psi` is a root, is the case the weight
theory uses, and `TauCeti.lie_pow_toEnd_eq_smul_of_mem_rootSpace` records it.

## Main results

* `TauCeti.mem_genWeightSpace_of_forall_lie_eq_smul`: a simultaneous eigenvector of `H` lies in the
  generalized weight space of its eigenvalue, at nilpotency index one.
* `TauCeti.lie_pow_toEnd_eq_smul`: applying an adjoint eigenvector of weight `psi` to an
  eigenvector of weight `chi`, `k` times, gives an eigenvector of weight `chi + k psi`.
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

/-- **Applying an adjoint eigenvector shifts the weight.** If `H` acts on `v` through `chi` and
`f` is a common adjoint eigenvector of weight `psi`, then `H` acts on `fᵏ v` through
`chi + k psi`.

Each application of `f` costs one `psi` by the Leibniz rule, and the statement is the induction on
`k` that accumulates the cost. The vector `fᵏ v` is allowed to be zero, when the statement is
vacuous. -/
theorem lie_pow_toEnd_eq_smul {chi psi : H → R} {v : M}
    (hv : ∀ x : H, ⁅(x : L), v⁆ = chi x • v) {f : L}
    (hf : ∀ x : H, ⁅(x : L), f⁆ = psi x • f) (k : ℕ) (x : H) :
    ⁅(x : L), ((toEnd R L M f) ^ k) v⁆ = (chi x + k * psi x) • ((toEnd R L M f) ^ k) v := by
  induction k with
  | zero => simpa using hv x
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

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsTriangularizable K H L] {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M]

/-- **Lowering by a root vector shifts the weight.** If `H` acts on `v` through the linear form
`chi` and `f` lies in the root space of `psi`, then `H` acts on `fᵏ v` through `chi + k psi`. -/
theorem lie_pow_toEnd_eq_smul_of_mem_rootSpace {chi psi : H → K} {v : M}
    (hv : ∀ x : H, ⁅(x : L), v⁆ = chi x • v) {f : L} (hf : f ∈ rootSpace H psi) (k : ℕ) (x : H) :
    ⁅(x : L), ((toEnd K L M f) ^ k) v⁆ = (chi x + k * psi x) • ((toEnd K L M f) ^ k) v := by
  apply lie_pow_toEnd_eq_smul hv (fun y => ?_) k x
  rw [← LieSubalgebra.coe_bracket_of_module]
  exact IsKilling.lie_eq_smul_of_mem_rootSpace hf y

end Killing

end TauCeti
