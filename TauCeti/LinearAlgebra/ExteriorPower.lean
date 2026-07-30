/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Trace

/-!
# Further results on exterior powers

This file records that the `d`th exterior power of a finite free module over a commutative ring
vanishes as soon as `d` exceeds the rank of the module. It also computes the trace of an induced
endomorphism from a basis of eigenvectors.

## Main results

* `exteriorPower.eq_zero_of_finrank_lt` states that every element of `⋀[R]^d M` is zero when
  `Module.finrank R M < d`.
* `exteriorPower.trace_map_of_apply_basis` computes the trace on `⋀[R]^d M` from the
  eigenvalues of an endomorphism on a finite basis.

## References

The results use Mathlib's exterior-power basis and dimension formula from
`Mathlib.LinearAlgebra.ExteriorPower.Basis`, by Sophie Morel and Daniel Morrison.
-/

public section

open scoped BigOperators

universe u w

variable {R : Type u} {M : Type w}

namespace exteriorPower

section Trace

variable [CommRing R]
variable {I : Type*} [Fintype I] [LinearOrder I]
variable [AddCommGroup M] [Module R M]

/-- If an endomorphism is diagonal in a finite basis, then its trace on the `d`th exterior
power is the `d`th elementary symmetric sum of its eigenvalues. -/
theorem trace_map_of_apply_basis (b : Module.Basis I R M) (f : M →ₗ[R] M)
    (a : I → R) (d : ℕ) (hf : ∀ i, f (b i) = a i • b i) :
    LinearMap.trace R (⋀[R]^d M) (map d f) =
      ∑ s : Set.powersetCard I d, ∏ i ∈ (s : Finset I), a i := by
  classical
  let B := b.exteriorPower d
  rw [LinearMap.trace_eq_matrix_trace R B, Matrix.trace]
  apply Finset.sum_congr rfl
  intro s _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [B, basis_apply]
  rw [map_apply_ιMulti_family, basis_repr_apply]
  have hmap :
      ιMulti_family R d (f ∘ b) s =
        (∏ j : Fin d, a (Set.powersetCard.ofFinEmbEquiv.symm s j)) •
          ιMulti_family R d b s := by
    rw [ιMulti_family, ιMulti_family]
    have hfun :
        (f ∘ b) ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
          fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j) •
            b (Set.powersetCard.ofFinEmbEquiv.symm s j) := by
      funext j
      simp only [Function.comp_apply, hf]
    have hbfun :
        b ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
          fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j) := rfl
    rw [hfun]
    rw [hbfun]
    simpa only [Function.comp_apply] using
      (ιMulti R d).map_smul_univ
        (fun j => a (Set.powersetCard.ofFinEmbEquiv.symm s j))
        (fun j => b (Set.powersetCard.ofFinEmbEquiv.symm s j))
  rw [hmap, map_smul, ιMultiDual_apply_diag, smul_eq_mul, mul_one]
  rw [← Finset.prod_coe_sort s.1 a]
  apply Fintype.prod_equiv (s.1.orderIsoOfFin s.2).toEquiv
  intro j
  rfl

end Trace

section Vanishing

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]

/-- An exterior power above the rank of a finite free module is zero. -/
theorem eq_zero_of_finrank_lt (d : ℕ) (h : Module.finrank R M < d) (x : ⋀[R]^d M) :
    x = 0 := by
  have : Subsingleton (⋀[R]^d M) := by
    rcases subsingleton_or_nontrivial R with _ | _
    · exact Module.subsingleton R _
    · rw [← Module.finrank_eq_zero_iff_of_free R, finrank_eq, Nat.choose_eq_zero_iff]
      exact h
  exact Subsingleton.elim x 0

end Vanishing

end exteriorPower
