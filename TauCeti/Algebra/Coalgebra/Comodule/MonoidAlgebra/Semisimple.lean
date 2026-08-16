/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Semisimple point actions on monoid-algebra comodules

The weight-space decomposition of a comodule over a monoid algebra diagonalizes the endomorphism
induced by any algebra map from the monoid algebra to a commutative ring. This file proves the
corresponding eigenspace spanning result and, when the target is a field, semisimplicity of the
induced endomorphism.

## Main declarations

* `TauCeti.Comodule.baseChange_weightSpace_le_eigenspace`: the base-changed `x`-weight space is
  contained in the corresponding eigenspace of the point-action endomorphism.
* `TauCeti.Comodule.iSup_baseChange_weightSpace_eq_top`: the base-changed weight submodules span the
  scalar extension.
* `TauCeti.Comodule.iSup_eigenspace_endOfPoint_eq_top`: the eigenspaces of the point action span the
  scalar extension.
* `TauCeti.Comodule.isSemisimple_endOfPoint_monoidAlgebra`: the point-action endomorphism on any
  comodule over a monoid algebra is semisimple.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.

This supplies generic comodule infrastructure used by the semisimple-points results for
diagonalizable groups in Layer 4 of the ReductiveGroups roadmap.
-/

public section

open Module
open scoped DirectSum TensorProduct

namespace TauCeti

universe u v w x

variable {R : Type u} {X : Type v} {V : Type w} {K : Type x}
variable [CommSemiring R] [Monoid X] [AddCommMonoid V] [Module R V]
variable [Comodule R (MonoidAlgebra R X) V]

section CommRing

variable [CommRing K] [Algebra R K]

/-- The base change to `K` of the `x`-weight submodule is contained in the eigenspace of
`Comodule.endOfPoint V f` with eigenvalue `f (MonoidAlgebra.single x 1)`. -/
theorem Comodule.baseChange_weightSpace_le_eigenspace (f : MonoidAlgebra R X →ₐ[R] K) (x : X) :
    (weightSpace R X V x).baseChange K ≤
      End.eigenspace (endOfPoint V f) (f (MonoidAlgebra.single x 1)) := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, End.mem_eigenspace_iff]
  have h := endOfPoint_tmul_of_mem_weightSpace f (1 : K) hv
  rw [one_mul] at h
  -- Eigenspace membership uses scalar multiplication on `K ⊗[R] V`, whereas the weight-space
  -- action lemma expresses the same vector as a pure tensor; expose that definitional equality
  -- before normalizing scalar multiplication on the tensor product.
  change endOfPoint V f (1 ⊗ₜ[R] v) = f (MonoidAlgebra.single x 1) • (1 ⊗ₜ[R] v)
  rw [h, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end CommRing

section CommSemiring

variable [CommSemiring K] [Algebra R K]

omit [Monoid X] in
/-- The base-changed weight submodules of a monoid-algebra comodule span the scalar extension. -/
theorem Comodule.iSup_baseChange_weightSpace_eq_top :
    ⨆ x : X, (weightSpace R X V x).baseChange K = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.mpr fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a v =>
    have hv : v = (weightDecomposition R X V v).sum (fun _ w ↦ w) :=
      (weightDecomposition_sum (R := R) (G := X) (V := V) v).symm
    rw [hv, Finsupp.sum, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun x _ ↦ ?_
    refine Submodule.mem_iSup_of_mem x ?_
    rw [weightDecomposition_apply]
    exact Submodule.tmul_mem_baseChange_of_mem a (weightProj_mem_weightSpace x v)
  | add z₁ z₂ hz₁ hz₂ => exact add_mem hz₁ hz₂

end CommSemiring

section CommRing

variable [CommRing K] [Algebra R K]

/-- The eigenspaces of the point-action endomorphism `Comodule.endOfPoint V f` span the scalar
extension `K ⊗[R] V`. -/
theorem Comodule.iSup_eigenspace_endOfPoint_eq_top (f : MonoidAlgebra R X →ₐ[R] K) :
    ⨆ μ : K, End.eigenspace (endOfPoint V f) μ = ⊤ := by
  classical
  have hspan : ⨆ x : X, (weightSpace R X V x).baseChange K ≤
      ⨆ μ : K, End.eigenspace (endOfPoint V f) μ := by
    refine iSup_le fun x ↦ ?_
    exact le_trans (baseChange_weightSpace_le_eigenspace f x)
      (le_iSup (fun μ : K ↦ End.eigenspace (endOfPoint V f) μ) (f (MonoidAlgebra.single x 1)))
  rw [iSup_baseChange_weightSpace_eq_top] at hspan
  exact top_unique hspan

end CommRing

variable [Field K] [Algebra R K]

/-- **The point-action endomorphism on any comodule over a monoid algebra is semisimple.** -/
theorem Comodule.isSemisimple_endOfPoint_monoidAlgebra (f : MonoidAlgebra R X →ₐ[R] K) :
    End.IsSemisimple (endOfPoint V f) :=
  isSemisimple_of_iSup_eigenspace_eq_top (iSup_eigenspace_endOfPoint_eq_top f)

end TauCeti
