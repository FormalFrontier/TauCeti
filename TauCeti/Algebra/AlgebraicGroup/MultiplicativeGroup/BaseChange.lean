/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# Base change of multiplicative-group points

The multiplicative group `𝔾_m` over `k` is represented here by the Laurent-polynomial Hopf
algebra `k[T;T⁻¹]`. This file records the base-changed functor-of-points calculation: for a
`k`-algebra `K` and a commutative `K`-algebra `A`, the convolution group of `K`-algebra maps
out of `K ⊗[k] k[T;T⁻¹]` is the unit group `Aˣ`.

The equivalence first restricts a base-changed point along `f ↦ f (1 ⊗ T)` using
`AlgHom.baseChangePointsMulEquiv`, then applies the Laurent-polynomial calculation
`MultiplicativeGroup.pointsMulEquiv`. The characteristic lemmas give the values on
`1 ⊗ T` and on the inverse map at pure tensors `s ⊗ C r * T n`.

This is the direct Laurent-polynomial `𝔾_m` worked example for the ReductiveGroups roadmap,
Layer 0 ("R-points as a group" and "Base change. `K ⊗[k] A` as a Hopf algebra over `K`"),
alongside the more general diagonalizable and split-torus base-change APIs.

## Main declarations

* `TauCeti.MultiplicativeGroup.baseChangePointsMulEquiv`: base-changed `𝔾_m` points are
  units of the value algebra.
* `TauCeti.MultiplicativeGroup.baseChangePointsMulEquiv_apply`: the equivalence reads a
  point on the base-changed coordinate `1 ⊗ T`.
* `TauCeti.MultiplicativeGroup.baseChangePointsMulEquiv_symm_apply_tmul_C_mul_T`: the inverse
  equivalence evaluates pure Laurent monomials `s ⊗ C r * T n`.
## References

This reuses Tau Ceti's `AlgHom.baseChangePointsMulEquiv` and
`MultiplicativeGroup.pointsMulEquiv`, which in turn build on Mathlib's tensor-product
base-change adjunction and Laurent-polynomial Hopf algebra structure.
-/

public section

open WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti

namespace MultiplicativeGroup

universe u v w

variable {k : Type u} {K : Type v} {A : Type w}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The `A`-points of the base change `K ⊗[k] k[T;T⁻¹]` of the multiplicative group are
the unit group `Aˣ`.

The source is the convolution group of `K`-algebra maps out of the base-changed Hopf algebra.
The target is the ordinary unit group of the value algebra. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] k[T;T⁻¹] →ₐ[K] A) ≃* Aˣ :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K) (A := k[T;T⁻¹]) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (A := A))

/-- The base-changed multiplicative-group points equivalence reads a point by evaluating it
on the base-changed coordinate `1 ⊗ T`. -/
@[simp]
theorem baseChangePointsMulEquiv_apply
    (f : WithConv (K ⊗[k] k[T;T⁻¹] →ₐ[K] A)) :
    (baseChangePointsMulEquiv f : A) =
      f.ofConv (1 ⊗ₜ[k] LaurentPolynomial.T 1) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, pointsMulEquiv_apply,
    unitOfPoint_val, AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed multiplicative-group points equivalence evaluates pure Laurent
monomials `s ⊗ C r * T n` as scalar multiples of the corresponding power of the chosen unit. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_C_mul_T (u : Aˣ) (s : K) (r : k) (n : ℤ) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u).ofConv
        (s ⊗ₜ[k] (LaurentPolynomial.C r * LaurentPolynomial.T n)) =
      s • (r • ((u ^ n : Aˣ) : A)) := by
  simp only [baseChangePointsMulEquiv, MulEquiv.symm_trans_apply, MulEquiv.symm_symm,
    AlgHom.baseChangePointsMulEquiv_apply_tmul, pointsMulEquiv_symm_apply]
  simp [Algebra.smul_def]

/-- The inverse base-changed multiplicative-group points equivalence evaluates pure tensors
`s ⊗ T n` as scalar multiples of the corresponding power of the chosen unit. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_T (u : Aˣ) (s : K) (n : ℤ) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u).ofConv
        (s ⊗ₜ[k] LaurentPolynomial.T n) =
      s • ((u ^ n : Aˣ) : A) := by
  simpa using baseChangePointsMulEquiv_symm_apply_tmul_C_mul_T
    (k := k) (K := K) (A := A) u s (1 : k) n

/-- The inverse base-changed multiplicative-group points equivalence takes `1 ⊗ T` to the
chosen unit. -/
theorem baseChangePointsMulEquiv_symm_apply_T (u : Aˣ) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm u).ofConv
        (1 ⊗ₜ[k] LaurentPolynomial.T 1) =
      (u : A) := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_T]
  simp

end MultiplicativeGroup

end TauCeti
