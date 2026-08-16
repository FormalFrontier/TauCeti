/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Base change of the finite dual

The finite dual of a finite projective bialgebra commutes with extension of scalars. More
precisely, for a map of commutative rings `k → K` and a finite projective `k`-bialgebra `H`,
there is a canonical `K`-bialgebra equivalence

```text
K ⊗[k] ConvolutionDual k H ≃ₐc[K] ConvolutionDual K (K ⊗[k] H).
```

On pure tensors this sends `a ⊗ φ` to the functional taking `b ⊗ x` to
`a * b * algebraMap k K (φ x)`. This is the affine algebraic base-change square needed to
transport Cartier duality for finite locally free commutative group schemes over a general base.

## Main declarations

* `TauCeti.ConvolutionDual.baseChangeBialgEquiv`: finite dualization commutes with extension of
  scalars.
* `TauCeti.ConvolutionDual.baseChangeBialgEquiv_tmul_apply_tmul`: the equivalence's value on pure
  tensors.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConvolutionDual

universe u v w

variable {k : Type u} {K : Type v} {H : Type w}
variable [CommRing k] [CommRing K] [Algebra k K]
variable [Semiring H] [Bialgebra k H]

variable [Module.Finite k H] [Module.Projective k H]

/-- The scalar-extended evaluation map as a linear equivalence. -/
private noncomputable def baseChangeLinearEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₗ[K] ConvolutionDual K (K ⊗[k] H) :=
  ((WithConv.linearEquiv k _).baseChange k K).trans <|
    (Module.Dual.baseChangeEquiv (R := k) (A := K) (M := H)).trans <|
      (WithConv.linearEquiv K _).symm

@[simp]
private theorem baseChangeLinearEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) :=
  by simp [baseChangeLinearEquiv]

private theorem baseChange_one :
    baseChangeLinearEquiv (k := k) (K := K) (H := H)
      (1 ⊗ₜ[k] (1 : ConvolutionDual k H)) = 1 := by
  apply WithConv.ofConv_injective
  ext x
  -- Unwrap `WithConv` after testing the functionals on a pure tensor.
  change (baseChangeLinearEquiv (k := k) (K := K) (H := H)
      (1 ⊗ₜ[k] (1 : ConvolutionDual k H))).ofConv (1 ⊗ₜ[k] x) =
    (1 : ConvolutionDual K (K ⊗[k] H)).ofConv (1 ⊗ₜ[k] x)
  rw [baseChangeLinearEquiv_tmul_apply_tmul]
  simp [Algebra.smul_def]

private theorem baseChange_mul (a b : K) (φ ψ : ConvolutionDual k H) :
    baseChangeLinearEquiv (k := k) (K := K) (H := H)
        ((a * b) ⊗ₜ[k] (φ * ψ)) =
      baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ) *
        baseChangeLinearEquiv (k := k) (K := K) (H := H) (b ⊗ₜ[k] ψ) := by
  apply WithConv.ofConv_injective
  ext x
  -- Unwrap tensor-product multiplication and convolution after evaluation at `1 ⊗ₜ x`.
  change (baseChangeLinearEquiv (k := k) (K := K) (H := H)
      ((a * b) ⊗ₜ[k] (φ * ψ))).ofConv (1 ⊗ₜ[k] x) =
    (baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ) *
      baseChangeLinearEquiv (k := k) (K := K) (H := H)
        (b ⊗ₜ[k] ψ)).ofConv (1 ⊗ₜ[k] x)
  rw [baseChangeLinearEquiv_tmul_apply_tmul]
  rw [LinearMap.convMul_apply, LinearMap.convMul_apply]
  simp only [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
  generalize Coalgebra.comul (R := k) (A := H) x = q
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add q r hq hr =>
      simp only [map_add, hq, hr, mul_add, TensorProduct.tmul_add]
  | tmul y z =>
      simp only [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
        TensorProduct.map_tmul, LinearMap.mul'_apply,
        baseChangeLinearEquiv_tmul_apply_tmul, map_mul]
      ring

/-- The scalar-extended evaluation map as an algebra equivalence. -/
private noncomputable def baseChangeAlgEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₐ[K] ConvolutionDual K (K ⊗[k] H) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (baseChangeLinearEquiv (k := k) (K := K) (H := H))
    baseChange_mul baseChange_one

@[simp]
private theorem baseChangeAlgEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeAlgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) :=
  baseChangeLinearEquiv_tmul_apply_tmul a b φ x

/-- The base-change algebra equivalence preserves the finite-dual counit. -/
private theorem baseChange_counit :
    (Bialgebra.counitAlgHom K (ConvolutionDual K (K ⊗[k] H))).comp
        (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[k] ConvolutionDual k H) := by
  apply AlgHom.ext (R := K) (A := K ⊗[k] ConvolutionDual k H) (B := K)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a φ =>
      -- `AlgHom.comp` and `baseChangeAlgEquiv` reduce to their underlying counit and map.
      change Coalgebra.counit (R := K)
          (baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)) =
        Coalgebra.counit (R := K) (a ⊗ₜ[k] φ)
      rw [ConvolutionDual.counit_apply]
      -- The finite-dual counit is evaluation at the tensor-product unit `1 ⊗ₜ 1`.
      change (baseChangeLinearEquiv (k := k) (K := K) (H := H)
          (a ⊗ₜ[k] φ)).ofConv (1 ⊗ₜ[k] (1 : H)) = _
      rw [baseChangeLinearEquiv_tmul_apply_tmul]
      simp [ConvolutionDual.counit_apply, Algebra.smul_def, mul_comm]

/-- The base-change algebra equivalence preserves the finite-dual comultiplication. -/
private theorem baseChange_comul :
    (Algebra.TensorProduct.map
        (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom
        (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom).comp
        (Bialgebra.comulAlgHom K (K ⊗[k] ConvolutionDual k H)) =
      (Bialgebra.comulAlgHom K (ConvolutionDual K (K ⊗[k] H))).comp
        (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom := by
  apply AlgHom.ext (R := K) (A := K ⊗[k] ConvolutionDual k H)
    (B := ConvolutionDual K (K ⊗[k] H) ⊗[K] ConvolutionDual K (K ⊗[k] H))
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a φ =>
      apply (dualDistribEquiv K (K ⊗[k] H)).injective
      ext x y
      -- Unwrap the two composed bialgebra maps, then compare distributions on pure tensors.
      change dualDistribEquiv K (K ⊗[k] H)
          ((Algebra.TensorProduct.map
            (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom
            (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom)
              (Coalgebra.comul (R := K) (a ⊗ₜ[k] φ)))
            ((1 ⊗ₜ[k] x) ⊗ₜ[K] (1 ⊗ₜ[k] y)) =
        dualDistribEquiv K (K ⊗[k] H)
          (Coalgebra.comul (R := K)
            (baseChangeAlgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)))
            ((1 ⊗ₜ[k] x) ⊗ₜ[K] (1 ⊗ₜ[k] y))
      rw [ConvolutionDual.dualDistribEquiv_comul_apply]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [baseChangeAlgEquiv_tmul_apply_tmul]
      rw [← ConvolutionDual.dualDistribEquiv_comul_apply k H φ x y]
      simp only [TensorProduct.comul_tmul]
      generalize Coalgebra.comul (R := k) (A := ConvolutionDual k H) φ = q
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q r hq hr =>
          simp only [TensorProduct.tmul_add, map_add, hq, hr,
            LinearMap.add_apply, mul_add]
      | tmul ψ χ =>
          simp [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
            baseChangeAlgEquiv_tmul_apply_tmul, map_mul]
          ring

/-- Finite dualization commutes with extension of scalars for finite projective bialgebras.

The equivalence preserves the Hopf algebra structure whenever `H` is a Hopf algebra, since
bialgebra morphisms commute with antipodes. -/
noncomputable def baseChangeBialgEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₐc[K] ConvolutionDual K (K ⊗[k] H) :=
  BialgEquiv.ofAlgEquiv
    (R := K) (A := K ⊗[k] ConvolutionDual k H)
    (B := ConvolutionDual K (K ⊗[k] H))
    (baseChangeAlgEquiv (k := k) (K := K) (H := H))
    baseChange_counit baseChange_comul

/-- The base-change equivalence evaluates pure tensors by scalar-extended evaluation. -/
@[simp]
theorem baseChangeBialgEquiv_tmul_apply_tmul (a b : K)
    (φ : ConvolutionDual k H) (x : H) :
    (baseChangeBialgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) := by
  rw [baseChangeBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact baseChangeAlgEquiv_tmul_apply_tmul a b φ x

end TauCeti.ConvolutionDual
