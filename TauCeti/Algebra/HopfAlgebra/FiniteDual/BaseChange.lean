/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.Algebra.Module.Projective
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
variable [CommRing H] [Bialgebra k H]

/-- The scalar-extended evaluation map, with convolution wrappers on its source and target. -/
private noncomputable def baseChangeGenerator :
    ConvolutionDual k H →ₗ[k] Module.Dual K (K ⊗[k] H) :=
  Module.Dual.baseChange K ∘ₗ (WithConv.linearEquiv k _).toLinearMap

/-- Extend a convolution-dual functional and restore the convolution wrapper. -/
private noncomputable def baseChange :
    K ⊗[k] ConvolutionDual k H →ₗ[K] ConvolutionDual K (K ⊗[k] H) where
  toFun z := WithConv.toConv
    ((baseChangeGenerator (k := k) (K := K) (H := H)).liftBaseChange K z)
  map_add' x y := by apply WithConv.ofConv_injective; simp
  map_smul' a x := by apply WithConv.ofConv_injective; simp

@[simp]
private theorem baseChange_tmul_apply_tmul (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChange (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv (b ⊗ₜ[k] x) =
      a * b * algebraMap k K (φ.ofConv x) := by
  simp [baseChange, baseChangeGenerator, Algebra.smul_def]
  ac_rfl

variable [Module.Finite k H] [Module.Projective k H]

/-- The underlying bijection of the base-change map, assembled from linear equivalences. -/
private noncomputable def baseChangeEquivAux :
    (K ⊗[k] ConvolutionDual k H) ≃ ConvolutionDual K (K ⊗[k] H) :=
  (TensorProduct.congr (LinearEquiv.refl k K) (WithConv.linearEquiv k _)).toEquiv.trans <|
    (Module.Dual.baseChangeEquiv (R := k) (A := K) (M := H)).toEquiv.trans <|
      (WithConv.linearEquiv K _).symm.toEquiv

private theorem baseChange_coe_eq_baseChangeEquivAux :
    (baseChange (k := k) (K := K) (H := H) :
      K ⊗[k] ConvolutionDual k H → ConvolutionDual K (K ⊗[k] H)) =
        baseChangeEquivAux (k := k) (K := K) (H := H) := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => simp [baseChangeEquivAux]
  | add z w hz hw =>
      rw [map_add, hz, hw]
      simp [baseChangeEquivAux]
  | tmul a φ =>
      apply WithConv.ofConv_injective
      ext x
      simp [baseChangeEquivAux, baseChange, baseChangeGenerator,
        Algebra.smul_def]

/-- The scalar-extended evaluation map as a linear equivalence. -/
private noncomputable def baseChangeLinearEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₗ[K] ConvolutionDual K (K ⊗[k] H) :=
  LinearEquiv.ofBijective (baseChange (k := k) (K := K) (H := H)) <| by
    rw [baseChange_coe_eq_baseChangeEquivAux]
    exact (baseChangeEquivAux (k := k) (K := K) (H := H)).bijective

@[simp]
private theorem baseChangeLinearEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) :=
  baseChange_tmul_apply_tmul a b φ x

omit [Module.Finite k H] [Module.Projective k H] in
private theorem baseChange_one :
    baseChange (k := k) (K := K) (H := H) 1 = 1 := by
  rw [show (1 : K ⊗[k] ConvolutionDual k H) =
      1 ⊗ₜ[k] (1 : ConvolutionDual k H) by exact Algebra.TensorProduct.one_def]
  apply WithConv.ofConv_injective
  ext x
  change (baseChange (k := k) (K := K) (H := H)
      (1 ⊗ₜ[k] (1 : ConvolutionDual k H))).ofConv (1 ⊗ₜ[k] x) =
    (1 : ConvolutionDual K (K ⊗[k] H)).ofConv (1 ⊗ₜ[k] x)
  rw [baseChange_tmul_apply_tmul]
  simp [Algebra.smul_def]

omit [Module.Finite k H] [Module.Projective k H] in
private theorem baseChange_mul (z w : K ⊗[k] ConvolutionDual k H) :
    baseChange (k := k) (K := K) (H := H) (z * w) =
      baseChange (k := k) (K := K) (H := H) z *
        baseChange (k := k) (K := K) (H := H) w := by
  apply LinearMap.map_mul_of_map_mul_tmul
  intro a b φ ψ
  apply WithConv.ofConv_injective
  ext x
  change (baseChange (k := k) (K := K) (H := H)
      ((a * b) ⊗ₜ[k] (φ * ψ))).ofConv (1 ⊗ₜ[k] x) =
    (baseChange (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ) *
      baseChange (k := k) (K := K) (H := H) (b ⊗ₜ[k] ψ)).ofConv (1 ⊗ₜ[k] x)
  rw [baseChange_tmul_apply_tmul]
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
        baseChange_tmul_apply_tmul, map_mul]
      ring

/-- The scalar-extended evaluation map as an algebra equivalence. -/
private noncomputable def baseChangeAlgEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₐ[K] ConvolutionDual K (K ⊗[k] H) :=
  AlgEquiv.ofLinearEquiv (baseChangeLinearEquiv (k := k) (K := K) (H := H))
    baseChange_one baseChange_mul

@[simp]
private theorem baseChangeAlgEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeAlgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) :=
  baseChange_tmul_apply_tmul a b φ x

/-- Finite dualization commutes with extension of scalars for finite projective bialgebras.

The equivalence preserves the Hopf algebra structure whenever `H` is a Hopf algebra, since
bialgebra morphisms commute with antipodes. -/
noncomputable def baseChangeBialgEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₐc[K] ConvolutionDual K (K ⊗[k] H) :=
  BialgEquiv.ofAlgEquiv
    (R := K) (A := K ⊗[k] ConvolutionDual k H)
    (B := ConvolutionDual K (K ⊗[k] H))
    (baseChangeAlgEquiv (k := k) (K := K) (H := H))
    (by
      apply AlgHom.ext (R := K) (A := K ⊗[k] ConvolutionDual k H) (B := K)
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul a φ =>
          change Coalgebra.counit (R := K)
              (baseChange (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)) =
            Coalgebra.counit (R := K) (a ⊗ₜ[k] φ)
          rw [ConvolutionDual.counit_apply]
          change (baseChange (k := k) (K := K) (H := H)
              (a ⊗ₜ[k] φ)).ofConv (1 ⊗ₜ[k] (1 : H)) = _
          rw [baseChange_tmul_apply_tmul]
          simp [ConvolutionDual.counit_apply, Algebra.smul_def, mul_comm])
    (by
      apply AlgHom.ext (R := K) (A := K ⊗[k] ConvolutionDual k H)
        (B := ConvolutionDual K (K ⊗[k] H) ⊗[K] ConvolutionDual K (K ⊗[k] H))
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul a φ =>
          apply (dualDistribEquiv K (K ⊗[k] H)).injective
          ext x y
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
              ring)

/-- The base-change equivalence evaluates pure tensors by scalar-extended evaluation. -/
@[simp]
theorem baseChangeBialgEquiv_tmul_apply_tmul (a b : K)
    (φ : ConvolutionDual k H) (x : H) :
    (baseChangeBialgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) := by
  rw [baseChangeBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  change (baseChange (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
    (b ⊗ₜ[k] x) = _
  exact baseChange_tmul_apply_tmul a b φ x

end TauCeti.ConvolutionDual
