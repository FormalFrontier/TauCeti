/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Functoriality
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
* `TauCeti.ConvolutionDual.baseChangeBialgEquiv_naturality`: compatibility with finite-dual maps.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConvolutionDual

universe u v w x

variable {k : Type u} {K : Type v} {H : Type w}
variable [CommRing k] [CommRing K] [Algebra k K]
variable [Semiring H] [Bialgebra k H]

variable [Module.Finite k H] [Module.Projective k H]

/-- The scalar-extended evaluation map as a linear equivalence. -/
private noncomputable def baseChangeLinearEquiv :
    K ⊗[k] ConvolutionDual k H ≃ₗ[K] ConvolutionDual K (K ⊗[k] H) :=
  ((WithConv.linearEquiv k _).baseChange k K).trans <|
    (Module.Dual.baseChangeEvaluationEquiv (R := k) (A := K) (M := H)).trans <|
      (WithConv.linearEquiv K _).symm

@[simp]
private theorem baseChangeLinearEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) :=
  by simp [baseChangeLinearEquiv]

omit [Module.Finite k H] [Module.Projective k H] in
private theorem ofConv_ext {φ ψ : ConvolutionDual K (K ⊗[k] H)}
    (h : ∀ x : H, φ.ofConv (1 ⊗ₜ[k] x) = ψ.ofConv (1 ⊗ₜ[k] x)) : φ = ψ := by
  apply WithConv.ofConv_injective
  ext x
  exact h x

private theorem dualDistribEquiv_ext
    {w z : ConvolutionDual K (K ⊗[k] H) ⊗[K] ConvolutionDual K (K ⊗[k] H)}
    (h : ∀ x y : H,
      dualDistribEquiv K (K ⊗[k] H) w ((1 ⊗ₜ[k] x) ⊗ₜ[K] (1 ⊗ₜ[k] y)) =
        dualDistribEquiv K (K ⊗[k] H) z ((1 ⊗ₜ[k] x) ⊗ₜ[K] (1 ⊗ₜ[k] y))) :
    w = z := by
  apply (dualDistribEquiv K (K ⊗[k] H)).injective
  ext x y
  exact h x y

private theorem baseChangeLinearEquiv_one :
    baseChangeLinearEquiv (k := k) (K := K) (H := H)
      (1 ⊗ₜ[k] (1 : ConvolutionDual k H)) = 1 := by
  apply ofConv_ext
  intro x
  rw [baseChangeLinearEquiv_tmul_apply_tmul]
  simp only [LinearMap.convOne_apply, TensorProduct.counit_tmul,
    Bialgebra.counit_one, Algebra.algebraMap_self_apply, Algebra.smul_def, mul_one, one_mul]

private theorem baseChangeLinearEquiv_mul (a b : K) (φ ψ : ConvolutionDual k H) :
    baseChangeLinearEquiv (k := k) (K := K) (H := H)
        ((a * b) ⊗ₜ[k] (φ * ψ)) =
      baseChangeLinearEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ) *
        baseChangeLinearEquiv (k := k) (K := K) (H := H) (b ⊗ₜ[k] ψ) := by
  apply ofConv_ext
  intro x
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
    baseChangeLinearEquiv_mul baseChangeLinearEquiv_one

private theorem baseChangeAlgEquiv_apply (z : K ⊗[k] ConvolutionDual k H) :
    baseChangeAlgEquiv (k := k) (K := K) (H := H) z =
      baseChangeLinearEquiv (k := k) (K := K) (H := H) z := by
  rw [baseChangeAlgEquiv,
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply]

@[simp]
private theorem baseChangeAlgEquiv_tmul_apply_tmul
    (a b : K) (φ : ConvolutionDual k H) (x : H) :
    (baseChangeAlgEquiv (k := k) (K := K) (H := H) (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) := by
  rw [baseChangeAlgEquiv_apply]
  exact baseChangeLinearEquiv_tmul_apply_tmul a b φ x

/-- The base-change algebra equivalence preserves the finite-dual counit. -/
private theorem baseChangeAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (ConvolutionDual K (K ⊗[k] H))).comp
        (baseChangeAlgEquiv (k := k) (K := K) (H := H)).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[k] ConvolutionDual k H) := by
  apply AlgHom.ext (R := K) (A := K ⊗[k] ConvolutionDual k H) (B := K)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a φ =>
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
      rw [AlgEquiv.coe_toAlgHom, baseChangeAlgEquiv_apply]
      rw [ConvolutionDual.counit_apply]
      rw [show (1 : K ⊗[k] H) = 1 ⊗ₜ[k] 1 from Algebra.TensorProduct.one_def]
      rw [baseChangeLinearEquiv_tmul_apply_tmul]
      simp only [TensorProduct.counit_tmul, ConvolutionDual.counit_apply,
        CommSemiring.counit_apply, Algebra.smul_def, mul_one, mul_comm]

/-- The base-change algebra equivalence preserves the finite-dual comultiplication. -/
private theorem baseChangeAlgEquiv_map_comp_comul :
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
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
      apply dualDistribEquiv_ext
      intro x y
      rw [ConvolutionDual.dualDistribEquiv_comul_apply]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [AlgEquiv.coe_toAlgHom, baseChangeAlgEquiv_tmul_apply_tmul]
      rw [← ConvolutionDual.dualDistribEquiv_comul_apply k H φ x y]
      simp only [TensorProduct.comul_tmul]
      have comul_self : Coalgebra.comul (R := K) a = a ⊗ₜ[K] 1 :=
        calc
          Coalgebra.comul (R := K) a = 1 ⊗ₜ[K] a := CommSemiring.comul_apply K a
          _ = 1 ⊗ₜ[K] (a • (1 : K)) := by rw [smul_eq_mul, mul_one]
          _ = (a • (1 : K)) ⊗ₜ[K] 1 := TensorProduct.tmul_smul _ _ _
          _ = a ⊗ₜ[K] 1 := by
            rw [smul_eq_mul, mul_one]
      generalize Coalgebra.comul (R := k) (A := ConvolutionDual k H) φ = q
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q r hq hr =>
          simp only [TensorProduct.tmul_add, map_add, hq, hr,
            LinearMap.add_apply, mul_add]
      | tmul ψ χ =>
          simp only [comul_self,
            TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
            Algebra.TensorProduct.map_tmul,
            ConvolutionDual.dualDistribEquiv_tmul_apply,
            AlgEquiv.coe_toAlgHom, baseChangeAlgEquiv_tmul_apply_tmul, map_mul]
          ring

/-- Finite dualization commutes with extension of scalars for finite projective bialgebras. -/
noncomputable def baseChangeBialgEquiv (k : Type u) (K : Type v) (H : Type w)
    [CommRing k] [CommRing K] [Algebra k K]
    [Semiring H] [Bialgebra k H]
    [Module.Finite k H] [Module.Projective k H] :
    K ⊗[k] ConvolutionDual k H ≃ₐc[K] ConvolutionDual K (K ⊗[k] H) :=
  BialgEquiv.ofAlgEquiv
    (R := K) (A := K ⊗[k] ConvolutionDual k H)
    (B := ConvolutionDual K (K ⊗[k] H))
    (baseChangeAlgEquiv (k := k) (K := K) (H := H))
    baseChangeAlgEquiv_counit_comp baseChangeAlgEquiv_map_comp_comul

/-- The base-change equivalence evaluates pure tensors by scalar-extended evaluation. -/
@[simp, grind =]
theorem baseChangeBialgEquiv_tmul_apply_tmul (a b : K)
    (φ : ConvolutionDual k H) (x : H) :
    (baseChangeBialgEquiv k K H (a ⊗ₜ[k] φ)).ofConv
        (b ⊗ₜ[k] x) = a * b * algebraMap k K (φ.ofConv x) := by
  rw [baseChangeBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact baseChangeAlgEquiv_tmul_apply_tmul a b φ x

/-- The finite-dual base-change equivalence is natural in finite projective bialgebras. -/
theorem baseChangeBialgEquiv_naturality {H' : Type x} [Semiring H'] [Bialgebra k H']
    [Module.Finite k H'] [Module.Projective k H'] (f : H →ₐc[k] H') :
    (map K (Bialgebra.TensorProduct.map (BialgHom.id K K) f)).comp
        (baseChangeBialgEquiv k K H') =
      (baseChangeBialgEquiv k K H :
        K ⊗[k] ConvolutionDual k H →ₐc[K] ConvolutionDual K (K ⊗[k] H)).comp
        (Bialgebra.TensorProduct.map (BialgHom.id K K) (map k f)) := by
  ext z x
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simpa only [map_add, WithConv.ofConv_add,
        TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.restrictScalars_apply, LinearMap.add_apply] using
        congrArg₂ (fun a b => a + b) hz hw
  | tmul a φ => simp

end TauCeti.ConvolutionDual
