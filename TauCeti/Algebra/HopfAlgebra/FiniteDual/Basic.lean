/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# The finite dual of a Hopf algebra

For a finite-dimensional bialgebra `H` over a field `k`, the linear dual carries the transposed
bialgebra structure. Its multiplication is convolution, while its comultiplication and counit are
characterized by

```text
Delta(phi)(x tensor y) = phi (x * y),        epsilon(phi) = phi(1).
```

If `H` is a Hopf algebra, precomposition with its antipode is the antipode of the dual. This is
the algebraic construction underlying Cartier duality for finite group schemes. The present file
builds the finite-dimensional Hopf dual over a field; the scheme-level duality and the extension
to finite locally free Hopf algebras over a general base remain separate steps.

## Main declarations

* `TauCeti.ConvolutionDual`: the convolution algebra on the linear dual.
* `TauCeti.ConvolutionDual.instBialgebra`: the bialgebra obtained by transposing multiplication and
  unit.
* `TauCeti.ConvolutionDual.instHopfAlgebra`: the Hopf structure obtained by transposing the
  antipode.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-- The linear dual, wrapped to select convolution multiplication when a coalgebra structure is
available.

The `WithConv` wrapper selects Mathlib's convolution multiplication on linear maps. -/
abbrev ConvolutionDual (k : Type u) (H : Type v) [CommSemiring k] [AddCommMonoid H] [Module k H] :=
  WithConv (Module.Dual k H)

namespace ConvolutionDual

/-- The convolution dual of a finite-dimensional vector space is finite-dimensional. -/
noncomputable instance instFiniteDimensional (k : Type u) (H : Type v) [Field k]
    [AddCommGroup H] [Module k H] [FiniteDimensional k H] :
    FiniteDimensional k (ConvolutionDual k H) :=
  LinearEquiv.finiteDimensional (WithConv.linearEquiv k (Module.Dual k H)).symm

section LinearAlgebra

variable (k : Type u) (H : Type v) [Field k] [AddCommGroup H] [Module k H]
  [FiniteDimensional k H]

/-- Forget the convolution wrappers on both factors of a tensor of finite-dual elements. -/
private noncomputable def tensorUnwrap :
    ConvolutionDual k H ⊗[k] ConvolutionDual k H ≃ₗ[k]
      Module.Dual k H ⊗[k] Module.Dual k H :=
  TensorProduct.congr (WithConv.linearEquiv k _) (WithConv.linearEquiv k _)

/-- A tensor of finite-dual functionals is equivalently a functional on the tensor square. -/
noncomputable def dualDistribEquiv :
    ConvolutionDual k H ⊗[k] ConvolutionDual k H ≃ₗ[k] Module.Dual k (H ⊗[k] H) :=
  (tensorUnwrap k H).trans (TensorProduct.dualDistribEquiv k H H)

private theorem dualDistribEquiv_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (z : H ⊗[k] H) :
    dualDistribEquiv k H w z =
      TensorProduct.dualDistrib k H H ((tensorUnwrap k H) w) z :=
  rfl

end LinearAlgebra

section Coalgebra

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Algebra k H]
  [FiniteDimensional k H]

/-- The comultiplication and counit on the finite dual, obtained by transposing multiplication
and unit on the original algebra. -/
noncomputable instance instCoalgebraStruct : CoalgebraStruct k (ConvolutionDual k H) where
  comul := (dualDistribEquiv k H).symm.toLinearMap ∘ₗ
    (LinearMap.mul' k H).dualMap ∘ₗ (WithConv.linearEquiv k _).toLinearMap
  counit := LinearMap.applyₗ (1 : H) ∘ₗ (WithConv.linearEquiv k _).toLinearMap

private theorem dualDistribEquiv_comul' (phi : ConvolutionDual k H) :
    dualDistribEquiv k H (Coalgebra.comul phi) =
      phi.ofConv.comp (LinearMap.mul' k H) := by
  dsimp only [CoalgebraStruct.comul, instCoalgebraStruct, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  let psi : Module.Dual k (H ⊗[k] H) :=
    phi.ofConv.comp (LinearMap.mul' k H)
  simpa only [psi, LinearMap.dualMap_apply', WithConv.linearEquiv_apply]
    using (dualDistribEquiv k H).apply_symm_apply psi

/-- A pure tensor of finite-dual functionals evaluates componentwise. -/
@[simp, grind =]
theorem dualDistribEquiv_tmul_apply (phi psi : ConvolutionDual k H) (x y : H) :
    dualDistribEquiv k H (phi ⊗ₜ[k] psi) (x ⊗ₜ[k] y) =
      phi.ofConv x * psi.ofConv y := by
  simp [dualDistribEquiv, tensorUnwrap]

private theorem dualDistribEquiv_comul_apply' (phi : ConvolutionDual k H) (x y : H) :
    dualDistribEquiv k H (Coalgebra.comul phi) (x ⊗ₜ[k] y) =
      phi.ofConv (x * y) := by
  rw [dualDistribEquiv_comul']
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply]

private theorem counit_apply' (phi : ConvolutionDual k H) :
    Coalgebra.counit (R := k) phi = phi.ofConv 1 := by
  simp [CoalgebraStruct.counit]

/-- Evaluate three finite-dual functionals on a right-associated triple tensor. -/
private noncomputable def evalTripleEquiv :
    ConvolutionDual k H ⊗[k] (ConvolutionDual k H ⊗[k] ConvolutionDual k H) ≃ₗ[k]
      Module.Dual k (H ⊗[k] (H ⊗[k] H)) :=
  (TensorProduct.congr (WithConv.linearEquiv k _) (dualDistribEquiv k H)).trans
    (TensorProduct.dualDistribEquiv k H (H ⊗[k] H))

private theorem evalTripleEquiv_tmul_tmul_apply
    (phi psi chi : ConvolutionDual k H) (x y z : H) :
    evalTripleEquiv k H (phi ⊗ₜ[k] (psi ⊗ₜ[k] chi)) (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      phi.ofConv x * (psi.ofConv y * chi.ofConv z) := by
  simp [evalTripleEquiv, dualDistribEquiv, tensorUnwrap]

private theorem evalTripleEquiv_tmul_apply
    (phi : ConvolutionDual k H) (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x y z : H) :
    evalTripleEquiv k H (phi ⊗ₜ[k] w) (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      phi.ofConv x * dualDistribEquiv k H w (y ⊗ₜ[k] z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, mul_add]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul psi chi => rw [evalTripleEquiv_tmul_tmul_apply, dualDistribEquiv_tmul_apply]

private theorem evalTripleEquiv_assoc_tmul_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (chi : ConvolutionDual k H) (x y z : H) :
    evalTripleEquiv k H ((TensorProduct.assoc k _ _ _).toLinearMap (w ⊗ₜ[k] chi))
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      dualDistribEquiv k H w (x ⊗ₜ[k] y) * chi.ofConv z := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul,
        evalTripleEquiv_tmul_tmul_apply, dualDistribEquiv_tmul_apply, mul_assoc]

private theorem evalTripleEquiv_assoc_comul_rTensor_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x y z : H) :
    evalTripleEquiv k H
        ((TensorProduct.assoc k _ _ _).toLinearMap
          ((Coalgebra.comul (R := k) (A := ConvolutionDual k H)).rTensor _ w))
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      dualDistribEquiv k H w ((x * y) ⊗ₜ[k] z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.rTensor_tmul, evalTripleEquiv_assoc_tmul_apply,
        dualDistribEquiv_comul_apply', dualDistribEquiv_tmul_apply]

private theorem evalTripleEquiv_comul_lTensor_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x y z : H) :
    evalTripleEquiv k H
        ((Coalgebra.comul (R := k) (A := ConvolutionDual k H)).lTensor _ w)
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      dualDistribEquiv k H w (x ⊗ₜ[k] (y * z)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.lTensor_tmul, evalTripleEquiv_tmul_apply,
        dualDistribEquiv_comul_apply', dualDistribEquiv_tmul_apply]

private theorem lid_counit_rTensor_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x : H) :
    ((TensorProduct.lid k (ConvolutionDual k H))
        ((Coalgebra.counit (R := k) (A := ConvolutionDual k H)).rTensor _ w)).ofConv x =
      dualDistribEquiv k H w ((1 : H) ⊗ₜ[k] x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, WithConv.ofConv_add, LinearMap.add_apply]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, dualDistribEquiv_tmul_apply,
        WithConv.ofConv_smul, LinearMap.smul_apply, counit_apply']
      simp only [smul_eq_mul]

private theorem rid_counit_lTensor_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x : H) :
    ((TensorProduct.rid k (ConvolutionDual k H))
        ((Coalgebra.counit (R := k) (A := ConvolutionDual k H)).lTensor _ w)).ofConv x =
      dualDistribEquiv k H w (x ⊗ₜ[k] (1 : H)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, WithConv.ofConv_add, LinearMap.add_apply]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, dualDistribEquiv_tmul_apply,
        WithConv.ofConv_smul, LinearMap.smul_apply, counit_apply']
      simp only [smul_eq_mul, mul_comm]

/-- The coalgebra structure on the finite dual, obtained by transposing multiplication and unit
on the original bialgebra. -/
noncomputable instance instCoalgebra : Coalgebra k (ConvolutionDual k H) where
  coassoc := by
    ext phi
    apply (evalTripleEquiv k H).injective
    apply LinearMap.ext
    intro xyz
    induction xyz using TensorProduct.induction_on with
    | zero => simp
    | add xyz₁ xyz₂ hxyz₁ hxyz₂ =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hxyz₁ hxyz₂
    | tmul x yz =>
        induction yz using TensorProduct.induction_on with
        | zero => simp
        | add yz₁ yz₂ hyz₁ hyz₂ =>
            simpa only [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
              using congrArg₂ (· + ·) hyz₁ hyz₂
        | tmul y z =>
            simp only [LinearMap.comp_apply]
            rw [evalTripleEquiv_assoc_comul_rTensor_apply, evalTripleEquiv_comul_lTensor_apply,
              dualDistribEquiv_comul_apply', dualDistribEquiv_comul_apply']
            simp only [mul_assoc]
  rTensor_counit_comp_comul := by
    ext phi
    apply (TensorProduct.lid k (ConvolutionDual k H)).injective
    apply WithConv.ofConv_injective
    ext x
    rw [LinearMap.comp_apply, lid_counit_rTensor_apply, dualDistribEquiv_comul_apply']
    simp only [one_mul, TensorProduct.lid_tmul, TensorProduct.mk_apply, one_smul]
  lTensor_counit_comp_comul := by
    ext phi
    apply (TensorProduct.rid k (ConvolutionDual k H)).injective
    apply WithConv.ofConv_injective
    ext x
    rw [LinearMap.comp_apply, rid_counit_lTensor_apply, dualDistribEquiv_comul_apply']
    simp only [mul_one, TensorProduct.rid_tmul, LinearMap.flip_apply,
      TensorProduct.mk_apply, one_smul]

/-- Evaluating the finite-dual comultiplication gives the transpose of multiplication on `H`. -/
@[simp, grind =]
theorem dualDistribEquiv_comul (phi : ConvolutionDual k H) :
    dualDistribEquiv k H (Coalgebra.comul phi) =
      phi.ofConv.comp (LinearMap.mul' k H) :=
  dualDistribEquiv_comul' k H phi

/-- Pointwise form of the characteristic equation for the finite-dual comultiplication. -/
@[grind =]
theorem dualDistribEquiv_comul_apply (phi : ConvolutionDual k H) (x y : H) :
    dualDistribEquiv k H (Coalgebra.comul phi) (x ⊗ₜ[k] y) =
      phi.ofConv (x * y) :=
  dualDistribEquiv_comul_apply' k H phi x y

/-- The finite-dual counit is evaluation at one. -/
@[simp, grind =]
theorem counit_apply (phi : ConvolutionDual k H) :
    Coalgebra.counit (R := k) phi = phi.ofConv 1 :=
  counit_apply' k H phi

end Coalgebra

section Bialgebra

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Bialgebra k H]
  [FiniteDimensional k H]

/-- `dualDistribEquiv` packaged in the convolution algebra on functionals on the tensor square. -/
private noncomputable def evalTensorConv :
    ConvolutionDual k H ⊗[k] ConvolutionDual k H →ₗ[k]
      WithConv (Module.Dual k (H ⊗[k] H)) :=
  (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ (dualDistribEquiv k H).toLinearMap

private theorem evalTensorConv_tmul (phi psi : ConvolutionDual k H) :
    evalTensorConv k H (phi ⊗ₜ[k] psi) = LinearMap.mulTensor phi psi := by
  apply WithConv.ofConv_injective
  apply TensorProduct.ext'
  intro x y
  simp [evalTensorConv]

private theorem evalTensorConv_mul
    (w z : ConvolutionDual k H ⊗[k] ConvolutionDual k H) :
    evalTensorConv k H (w * z) = evalTensorConv k H w * evalTensorConv k H z := by
  apply LinearMap.map_mul_of_map_mul_tmul
  intro phi chi psi omega
  rw [evalTensorConv_tmul, evalTensorConv_tmul, evalTensorConv_tmul,
    LinearMap.mulTensor_convMul]

private theorem evalTensorConv_comul (phi : ConvolutionDual k H) :
    evalTensorConv k H (Coalgebra.comul phi) =
      WithConv.toConv (phi.ofConv.comp (LinearMap.mul' k H)) := by
  apply WithConv.ofConv_injective
  exact dualDistribEquiv_comul k H phi

@[simp]
private theorem evalTensorConv_ofConv (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) :
    (evalTensorConv k H w).ofConv = dualDistribEquiv k H w :=
  rfl

/-- The bialgebra structure on the finite dual. Multiplication is convolution and the coalgebra
operations are transposes of multiplication and unit on the original bialgebra. -/
noncomputable instance instBialgebra : Bialgebra k (ConvolutionDual k H) :=
  Bialgebra.mk' k (ConvolutionDual k H)
    (by
      rw [counit_apply]
      rw [LinearMap.convOne_apply, Bialgebra.counit_one, map_one])
    (fun {phi psi} ↦ by
      rw [counit_apply, counit_apply, counit_apply, LinearMap.convMul_apply,
        Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
        LinearMap.mul'_apply])
    (by
      apply (dualDistribEquiv k H).injective
      apply LinearMap.ext
      intro xy
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add xy₁ xy₂ hxy₁ hxy₂ =>
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hxy₁ hxy₂
      | tmul x y =>
          rw [dualDistribEquiv_comul_apply]
          simp only [LinearMap.convOne_apply, Bialgebra.counit_mul, map_mul]
          rw [Algebra.TensorProduct.one_def, dualDistribEquiv_tmul_apply]
          simp only [LinearMap.convOne_apply])
    (fun {phi psi} ↦ by
      apply (dualDistribEquiv k H).injective
      rw [← evalTensorConv_ofConv, ← evalTensorConv_ofConv, evalTensorConv_mul,
        evalTensorConv_comul, evalTensorConv_comul, evalTensorConv_comul]
      have h := LinearMap.convMul_comp_coalgHom_distrib phi psi (Bialgebra.mulCoalgHom k H)
      have hmul : (Bialgebra.mulCoalgHom k H).toLinearMap = LinearMap.mul' k H :=
        Bialgebra.toLinearMap_mulCoalgHom
      rw [hmul] at h
      simpa only [WithConv.toConv_ofConv] using h)

end Bialgebra

end ConvolutionDual

namespace ConvolutionDual

variable (k : Type u) (H : Type v) [Field k] [CommRing H] [Algebra k H]
  [FiniteDimensional k H]

private theorem dualDistribEquiv_comm_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x y : H) :
    dualDistribEquiv k H (TensorProduct.comm k _ _ w) (x ⊗ₜ[k] y) =
      dualDistribEquiv k H w (y ⊗ₜ[k] x) := by
  have hcomm :
      (tensorUnwrap k H) (TensorProduct.comm k _ _ w) =
        TensorProduct.comm k _ _ ((tensorUnwrap k H) w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w₁ w₂ hw₁ hw₂ => simpa only [map_add] using congrArg₂ (· + ·) hw₁ hw₂
    | tmul phi psi => simp [tensorUnwrap]
  rw [dualDistribEquiv_apply, dualDistribEquiv_apply, hcomm]
  exact (TensorProduct.dualDistrib_apply_comm ((tensorUnwrap k H) w) (x ⊗ₜ[k] y)).symm

/-- The coalgebra underlying the finite dual is cocommutative. -/
noncomputable instance instIsCocomm : Coalgebra.IsCocomm k (ConvolutionDual k H) where
  comm_comp_comul := by
    ext phi
    apply (dualDistribEquiv k H).injective
    apply LinearMap.ext
    intro xy
    induction xy using TensorProduct.induction_on with
    | zero => simp
    | add xy₁ xy₂ hxy₁ hxy₂ =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hxy₁ hxy₂
    | tmul x y =>
        simp only [LinearMap.comp_apply]
        rw [LinearEquiv.coe_toLinearMap]
        rw [dualDistribEquiv_comm_apply, dualDistribEquiv_comul_apply,
          dualDistribEquiv_comul_apply]
        simp only [mul_comm]

end ConvolutionDual

namespace ConvolutionDual

section HopfAlgebra

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
  [FiniteDimensional k H]

/-- The antipode operation on the finite dual, obtained by transposing the antipode of the
original Hopf algebra. -/
noncomputable instance instHopfAlgebraStruct :
    HopfAlgebraStruct k (ConvolutionDual k H) where
  antipode := (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ
      (HopfAlgebra.antipode k (A := H)).dualMap ∘ₗ
        (WithConv.linearEquiv k _).toLinearMap

private theorem antipode_apply' (phi : ConvolutionDual k H) (x : H) :
    (HopfAlgebra.antipode k (A := ConvolutionDual k H) phi).ofConv x =
      phi.ofConv (HopfAlgebra.antipode k x) := by
  simp [HopfAlgebraStruct.antipode]

private theorem ofConv_mul_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (x : H) :
    (LinearMap.mul' k (ConvolutionDual k H) w).ofConv x =
      dualDistribEquiv k H w (Coalgebra.comul x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, WithConv.ofConv_add, LinearMap.add_apply]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.mul'_apply]
      rw [LinearMap.convMul_apply]
      generalize Coalgebra.comul (R := k) (A := H) x = z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz₁ hz₂
      | tmul y z =>
          rw [TensorProduct.map_tmul, LinearMap.mul'_apply, dualDistribEquiv_tmul_apply]

private theorem dualDistribEquiv_map_antipode_left_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (z : H ⊗[k] H) :
    dualDistribEquiv k H
        (TensorProduct.map (HopfAlgebra.antipode k (A := ConvolutionDual k H))
          LinearMap.id w) z =
      dualDistribEquiv k H w
        (TensorProduct.map (HopfAlgebra.antipode k (A := H)) LinearMap.id z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz₁ hz₂
      | tmul x y =>
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul, dualDistribEquiv_tmul_apply,
            dualDistribEquiv_tmul_apply, antipode_apply']
          rfl

private theorem dualDistribEquiv_map_antipode_right_apply
    (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) (z : H ⊗[k] H) :
    dualDistribEquiv k H
        (TensorProduct.map LinearMap.id
          (HopfAlgebra.antipode k (A := ConvolutionDual k H)) w) z =
      dualDistribEquiv k H w
        (TensorProduct.map LinearMap.id (HopfAlgebra.antipode k (A := H)) z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hz₁ hz₂
      | tmul x y =>
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul, dualDistribEquiv_tmul_apply,
            dualDistribEquiv_tmul_apply, antipode_apply']
          rfl

/-- The Hopf algebra structure on the finite dual. Its antipode is precomposition with the
antipode of the original finite-dimensional Hopf algebra. -/
noncomputable instance instHopfAlgebra : HopfAlgebra k (ConvolutionDual k H) :=
  HopfAlgebra.ofConvInverse
    (HopfAlgebra.antipode k (A := ConvolutionDual k H))
    (by
      apply WithConv.ofConv_injective
      ext phi x
      rw [LinearMap.convMul_apply, ofConv_mul_apply, dualDistribEquiv_map_antipode_left_apply]
      rw [dualDistribEquiv_comul]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.rTensor_def, HopfAlgebra.mul_antipode_rTensor_comul_apply]
      rw [LinearMap.convOne_apply, counit_apply, LinearMap.convAlgebraMap_apply,
        Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul, Algebra.algebraMap_self_apply]
      rw [mul_comm])
    (by
      apply WithConv.ofConv_injective
      ext phi x
      rw [LinearMap.convMul_apply, ofConv_mul_apply, dualDistribEquiv_map_antipode_right_apply]
      rw [dualDistribEquiv_comul]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.lTensor_def, HopfAlgebra.mul_antipode_lTensor_comul_apply]
      rw [LinearMap.convOne_apply, counit_apply, LinearMap.convAlgebraMap_apply,
        Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul, Algebra.algebraMap_self_apply]
      rw [mul_comm])

/-- The finite-dual antipode acts by precomposition with the original antipode. -/
@[simp, grind =]
theorem antipode_apply (phi : ConvolutionDual k H) (x : H) :
    (HopfAlgebra.antipode k phi).ofConv x =
      phi.ofConv (HopfAlgebra.antipode k x) :=
  antipode_apply' k H phi x

end HopfAlgebra

end ConvolutionDual

end TauCeti
