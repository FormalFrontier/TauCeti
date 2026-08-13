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

* `TauCeti.FiniteDual`: the convolution algebra on the linear dual.
* `TauCeti.FiniteDual.instBialgebra`: the bialgebra obtained by transposing multiplication and
  unit.
* `TauCeti.FiniteDual.instHopfAlgebra`: the Hopf structure obtained by transposing the antipode.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe u v

/-- The finite dual of a coalgebra, carrying the convolution algebra structure.

The `WithConv` wrapper selects Mathlib's convolution multiplication on linear maps. -/
abbrev FiniteDual (k : Type u) (H : Type v) [Field k] [AddCommMonoid H] [Module k H] :=
  WithConv (Module.Dual k H)

namespace FiniteDual

variable (k : Type u) (H : Type v) [Field k] [Ring H] [Bialgebra k H]
  [FiniteDimensional k H]

/-- Forget the convolution wrappers on both factors of a tensor of finite-dual elements. -/
private noncomputable def tensorUnwrap :
    FiniteDual k H ⊗[k] FiniteDual k H ≃ₗ[k]
      Module.Dual k H ⊗[k] Module.Dual k H :=
  TensorProduct.congr (WithConv.linearEquiv k _) (WithConv.linearEquiv k _)

/-- A tensor of finite-dual functionals is equivalently a functional on the tensor square. -/
noncomputable def evalTensorEquiv :
    FiniteDual k H ⊗[k] FiniteDual k H ≃ₗ[k] Module.Dual k (H ⊗[k] H) :=
  (tensorUnwrap k H).trans (TensorProduct.dualDistribEquiv k H H)

/-- The comultiplication on the finite dual, obtained by transposing multiplication on `H`. -/
noncomputable def comul : FiniteDual k H →ₗ[k] FiniteDual k H ⊗[k] FiniteDual k H :=
  (evalTensorEquiv k H).symm.toLinearMap ∘ₗ
      LinearMap.lcomp k k (LinearMap.mul' k H) ∘ₗ
        (WithConv.linearEquiv k _).toLinearMap

/-- The counit on the finite dual is evaluation at the unit of `H`. -/
def counit : FiniteDual k H →ₗ[k] k :=
  LinearMap.applyₗ (1 : H) ∘ₗ (WithConv.linearEquiv k _).toLinearMap

/-- Evaluating the transposed comultiplication on `x tensor y` gives `phi (x * y)`. -/
@[simp]
theorem evalTensor_comul (phi : FiniteDual k H) :
    evalTensorEquiv k H (comul k H phi) =
      phi.ofConv.comp (LinearMap.mul' k H) := by
  simp only [comul, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_toLinearMap]
  let psi : Module.Dual k (H ⊗[k] H) :=
    phi.ofConv.comp (LinearMap.mul' k H)
  simpa only [psi, LinearMap.lcomp_apply', WithConv.linearEquiv_apply]
    using (evalTensorEquiv k H).apply_symm_apply psi

/-- A pure tensor of finite-dual functionals evaluates componentwise. -/
@[simp]
theorem evalTensor_tmul_apply (phi psi : FiniteDual k H) (x y : H) :
    evalTensorEquiv k H (phi ⊗ₜ[k] psi) (x ⊗ₜ[k] y) =
      phi.ofConv x * psi.ofConv y := by
  simp [evalTensorEquiv, tensorUnwrap]

/-- Pointwise form of the characteristic equation for the finite-dual comultiplication. -/
theorem evalTensor_comul_apply (phi : FiniteDual k H) (x y : H) :
    evalTensorEquiv k H (comul k H phi) (x ⊗ₜ[k] y) =
      phi.ofConv (x * y) := by
  rw [evalTensor_comul]
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply]

omit [FiniteDimensional k H] in
/-- The finite-dual counit is evaluation at one. -/
@[simp]
theorem counit_apply (phi : FiniteDual k H) : counit k H phi = phi.ofConv 1 :=
  by simp [counit]

/-- Evaluate three finite-dual functionals on a right-associated triple tensor. -/
private noncomputable def evalTripleEquiv :
    FiniteDual k H ⊗[k] (FiniteDual k H ⊗[k] FiniteDual k H) ≃ₗ[k]
      Module.Dual k (H ⊗[k] (H ⊗[k] H)) :=
  (TensorProduct.congr (WithConv.linearEquiv k _) (evalTensorEquiv k H)).trans
    (TensorProduct.dualDistribEquiv k H (H ⊗[k] H))

private theorem evalTripleEquiv_tmul_tmul_apply
    (phi psi chi : FiniteDual k H) (x y z : H) :
    evalTripleEquiv k H (phi ⊗ₜ[k] (psi ⊗ₜ[k] chi)) (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      phi.ofConv x * (psi.ofConv y * chi.ofConv z) := by
  simp [evalTripleEquiv, evalTensorEquiv, tensorUnwrap]

private theorem evalTripleEquiv_tmul_apply
    (phi : FiniteDual k H) (w : FiniteDual k H ⊗[k] FiniteDual k H) (x y z : H) :
    evalTripleEquiv k H (phi ⊗ₜ[k] w) (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      phi.ofConv x * evalTensorEquiv k H w (y ⊗ₜ[k] z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, mul_add]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul psi chi => rw [evalTripleEquiv_tmul_tmul_apply, evalTensor_tmul_apply]

private theorem evalTripleEquiv_assoc_tmul_apply
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (chi : FiniteDual k H) (x y z : H) :
    evalTripleEquiv k H ((TensorProduct.assoc k _ _ _).toLinearMap (w ⊗ₜ[k] chi))
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      evalTensorEquiv k H w (x ⊗ₜ[k] y) * chi.ofConv z := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, add_mul]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearEquiv.coe_toLinearMap, TensorProduct.assoc_tmul,
        evalTripleEquiv_tmul_tmul_apply, evalTensor_tmul_apply, mul_assoc]

private theorem evalTriple_assoc_comul_rTensor
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x y z : H) :
    evalTripleEquiv k H
        ((TensorProduct.assoc k _ _ _).toLinearMap ((comul k H).rTensor _ w))
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      evalTensorEquiv k H w ((x * y) ⊗ₜ[k] z) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.rTensor_tmul, evalTripleEquiv_assoc_tmul_apply,
        evalTensor_comul_apply, evalTensor_tmul_apply]

private theorem evalTriple_comul_lTensor
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x y z : H) :
    evalTripleEquiv k H ((comul k H).lTensor _ w)
        (x ⊗ₜ[k] (y ⊗ₜ[k] z)) =
      evalTensorEquiv k H w (x ⊗ₜ[k] (y * z)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.lTensor_tmul, evalTripleEquiv_tmul_apply,
        evalTensor_comul_apply, evalTensor_tmul_apply]

private theorem lid_counit_rTensor_apply
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x : H) :
    ((TensorProduct.lid k (FiniteDual k H)) ((counit k H).rTensor _ w)).ofConv x =
      evalTensorEquiv k H w ((1 : H) ⊗ₜ[k] x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, WithConv.ofConv_add, LinearMap.add_apply]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, evalTensor_tmul_apply,
        WithConv.ofConv_smul, LinearMap.smul_apply, counit_apply]
      simp only [smul_eq_mul]

private theorem rid_counit_lTensor_apply
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x : H) :
    ((TensorProduct.rid k (FiniteDual k H)) ((counit k H).lTensor _ w)).ofConv x =
      evalTensorEquiv k H w (x ⊗ₜ[k] (1 : H)) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, WithConv.ofConv_add, LinearMap.add_apply]
        using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, evalTensor_tmul_apply,
        WithConv.ofConv_smul, LinearMap.smul_apply, counit_apply]
      simp only [smul_eq_mul, mul_comm]

/-- The coalgebra structure on the finite dual, obtained by transposing multiplication and unit
on the original bialgebra. -/
noncomputable instance instCoalgebra : Coalgebra k (FiniteDual k H) where
  comul := comul k H
  counit := counit k H
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
            rw [evalTriple_assoc_comul_rTensor, evalTriple_comul_lTensor,
              evalTensor_comul_apply, evalTensor_comul_apply]
            simp only [mul_assoc]
  rTensor_counit_comp_comul := by
    ext phi
    apply (TensorProduct.lid k (FiniteDual k H)).injective
    apply WithConv.ofConv_injective
    ext x
    rw [LinearMap.comp_apply, lid_counit_rTensor_apply, evalTensor_comul_apply]
    simp only [one_mul, TensorProduct.lid_tmul, TensorProduct.mk_apply, one_smul]
  lTensor_counit_comp_comul := by
    ext phi
    apply (TensorProduct.rid k (FiniteDual k H)).injective
    apply WithConv.ofConv_injective
    ext x
    rw [LinearMap.comp_apply, rid_counit_lTensor_apply, evalTensor_comul_apply]
    simp only [mul_one, TensorProduct.rid_tmul, LinearMap.flip_apply,
      TensorProduct.mk_apply, one_smul]

/-- `evalTensorEquiv` packaged in the convolution algebra on functionals on the tensor square. -/
private noncomputable def evalTensorConv :
    FiniteDual k H ⊗[k] FiniteDual k H →ₗ[k]
      WithConv (Module.Dual k (H ⊗[k] H)) :=
  (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ (evalTensorEquiv k H).toLinearMap

private theorem evalTensorConv_tmul (phi psi : FiniteDual k H) :
    evalTensorConv k H (phi ⊗ₜ[k] psi) = LinearMap.mulTensor phi psi := by
  apply WithConv.ofConv_injective
  apply TensorProduct.ext'
  intro x y
  simp [evalTensorConv]

private theorem evalTensorConv_mul
    (w z : FiniteDual k H ⊗[k] FiniteDual k H) :
    evalTensorConv k H (w * z) = evalTensorConv k H w * evalTensorConv k H z := by
  apply LinearMap.map_mul_of_map_mul_tmul
  intro phi chi psi omega
  rw [evalTensorConv_tmul, evalTensorConv_tmul, evalTensorConv_tmul,
    LinearMap.mulTensor_convMul]

private theorem evalTensorConv_comul (phi : FiniteDual k H) :
    evalTensorConv k H (comul k H phi) =
      WithConv.toConv (phi.ofConv.comp (LinearMap.mul' k H)) := by
  apply WithConv.ofConv_injective
  exact evalTensor_comul k H phi

@[simp]
private theorem evalTensorConv_ofConv (w : FiniteDual k H ⊗[k] FiniteDual k H) :
    (evalTensorConv k H w).ofConv = evalTensorEquiv k H w :=
  rfl

omit [FiniteDimensional k H] in
private theorem mulCoalgHom_toLinearMap :
    (Bialgebra.mulCoalgHom k H).toLinearMap = LinearMap.mul' k H :=
  rfl

/-- The bialgebra structure on the finite dual. Multiplication is convolution and the coalgebra
operations are transposes of multiplication and unit on the original bialgebra. -/
noncomputable instance instBialgebra : Bialgebra k (FiniteDual k H) :=
  Bialgebra.mk' k (FiniteDual k H)
    (by
      change counit k H (1 : FiniteDual k H) = 1
      rw [counit_apply]
      rw [LinearMap.convOne_apply, Bialgebra.counit_one, map_one])
    (fun {phi psi} ↦ by
      change counit k H (phi * psi) = counit k H phi * counit k H psi
      rw [counit_apply, counit_apply, counit_apply, LinearMap.convMul_apply,
        Bialgebra.comul_one, Algebra.TensorProduct.one_def, TensorProduct.map_tmul,
        LinearMap.mul'_apply])
    (by
      change comul k H (1 : FiniteDual k H) = 1
      apply (evalTensorEquiv k H).injective
      apply LinearMap.ext
      intro xy
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | add xy₁ xy₂ hxy₁ hxy₂ =>
          simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hxy₁ hxy₂
      | tmul x y =>
          rw [evalTensor_comul_apply]
          simp only [LinearMap.convOne_apply, Bialgebra.counit_mul, map_mul]
          rw [Algebra.TensorProduct.one_def, evalTensor_tmul_apply]
          simp only [LinearMap.convOne_apply])
    (fun {phi psi} ↦ by
      change comul k H (phi * psi) = comul k H phi * comul k H psi
      apply (evalTensorEquiv k H).injective
      rw [← evalTensorConv_ofConv, ← evalTensorConv_ofConv, evalTensorConv_mul,
        evalTensorConv_comul, evalTensorConv_comul, evalTensorConv_comul]
      have h := LinearMap.convMul_comp_coalgHom_distrib phi psi (Bialgebra.mulCoalgHom k H)
      rw [mulCoalgHom_toLinearMap] at h
      simpa only [WithConv.toConv_ofConv] using h)

end FiniteDual

namespace FiniteDual

variable (k : Type u) (H : Type v) [Field k] [CommRing H] [Bialgebra k H]
  [FiniteDimensional k H]

private theorem evalTensor_comm_apply
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x y : H) :
    evalTensorEquiv k H (TensorProduct.comm k _ _ w) (x ⊗ₜ[k] y) =
      evalTensorEquiv k H w (y ⊗ₜ[k] x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w₁ w₂ hw₁ hw₂ =>
      simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw₁ hw₂
  | tmul phi psi =>
      rw [TensorProduct.comm_tmul, evalTensor_tmul_apply, evalTensor_tmul_apply, mul_comm]

/-- The coalgebra underlying the finite dual is cocommutative. -/
noncomputable instance instIsCocomm : Coalgebra.IsCocomm k (FiniteDual k H) where
  comm_comp_comul := by
    change (TensorProduct.comm k (FiniteDual k H) (FiniteDual k H)).toLinearMap ∘ₗ
      comul k H = comul k H
    ext phi
    apply (evalTensorEquiv k H).injective
    apply LinearMap.ext
    intro xy
    induction xy using TensorProduct.induction_on with
    | zero => simp
    | add xy₁ xy₂ hxy₁ hxy₂ =>
        simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hxy₁ hxy₂
    | tmul x y =>
        simp only [LinearMap.comp_apply]
        rw [LinearEquiv.coe_toLinearMap]
        rw [evalTensor_comm_apply, evalTensor_comul_apply, evalTensor_comul_apply]
        simp only [mul_comm]

end FiniteDual

namespace FiniteDual

section HopfAlgebra

variable (k : Type u) (H : Type v) [Field k] [Ring H] [HopfAlgebra k H]
  [FiniteDimensional k H]

/-- The antipode on the finite dual is precomposition with the antipode of `H`. -/
noncomputable def antipode : FiniteDual k H →ₗ[k] FiniteDual k H :=
  (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ
    LinearMap.lcomp k k (HopfAlgebra.antipode k (A := H)) ∘ₗ
      (WithConv.linearEquiv k _).toLinearMap

omit [FiniteDimensional k H] in
/-- The finite-dual antipode acts by precomposition. -/
@[simp]
theorem antipode_apply (phi : FiniteDual k H) (x : H) :
    (antipode k H phi).ofConv x = phi.ofConv (HopfAlgebra.antipode k x) :=
  by simp [antipode]

@[simp]
private theorem coalgebra_comul_eq_comul (phi : FiniteDual k H) :
    Coalgebra.comul (R := k) (A := FiniteDual k H) phi = comul k H phi :=
  rfl

@[simp]
private theorem coalgebra_counit_eq_counit (phi : FiniteDual k H) :
    Coalgebra.counit (R := k) (A := FiniteDual k H) phi = counit k H phi :=
  rfl

private theorem mul_apply_eq_evalTensorEquiv
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (x : H) :
    (LinearMap.mul' k (FiniteDual k H) w).ofConv x =
      evalTensorEquiv k H w (Coalgebra.comul x) := by
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
      | tmul y z => rw [TensorProduct.map_tmul, LinearMap.mul'_apply, evalTensor_tmul_apply]

private theorem evalTensor_map_antipode_left
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (z : H ⊗[k] H) :
    evalTensorEquiv k H
        (TensorProduct.map (antipode k H) LinearMap.id w) z =
      evalTensorEquiv k H w
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
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul, evalTensor_tmul_apply,
            evalTensor_tmul_apply, antipode_apply]
          rfl

private theorem evalTensor_map_antipode_right
    (w : FiniteDual k H ⊗[k] FiniteDual k H) (z : H ⊗[k] H) :
    evalTensorEquiv k H
        (TensorProduct.map LinearMap.id (antipode k H) w) z =
      evalTensorEquiv k H w
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
          rw [TensorProduct.map_tmul, TensorProduct.map_tmul, evalTensor_tmul_apply,
            evalTensor_tmul_apply, antipode_apply]
          rfl

/-- The Hopf algebra structure on the finite dual. Its antipode is precomposition with the
antipode of the original finite-dimensional Hopf algebra. -/
noncomputable instance instHopfAlgebra : HopfAlgebra k (FiniteDual k H) :=
  HopfAlgebra.ofConvInverse (antipode k H)
    (by
      apply WithConv.ofConv_injective
      ext phi x
      rw [LinearMap.convMul_apply, mul_apply_eq_evalTensorEquiv,
        evalTensor_map_antipode_left]
      rw [coalgebra_comul_eq_comul, evalTensor_comul]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.rTensor_def, HopfAlgebra.mul_antipode_rTensor_comul_apply]
      rw [LinearMap.convOne_apply, coalgebra_counit_eq_counit, counit_apply,
        LinearMap.convAlgebraMap_apply,
        Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul, Algebra.algebraMap_self_apply]
      rw [mul_comm])
    (by
      apply WithConv.ofConv_injective
      ext phi x
      rw [LinearMap.convMul_apply, mul_apply_eq_evalTensorEquiv,
        evalTensor_map_antipode_right]
      rw [coalgebra_comul_eq_comul, evalTensor_comul]
      simp only [LinearMap.comp_apply]
      rw [← LinearMap.lTensor_def, HopfAlgebra.mul_antipode_lTensor_comul_apply]
      rw [LinearMap.convOne_apply, coalgebra_counit_eq_counit, counit_apply,
        LinearMap.convAlgebraMap_apply,
        Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul, Algebra.algebraMap_self_apply]
      rw [mul_comm])

end HopfAlgebra

end FiniteDual

end TauCeti
