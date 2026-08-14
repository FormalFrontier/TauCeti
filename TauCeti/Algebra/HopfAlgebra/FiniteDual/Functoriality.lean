/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic

/-!
# Functoriality and reflexivity of the finite Hopf dual

Dualizing a bialgebra morphism between finite-dimensional bialgebras gives a morphism in the
opposite direction between their convolution duals. Evaluation identifies a finite-dimensional
bialgebra with its double convolution dual, compatibly with multiplication, comultiplication,
unit, and counit.

These are algebraic functoriality and involutivity statements for the finite bialgebra dual
constructed in `TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic`. The scheme-level Cartier duality
and its finite locally free general-base form remain separate developments.

## Main declarations

* `TauCeti.ConvolutionDual.map`: the contravariant map on finite-dimensional bialgebras.
* `TauCeti.ConvolutionDual.map_id` and `TauCeti.ConvolutionDual.map_comp`: its functoriality laws.
* `TauCeti.ConvolutionDual.mapEquiv`: the contravariant equivalence induced by a bialgebra
  equivalence.
* `TauCeti.ConvolutionDual.evalBialgEquiv`: evaluation as a bialgebra equivalence with the double
  convolution dual.
* `TauCeti.ConvolutionDual.evalBialgEquiv_naturality`: naturality of evaluation.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), Section 12.e.

This supports the separate Cartier-duality development identified alongside Layer 4, "Jordan
decomposition, diagonalizable groups, tori", of the ReductiveGroups roadmap.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConvolutionDual

universe u v w

section Map

variable (k : Type u) [Field k]
variable {H : Type v} {K : Type w}

section Coalgebra

variable [AddCommGroup H] [Module k H] [Coalgebra k H]
variable [AddCommGroup K] [Module k K] [Coalgebra k K]

/-- The linear dual of a coalgebra morphism, with convolution wrappers on its source and target. -/
private noncomputable def mapLinear (f : H →ₗc[k] K) :
    ConvolutionDual k K →ₗ[k] ConvolutionDual k H :=
  (WithConv.linearEquiv k _).symm.toLinearMap ∘ₗ
    f.toLinearMap.dualMap ∘ₗ (WithConv.linearEquiv k _).toLinearMap

private theorem mapLinear_apply (f : H →ₗc[k] K)
    (phi : ConvolutionDual k K) (x : H) :
    (mapLinear k f phi).ofConv x = phi.ofConv (f x) :=
  rfl

/-- Precomposition by a coalgebra morphism as an algebra morphism between convolution duals. -/
private noncomputable def mapAlgHom (f : H →ₗc[k] K) :
    ConvolutionDual k K →ₐ[k] ConvolutionDual k H where
  toFun := mapLinear k f
  map_zero' := map_zero (mapLinear k f)
  map_add' := map_add (mapLinear k f)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext x
    simp [mapLinear_apply]
  map_one' := by
    apply WithConv.ofConv_injective
    ext x
    simp [mapLinear_apply, LinearMap.convOne_apply]
  map_mul' phi psi := by
    apply WithConv.ofConv_injective
    exact LinearMap.convMul_comp_coalgHom_distrib phi psi f

@[simp]
private theorem mapAlgHom_apply (f : H →ₗc[k] K)
    (phi : ConvolutionDual k K) (x : H) :
    (mapAlgHom k f phi).ofConv x = phi.ofConv (f x) :=
  mapLinear_apply k f phi x

variable [FiniteDimensional k H] [FiniteDimensional k K]

private theorem dualDistribEquiv_tensor_map_apply (f : H →ₗc[k] K)
    (z : ConvolutionDual k K ⊗[k] ConvolutionDual k K) (x y : H) :
    dualDistribEquiv k H
        (Algebra.TensorProduct.map (mapAlgHom k f) (mapAlgHom k f) z) (x ⊗ₜ[k] y) =
      dualDistribEquiv k K z (f x ⊗ₜ[k] f y) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, LinearMap.add_apply] using
        congrArg₂ (fun a b ↦ a + b) hz₁ hz₂
  | tmul phi psi => simp [mapAlgHom_apply]

end Coalgebra

variable [Ring H] [Bialgebra k H]
variable [Ring K] [Bialgebra k K]
variable [FiniteDimensional k H] [FiniteDimensional k K]

/-- **The finite dual is contravariantly functorial.** A bialgebra morphism `H → K` induces
the bialgebra morphism `K* → H*` given by precomposition. -/
noncomputable def map (f : H →ₐc[k] K) :
    ConvolutionDual k K →ₐc[k] ConvolutionDual k H :=
  BialgHom.ofAlgHom (mapAlgHom k f.toCoalgHom)
    (by
      ext phi
      change Coalgebra.counit (R := k) (mapAlgHom k f.toCoalgHom phi) =
        Coalgebra.counit (R := k) phi
      rw [counit_apply, mapAlgHom_apply, counit_apply]
      exact congrArg phi.ofConv f.map_one)
    (by
      ext phi
      apply (dualDistribEquiv k H).injective
      apply TensorProduct.ext'
      intro x y
      simp only [AlgHom.comp_apply]
      simp only [Bialgebra.comulAlgHom, AlgHom.ofLinearMap_apply]
      rw [dualDistribEquiv_tensor_map_apply k f.toCoalgHom (Coalgebra.comul phi) x y,
        dualDistribEquiv_comul_apply, dualDistribEquiv_comul_apply,
        mapAlgHom_apply]
      exact congrArg phi.ofConv (f.map_mul x y).symm)

/-- The dual morphism evaluates by precomposition. -/
@[simp, grind =]
theorem map_apply (f : H →ₐc[k] K) (phi : ConvolutionDual k K) (x : H) :
    (map k f phi).ofConv x = phi.ofConv (f x) :=
  mapAlgHom_apply k f.toCoalgHom phi x

/-- Dualizing the identity bialgebra morphism gives the identity. -/
@[simp]
theorem map_id :
    map k (BialgHom.id k H) = BialgHom.id k (ConvolutionDual k H) := by
  ext phi x
  simp

/-- Dualizing a composite reverses the order of the dual morphisms. -/
@[simp]
theorem map_comp {L : Type*} [Ring L] [Bialgebra k L]
    [FiniteDimensional k L] (g : K →ₐc[k] L) (f : H →ₐc[k] K) :
    map k (g.comp f) = (map k f).comp (map k g) := by
  ext phi x
  simp

/-- A bialgebra equivalence induces a bialgebra equivalence of finite duals in the opposite
direction. -/
noncomputable def mapEquiv (e : H ≃ₐc[k] K) :
    ConvolutionDual k K ≃ₐc[k] ConvolutionDual k H :=
  BialgEquiv.ofBialgHom (map k e) (map k e.symm)
    (by rw [← map_comp, BialgEquiv.symm_comp, map_id])
    (by rw [← map_comp, BialgEquiv.comp_symm, map_id])

/-- The forward map of the dual equivalence is the dual morphism. -/
@[simp]
theorem mapEquiv_apply (e : H ≃ₐc[k] K) (phi : ConvolutionDual k K) :
    mapEquiv k e phi = map k e phi :=
  (rfl)

/-- The inverse of the dual equivalence is induced by the inverse bialgebra equivalence. -/
@[simp]
theorem mapEquiv_symm (e : H ≃ₐc[k] K) :
    (mapEquiv k e).symm = mapEquiv k e.symm := by
  unfold mapEquiv
  rw [BialgEquiv.ofBialgHom_symm]
  apply BialgEquiv.ext
  intro phi
  rfl

end Map

section Evaluation

variable (k : Type u) [Field k]
variable (H : Type v) [Ring H] [Bialgebra k H] [FiniteDimensional k H]

/-- Evaluation into the double convolution dual as a linear equivalence. -/
private noncomputable def evalLinearEquiv :
    H ≃ₗ[k] ConvolutionDual k (ConvolutionDual k H) :=
  (Module.evalEquiv k H).trans
    ((WithConv.linearEquiv k (Module.Dual k H)).dualMap.trans
      (WithConv.linearEquiv k (Module.Dual k (ConvolutionDual k H))).symm)

private theorem evalLinearEquiv_apply (x : H) (phi : ConvolutionDual k H) :
    (evalLinearEquiv k H x).ofConv phi = phi.ofConv x :=
  rfl

private theorem dualDistribEquiv_tensor_eval_apply
    (z : H ⊗[k] H) (w : ConvolutionDual k H ⊗[k] ConvolutionDual k H) :
    dualDistribEquiv k (ConvolutionDual k H)
        (TensorProduct.map (evalLinearEquiv k H).toLinearMap
          (evalLinearEquiv k H).toLinearMap z) w =
      dualDistribEquiv k H w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add, LinearMap.add_apply, WithConv.ofConv_add] using
        congrArg₂ (fun a b ↦ a + b) hz₁ hz₂
  | tmul x y =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ =>
          simpa only [map_add, LinearMap.add_apply] using
            congrArg₂ (fun a b ↦ a + b) hw₁ hw₂
      | tmul phi psi => simp [evalLinearEquiv_apply]

/-- Evaluation into the double finite dual as an algebra morphism. -/
private noncomputable def evalAlgHom :
    H →ₐ[k] ConvolutionDual k (ConvolutionDual k H) where
  toFun := evalLinearEquiv k H
  map_zero' := map_zero (evalLinearEquiv k H)
  map_add' := map_add (evalLinearEquiv k H)
  commutes' r := by
    apply WithConv.ofConv_injective
    ext phi
    rw [evalLinearEquiv_apply, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
    simp [Algebra.algebraMap_eq_smul_one, counit_apply]
  map_one' := by
    apply WithConv.ofConv_injective
    ext phi
    simp [evalLinearEquiv_apply, counit_apply]
  map_mul' x y := by
    apply WithConv.ofConv_injective
    ext phi
    rw [evalLinearEquiv_apply]
    symm
    calc
      ((evalLinearEquiv k H x) * (evalLinearEquiv k H y)).ofConv phi =
          dualDistribEquiv k (ConvolutionDual k H)
            (evalLinearEquiv k H x ⊗ₜ[k] evalLinearEquiv k H y)
              (Coalgebra.comul phi) :=
        convMul_apply k (ConvolutionDual k H) _ _ phi
      _ = dualDistribEquiv k H (Coalgebra.comul phi) (x ⊗ₜ[k] y) := by
        simpa using dualDistribEquiv_tensor_eval_apply k H (x ⊗ₜ[k] y)
          (Coalgebra.comul phi)
      _ = phi.ofConv (x * y) := dualDistribEquiv_comul_apply k H phi x y

@[simp]
private theorem evalAlgHom_apply (x : H) (phi : ConvolutionDual k H) :
    (evalAlgHom k H x).ofConv phi = phi.ofConv x :=
  evalLinearEquiv_apply k H x phi

private theorem evalAlgHom_counit_comp :
    (Bialgebra.counitAlgHom k (ConvolutionDual k (ConvolutionDual k H))).comp
        (evalAlgHom k H) = Bialgebra.counitAlgHom k H := by
  ext x
  simp [counit_apply, evalAlgHom_apply, LinearMap.convOne_apply]

private theorem evalAlgHom_map_comp_comul :
    (Algebra.TensorProduct.map (evalAlgHom k H) (evalAlgHom k H)).comp
        (Bialgebra.comulAlgHom k H) =
      (Bialgebra.comulAlgHom k (ConvolutionDual k (ConvolutionDual k H))).comp
        (evalAlgHom k H) := by
  ext x
  apply (dualDistribEquiv k (ConvolutionDual k H)).injective
  apply LinearMap.ext
  intro w
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom, AlgHom.ofLinearMap_apply]
  calc
    _ = dualDistribEquiv k H w (Coalgebra.comul x) := by
      exact dualDistribEquiv_tensor_eval_apply k H (Coalgebra.comul x) w
    _ = (LinearMap.mul' k (ConvolutionDual k H) w).ofConv x :=
      (ofConv_mul_apply k H w x).symm
    _ = _ := by
      rw [dualDistribEquiv_comul]
      simp only [LinearMap.comp_apply, evalAlgHom_apply]

/-- Evaluation into the double finite dual as a bialgebra morphism. -/
private noncomputable def evalBialgHom :
    H →ₐc[k] ConvolutionDual k (ConvolutionDual k H) :=
  BialgHom.ofAlgHom (R := k) (A := H)
    (B := ConvolutionDual k (ConvolutionDual k H))
    (evalAlgHom k H) (evalAlgHom_counit_comp k H)
    (evalAlgHom_map_comp_comul k H)

private theorem evalBialgHom_apply (x : H) :
    evalBialgHom k H x = evalLinearEquiv k H x :=
  rfl

/-- **A finite-dimensional bialgebra is canonically isomorphic to its double finite dual.**

The equivalence sends `x` to evaluation at `x`. -/
noncomputable def evalBialgEquiv :
    H ≃ₐc[k] ConvolutionDual k (ConvolutionDual k H) := by
  let bH : Bialgebra k H := inferInstance
  let bHH : Bialgebra k (ConvolutionDual k (ConvolutionDual k H)) := inferInstance
  change @BialgEquiv k _ H (ConvolutionDual k (ConvolutionDual k H)) _ _
    bH.toAlgebra bHH.toAlgebra bH.toCoalgebra.toCoalgebraStruct
      bHH.toCoalgebra.toCoalgebraStruct
  have hbij : Function.Bijective (evalBialgHom k H) := by
    change Function.Bijective (evalLinearEquiv k H)
    exact (evalLinearEquiv k H).bijective
  exact @BialgEquiv.ofBijective k H (ConvolutionDual k (ConvolutionDual k H)) _ _ _
    bH bHH (evalBialgHom k H) hbij

private theorem evalBialgEquiv_eq_evalBialgHom (x : H) :
    evalBialgEquiv k H x = evalBialgHom k H x := by
  simp only [evalBialgEquiv, id_eq, BialgEquiv.ofBijective_apply]

/-- The double-dual equivalence evaluates a functional at the original element. -/
@[simp, grind =]
theorem evalBialgEquiv_apply (x : H) (phi : ConvolutionDual k H) :
    (evalBialgEquiv k H x).ofConv phi = phi.ofConv x :=
  by
    rw [evalBialgEquiv_eq_evalBialgHom]
    rw [evalBialgHom_apply]
    exact evalLinearEquiv_apply k H x phi

/-- The inverse double-dual equivalence is characterized by evaluation. -/
@[simp, grind =]
theorem apply_evalBialgEquiv_symm_apply
    (Phi : ConvolutionDual k (ConvolutionDual k H)) (phi : ConvolutionDual k H) :
    phi.ofConv ((evalBialgEquiv k H).symm Phi) = Phi.ofConv phi := by
  rw [← evalBialgEquiv_apply]
  simp

/-- Evaluation into the double dual is natural in finite-dimensional bialgebras. -/
theorem evalBialgEquiv_naturality {K : Type w} [Ring K] [Bialgebra k K]
    [FiniteDimensional k K] (f : H →ₐc[k] K) :
    (evalBialgEquiv k K : K →ₐc[k] ConvolutionDual k (ConvolutionDual k K)).comp f =
      (map k (map k f)).comp (evalBialgEquiv k H) := by
  ext x phi
  simp

end Evaluation

end TauCeti.ConvolutionDual
